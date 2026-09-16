#include "balance_bot.h"

#include "i2c.h"
#include "main.h"
#include "tim.h"
#include "usart.h"

#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * Mechanical/sensor convention used by this firmware:
 *
 * - The MPU6050 breakout is fixed flat against the vertical foam-board.
 * - MPU X points upward while the robot is standing.
 * - MPU Y is parallel to the wheel axle.
 * - A forward lean must produce a positive ANG value in the serial output.
 *
 * If a forward lean produces a negative ANG value, send "SSIGN -1".
 */

#define MPU6050_WHO_AM_I            0x75U
#define MPU6050_PWR_MGMT_1          0x6BU
#define MPU6050_SMPLRT_DIV          0x19U
#define MPU6050_CONFIG              0x1AU
#define MPU6050_GYRO_CONFIG         0x1BU
#define MPU6050_ACCEL_CONFIG        0x1CU
#define MPU6050_ACCEL_XOUT_H        0x3BU

#define CONTROL_PERIOD_MS           4U
#define CONTROL_DT_S                0.004f
#define COMPLEMENTARY_ALPHA         0.980f
#define RAD_TO_DEG                  57.2957795f
#define GYRO_LSB_PER_DPS            65.5f

#define PWM_TIMER_MAX               799
#define CALIBRATION_SAMPLES         500U
#define ARM_ANGLE_LIMIT_DEG         8.0f
#define FALL_ANGLE_LIMIT_DEG        35.0f
/* Caps the accumulated error in deg*s, so KI's contribution tops out at
 * KI * 10 PWM counts. Useful KI values here are therefore in the 5-30 range,
 * not the fractions that a differently-scaled loop would want. */
#define INTEGRAL_LIMIT              10.0f
#define MPU_MAX_CONSECUTIVE_ERRORS  3U

/*
 * Motor noise can knock the I2C bus over mid-transfer. Rather than latching a
 * fault on the first hiccup, recover the bus in place and keep balancing. Give
 * up only if recoveries keep coming without a healthy stretch in between
 * (MPU_CLEAN_READS_TO_FORGIVE ticks at CONTROL_PERIOD_MS = about 2 s).
 */
#define MPU_MAX_RECOVERIES          5U
#define MPU_CLEAN_READS_TO_FORGIVE  500U

#define UART_RX_CAPACITY            80U
#define UART_TX_CAPACITY            192U
#define TELEMETRY_PERIOD_MS         200U
#define MOTOR_TEST_DURATION_MS      400U
#define MOTOR_TEST_LIMIT            250

/*
 * Auto-arm: once READY, the robot arms itself after being held inside the arm
 * window and steady for AUTO_ARM_STABLE_MS. The steadiness test is what keeps
 * it from arming while it is still being carried around.
 *
 * An explicit STOP (serial command or B1) inhibits auto-arm until the next
 * explicit ARM or reset, so the stop button always means stop. Recovery from
 * FALLEN is not inhibited: stand the robot back up and it resumes on its own.
 *
 * Set AUTO_ARM_ENABLED to 0 to go back to manual arming only.
 */
#define AUTO_ARM_ENABLED            1
#define AUTO_ARM_STABLE_MS          1000U
#define AUTO_ARM_MAX_RATE_DPS       30.0f

typedef enum
{
    BOT_BOOT = 0,
    BOT_READY,
    BOT_ARMED,
    BOT_FALLEN,
    BOT_MPU_FAULT
} BotState;

typedef struct
{
    int16_t ax;
    int16_t ay;
    int16_t az;
    int16_t gx;
    int16_t gy;
    int16_t gz;
} MpuRaw;

static BotState bot_state = BOT_BOOT;
static uint16_t mpu_i2c_address = (0x68U << 1);
static uint8_t mpu_address_7bit;
static uint8_t mpu_who_am_i;
static bool mpu_probe_responded;
static bool mpu_probe_who_read;
static uint8_t mpu_probe_address;
static uint8_t mpu_probe_who;

static float angle_deg;
static float accelerometer_upright_reference_deg;
static float gyro_rate_dps;
static float gyro_y_bias_dps;
/*
 * The attitude the robot actually balances at, not zero: the boot pose that
 * sets the angle reference is close to but not exactly over the axle. Found by
 * watching OUT while balancing - at -0.5 its average sat near zero, so the
 * wheels stopped being driven one way the whole time. Re-find it (TARGET n)
 * after moving any mass around.
 */
static float target_angle_deg = -0.5f;
static float integral_error;
/*
 * KP 28 / KD 1.10 was too soft for this chassis: the robot leaned away faster
 * than the wheels came back under it. Raised together so the damping ratio
 * (KD/KP) stays where it was - KD alone lags behind a KP bump and the robot
 * starts oscillating instead of catching itself.
 *
 * Tune live with KP/KD/KI, then copy the settled numbers back here:
 *   falls over limply           -> KP up
 *   shivers in place, growing   -> KD up (or KP down)
 *   drifts one way and falls    -> TARGET, not the gains
 * KI stays 0 until the robot balances on its own.
 */
static float kp = 45.0f;
static float ki = 0.0f;
static float kd = 2.50f;

static int16_t motor_output;

/*
 * Measured on this chassis (FIT0450 gearmotors, 6V alkaline pack):
 * both wheels start turning at about 130 of 799, so 130 is the floor and the
 * extra margin keeps the weaker side moving as the pack sags. Re-measure with
 * DEAD 0 + TEST BOTH <n> after changing motors, wheels or battery.
 */
static int16_t motor_deadband = 130;

/*
 * Full range. These gearmotors are slow enough that the robot needs all of it.
 *
 * This was briefly capped at 400 to test whether the I2C dropouts tracked
 * motor current. They did: the motor return was sharing a breadboard rail with
 * the MPU's ground, so motor current developed a few hundred mV across the
 * shared contacts and moved the sensor's reference out from under the I2C
 * levels. Star-grounding it (battery and TB6612 in their own loop, MPU on its
 * own wire to a separate Nucleo GND pin) fixed it, so the cap is gone.
 */
static int16_t maximum_pwm = PWM_TIMER_MAX;

/*
 * Mounting-dependent signs, confirmed on this build:
 *   sensor_sign      leaning the MPU side (front) down must give ANG > 0
 *   left/right sign  TEST BOTH must roll both wheels toward the front
 * Flip at runtime with SSIGN / LSIGN / RSIGN if the hardware changes.
 */
static int8_t sensor_sign = -1;
static int8_t left_motor_sign = -1;
static int8_t right_motor_sign = 1;

static uint32_t next_control_ms;
static uint32_t last_telemetry_ms;
static uint32_t last_button_event_ms;
static bool previous_button_state;
static uint8_t consecutive_mpu_errors;
static uint32_t mpu_recoveries;
static uint32_t mpu_clean_reads;
static uint32_t auto_arm_stable_ms;
static bool auto_arm_inhibited;

static bool motor_test_active;
static uint32_t motor_test_stop_ms;

static uint8_t uart_rx_byte;
static volatile bool uart_line_ready;
static volatile uint16_t uart_rx_index;
static char uart_rx_line[UART_RX_CAPACITY];
static char uart_tx_buffer[UART_TX_CAPACITY];

static bool MpuWrite(uint8_t reg, uint8_t value);
static bool MpuRead(uint8_t reg, uint8_t *data, uint16_t length);
static bool MpuReadRaw(MpuRaw *raw);
static bool MpuConfigure(void);
static void RecoveryHalfBit(void);
static bool MpuRecoverBus(void);
static bool MpuInitialize(void);
static bool MpuCalibrate(void);
static void UpdateControl(void);
static void StopMotors(void);
static void ApplyMotorOutputs(int16_t left, int16_t right);
static void ApplyOneMotor(bool motor_a, int16_t command, int8_t direction_sign);
static void SetState(BotState new_state);
static void TryArm(void);
static void Disarm(BotState new_state);
static void ProcessButton(uint32_t now_ms);
static void ProcessSerialCommand(void);
static void StartMotorTest(int16_t left, int16_t right);
static void StopMotorTest(void);
static void SendStatus(void);
static void SendHelp(void);
static void UartTrySend(const char *text);
static void UartSendBlocking(const char *text);
static bool ParseFloat(const char *text, float minimum, float maximum, float *value);
static bool ParseLong(const char *text, long minimum, long maximum, long *value);
static int16_t ReadBigEndianInt16(const uint8_t *bytes);
static int16_t ClampInt16(int32_t value, int16_t minimum, int16_t maximum);
static float ClampFloat(float value, float minimum, float maximum);
static float NormalizeAngle(float angle);
static const char *StateName(BotState state);
static void UpdateLeds(void);

void BalanceBot_Init(void)
{
    StopMotors();

    if (HAL_TIM_PWM_Start(&htim4, TIM_CHANNEL_3) != HAL_OK)
    {
        Error_Handler();
    }
    if (HAL_TIM_PWM_Start(&htim4, TIM_CHANNEL_4) != HAL_OK)
    {
        Error_Handler();
    }

    __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_3, 0U);
    __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_4, 0U);

    if (HAL_UART_Receive_IT(&huart3, &uart_rx_byte, 1U) != HAL_OK)
    {
        Error_Handler();
    }

    UartSendBlocking(
        "\r\nBalanceBot_F446ZE\r\n"
        "Keep the robot still while MPU6050 calibrates...\r\n");

    SetState(BOT_BOOT);
    if (!MpuInitialize())
    {
        GPIO_InitTypeDef gpio_diagnostic = {0};
        char line_state_message[112];
        unsigned int scl_without_pull;
        unsigned int sda_without_pull;

        SetState(BOT_MPU_FAULT);
        UartSendBlocking(
            "FAULT: no compatible MPU response at I2C 0x68 or 0x69\r\n");
        if (mpu_probe_responded)
        {
            char probe_message[96];

            (void)snprintf(
                probe_message,
                sizeof(probe_message),
                "PROBE: ACK at 0x%02X, WHO_AM_I %s0x%02X\r\n",
                (unsigned int)mpu_probe_address,
                mpu_probe_who_read ? "=" : "read-failed, last=",
                (unsigned int)mpu_probe_who);
            UartSendBlocking(probe_message);
        }
        else
        {
            UartSendBlocking("PROBE: no ACK at either address\r\n");
        }

        /*
         * Release the I2C peripheral, then check whether either physical
         * bus line is externally held low.
         */
        (void)HAL_I2C_DeInit(&hi2c1);
        __HAL_RCC_GPIOB_CLK_ENABLE();
        gpio_diagnostic.Pin = GPIO_PIN_8 | GPIO_PIN_9;
        gpio_diagnostic.Mode = GPIO_MODE_INPUT;
        gpio_diagnostic.Pull = GPIO_NOPULL;
        gpio_diagnostic.Speed = GPIO_SPEED_FREQ_LOW;
        HAL_GPIO_Init(GPIOB, &gpio_diagnostic);
        HAL_Delay(5U);
        scl_without_pull =
            (HAL_GPIO_ReadPin(GPIOB, GPIO_PIN_8) == GPIO_PIN_SET) ? 1U : 0U;
        sda_without_pull =
            (HAL_GPIO_ReadPin(GPIOB, GPIO_PIN_9) == GPIO_PIN_SET) ? 1U : 0U;

        gpio_diagnostic.Pull = GPIO_PULLUP;
        HAL_GPIO_Init(GPIOB, &gpio_diagnostic);
        HAL_Delay(5U);

        (void)snprintf(
            line_state_message,
            sizeof(line_state_message),
            "BUS RELEASED: external SCL=%u SDA=%u; internal-pull SCL=%u SDA=%u\r\n",
            scl_without_pull,
            sda_without_pull,
            (HAL_GPIO_ReadPin(GPIOB, GPIO_PIN_8) == GPIO_PIN_SET) ? 1U : 0U,
            (HAL_GPIO_ReadPin(GPIOB, GPIO_PIN_9) == GPIO_PIN_SET) ? 1U : 0U);
        UartSendBlocking(line_state_message);
    }
    else
    {
        char detection_message[80];

        (void)snprintf(
            detection_message,
            sizeof(detection_message),
            "MPU detected: address=0x%02X WHO_AM_I=0x%02X\r\n",
            (unsigned int)mpu_address_7bit,
            (unsigned int)mpu_who_am_i);
        UartSendBlocking(detection_message);

        if (!MpuCalibrate())
        {
            SetState(BOT_MPU_FAULT);
            UartSendBlocking("FAULT: MPU6050 calibration/read failed\r\n");
        }
        else
        {
            SetState(BOT_READY);
#if AUTO_ARM_ENABLED
            UartSendBlocking(
                "READY: hold upright and steady 1s - it will arm itself\r\n"
                "STOP or B1 to disarm. Type HELP for commands\r\n");
#else
            UartSendBlocking(
                "READY: hold upright, verify ANG sign, then press B1 or send ARM\r\n"
                "Type HELP for commands\r\n");
#endif
        }
    }

    next_control_ms = HAL_GetTick() + CONTROL_PERIOD_MS;
    last_telemetry_ms = HAL_GetTick();
    previous_button_state =
        (HAL_GPIO_ReadPin(USER_Btn_GPIO_Port, USER_Btn_Pin) == GPIO_PIN_SET);
}

void BalanceBot_Process(void)
{
    uint32_t now_ms = HAL_GetTick();

    ProcessSerialCommand();
    ProcessButton(now_ms);

    if (motor_test_active
        && ((int32_t)(now_ms - motor_test_stop_ms) >= 0))
    {
        StopMotorTest();
    }

    if ((int32_t)(now_ms - next_control_ms) >= 0)
    {
        next_control_ms += CONTROL_PERIOD_MS;

        /* Do not run a burst of stale control iterations after a long pause. */
        if ((int32_t)(now_ms - next_control_ms)
            > (int32_t)(2U * CONTROL_PERIOD_MS))
        {
            next_control_ms = now_ms + CONTROL_PERIOD_MS;
        }

        UpdateControl();
    }

    if ((now_ms - last_telemetry_ms) >= TELEMETRY_PERIOD_MS)
    {
        last_telemetry_ms = now_ms;
        SendStatus();
    }

    UpdateLeds();
}

void HAL_UART_RxCpltCallback(UART_HandleTypeDef *huart)
{
    if (huart->Instance != USART3)
    {
        return;
    }

    if (!uart_line_ready)
    {
        if ((uart_rx_byte == '\r') || (uart_rx_byte == '\n'))
        {
            if (uart_rx_index > 0U)
            {
                uart_rx_line[uart_rx_index] = '\0';
                uart_line_ready = true;
                uart_rx_index = 0U;
            }
        }
        else if (uart_rx_index < (UART_RX_CAPACITY - 1U))
        {
            uart_rx_line[uart_rx_index] = (char)uart_rx_byte;
            uart_rx_index++;
        }
        else
        {
            uart_rx_index = 0U;
        }
    }

    (void)HAL_UART_Receive_IT(&huart3, &uart_rx_byte, 1U);
}

void HAL_UART_ErrorCallback(UART_HandleTypeDef *huart)
{
    if (huart->Instance != USART3)
    {
        return;
    }

    uart_rx_index = 0U;
    uart_line_ready = false;
    (void)HAL_UART_AbortReceive(huart);
    (void)HAL_UART_Receive_IT(&huart3, &uart_rx_byte, 1U);
}

static bool MpuWrite(uint8_t reg, uint8_t value)
{
    return HAL_I2C_Mem_Write(
               &hi2c1,
               mpu_i2c_address,
               reg,
               I2C_MEMADD_SIZE_8BIT,
               &value,
               1U,
               20U) == HAL_OK;
}

static bool MpuRead(uint8_t reg, uint8_t *data, uint16_t length)
{
    return HAL_I2C_Mem_Read(
               &hi2c1,
               mpu_i2c_address,
               reg,
               I2C_MEMADD_SIZE_8BIT,
               data,
               length,
               20U) == HAL_OK;
}

static bool MpuReadRaw(MpuRaw *raw)
{
    uint8_t data[14];

    if (!MpuRead(MPU6050_ACCEL_XOUT_H, data, sizeof(data)))
    {
        return false;
    }

    raw->ax = ReadBigEndianInt16(&data[0]);
    raw->ay = ReadBigEndianInt16(&data[2]);
    raw->az = ReadBigEndianInt16(&data[4]);
    raw->gx = ReadBigEndianInt16(&data[8]);
    raw->gy = ReadBigEndianInt16(&data[10]);
    raw->gz = ReadBigEndianInt16(&data[12]);
    return true;
}

/*
 * Register setup only: no device reset, no long delays, so this is safe to
 * call from the control loop while recovering. PLL clock from X gyro,
 * 250 Hz output, DLPF around 44 Hz, gyro +/-500 dps, accelerometer +/-2 g.
 */
static bool MpuConfigure(void)
{
    return MpuWrite(MPU6050_PWR_MGMT_1, 0x01U)
        && MpuWrite(MPU6050_SMPLRT_DIV, 0x03U)
        && MpuWrite(MPU6050_CONFIG, 0x03U)
        && MpuWrite(MPU6050_GYRO_CONFIG, 0x08U)
        && MpuWrite(MPU6050_ACCEL_CONFIG, 0x00U);
}

/* Roughly 25 us at 16 MHz - one half-period of the recovery clock. */
static void RecoveryHalfBit(void)
{
    volatile uint32_t spin = 40U;

    while (spin > 0U)
    {
        spin--;
    }
}

/*
 * Motor brush noise can corrupt a transfer mid-byte and leave the MPU holding
 * SDA low, waiting for clocks that never come. A peripheral reset alone does
 * not fix that - the slave has to be clocked out of it. Free the line by hand,
 * re-init I2C1, then re-apply the sensor configuration.
 *
 * Deliberately does not recalibrate the gyro or recapture the upright
 * reference: the robot is moving, so both would come out wrong.
 */
static bool MpuRecoverBus(void)
{
    GPIO_InitTypeDef gpio = {0};
    uint32_t pulse;

    (void)HAL_I2C_DeInit(&hi2c1);
    __HAL_RCC_GPIOB_CLK_ENABLE();

    gpio.Pin = GPIO_PIN_9;            /* SDA: watch only */
    gpio.Mode = GPIO_MODE_INPUT;
    gpio.Pull = GPIO_PULLUP;
    gpio.Speed = GPIO_SPEED_FREQ_LOW;
    HAL_GPIO_Init(GPIOB, &gpio);

    gpio.Pin = GPIO_PIN_8;            /* SCL: drive open-drain */
    gpio.Mode = GPIO_MODE_OUTPUT_OD;
    HAL_GPIO_Init(GPIOB, &gpio);
    HAL_GPIO_WritePin(GPIOB, GPIO_PIN_8, GPIO_PIN_SET);

    /* Nine clocks is enough to walk any stuck slave past its last byte. */
    for (pulse = 0U; pulse < 9U; pulse++)
    {
        if (HAL_GPIO_ReadPin(GPIOB, GPIO_PIN_9) == GPIO_PIN_SET)
        {
            break;
        }
        HAL_GPIO_WritePin(GPIOB, GPIO_PIN_8, GPIO_PIN_RESET);
        RecoveryHalfBit();
        HAL_GPIO_WritePin(GPIOB, GPIO_PIN_8, GPIO_PIN_SET);
        RecoveryHalfBit();
    }

    MX_I2C1_Init();
    return MpuConfigure();
}

static bool MpuInitialize(void)
{
    static const uint8_t candidate_addresses[] = {0x68U, 0x69U};
    bool found = false;

    mpu_probe_responded = false;
    mpu_probe_who_read = false;
    mpu_probe_address = 0U;
    mpu_probe_who = 0U;
    HAL_Delay(100U);
    for (uint32_t i = 0U;
         i < (sizeof(candidate_addresses) / sizeof(candidate_addresses[0]));
         i++)
    {
        mpu_address_7bit = candidate_addresses[i];
        mpu_i2c_address = (uint16_t)mpu_address_7bit << 1;

        if (HAL_I2C_IsDeviceReady(
                &hi2c1,
                mpu_i2c_address,
                3U,
                30U) == HAL_OK)
        {
            mpu_probe_responded = true;
            mpu_probe_address = mpu_address_7bit;

            if (!MpuRead(MPU6050_WHO_AM_I, &mpu_who_am_i, 1U))
            {
                continue;
            }

            mpu_probe_who_read = true;
            mpu_probe_who = mpu_who_am_i;

            /*
             * 0x68 is MPU6050. 0x70/0x71 are register-compatible
             * MPU6500/MPU9250 variants. Some clone modules report 0x72
             * while retaining the same registers used by this firmware.
             */
            if ((mpu_who_am_i == 0x68U)
                || (mpu_who_am_i == 0x70U)
                || (mpu_who_am_i == 0x71U)
                || (mpu_who_am_i == 0x72U))
            {
                found = true;
                break;
            }
        }
    }

    if (!found)
    {
        return false;
    }

    if (!MpuWrite(MPU6050_PWR_MGMT_1, 0x80U))
    {
        return false;
    }
    HAL_Delay(100U);

    if (!MpuConfigure())
    {
        return false;
    }

    HAL_Delay(50U);
    return true;
}

static bool MpuCalibrate(void)
{
    int64_t gyro_sum = 0;
    int64_t ax_sum = 0;
    int64_t az_sum = 0;
    MpuRaw raw;

    for (uint32_t sample = 0U; sample < CALIBRATION_SAMPLES; sample++)
    {
        if (!MpuReadRaw(&raw))
        {
            return false;
        }

        gyro_sum += raw.gy;
        ax_sum += raw.ax;
        az_sum += raw.az;
        HAL_Delay(CONTROL_PERIOD_MS);
    }

    gyro_y_bias_dps =
        ((float)gyro_sum / (float)CALIBRATION_SAMPLES) / GYRO_LSB_PER_DPS;

    /*
     * Treat the motionless startup pose as the upright zero. This removes
     * a fixed mounting-angle offset while preserving the tilt direction.
     */
    accelerometer_upright_reference_deg =
        atan2f(
            (float)az_sum / (float)CALIBRATION_SAMPLES,
            (float)ax_sum / (float)CALIBRATION_SAMPLES)
        * RAD_TO_DEG;
    angle_deg = 0.0f;
    gyro_rate_dps = 0.0f;
    return true;
}

static void UpdateControl(void)
{
    MpuRaw raw;
    float accelerometer_angle;

    if (bot_state == BOT_MPU_FAULT)
    {
        return;
    }

    if (!MpuReadRaw(&raw))
    {
        consecutive_mpu_errors++;
        if (consecutive_mpu_errors < MPU_MAX_CONSECUTIVE_ERRORS)
        {
            return;                       /* single glitch - just skip a tick */
        }

        consecutive_mpu_errors = 0U;
        mpu_clean_reads = 0U;
        mpu_recoveries++;

        if (mpu_recoveries > MPU_MAX_RECOVERIES)
        {
            Disarm(BOT_MPU_FAULT);
            UartTrySend("FAULT: MPU6050 keeps dropping out; check wiring\r\n");
            return;
        }

        if (MpuRecoverBus())
        {
            UartTrySend("I2C: bus recovered\r\n");
        }
        else
        {
            Disarm(BOT_MPU_FAULT);
            UartTrySend("FAULT: I2C recovery failed; power-cycle the MPU\r\n");
        }
        return;
    }

    consecutive_mpu_errors = 0U;

    /* A long clean stretch means the bus is healthy again, so stop counting
     * earlier recoveries against the give-up limit. */
    if (mpu_recoveries > 0U)
    {
        mpu_clean_reads++;
        if (mpu_clean_reads >= MPU_CLEAN_READS_TO_FORGIVE)
        {
            mpu_clean_reads = 0U;
            mpu_recoveries = 0U;
        }
    }

    accelerometer_angle =
        (float)sensor_sign
        * NormalizeAngle(
            (atan2f((float)raw.az, (float)raw.ax) * RAD_TO_DEG)
            - accelerometer_upright_reference_deg);
    gyro_rate_dps =
        (float)sensor_sign
        * (((float)raw.gy / GYRO_LSB_PER_DPS) - gyro_y_bias_dps);

    angle_deg =
        COMPLEMENTARY_ALPHA
        * (angle_deg + (gyro_rate_dps * CONTROL_DT_S))
        + ((1.0f - COMPLEMENTARY_ALPHA) * accelerometer_angle);

    if (bot_state != BOT_ARMED)
    {
        if ((bot_state == BOT_FALLEN)
            && (fabsf(angle_deg) <= ARM_ANGLE_LIMIT_DEG))
        {
            SetState(BOT_READY);
            UartTrySend("READY: upright again\r\n");
        }

#if AUTO_ARM_ENABLED
        /* Arm by itself once held upright and steady, unless STOP inhibited it. */
        if ((bot_state == BOT_READY) && !auto_arm_inhibited)
        {
            if ((fabsf(angle_deg - target_angle_deg) <= ARM_ANGLE_LIMIT_DEG)
                && (fabsf(gyro_rate_dps) <= AUTO_ARM_MAX_RATE_DPS))
            {
                auto_arm_stable_ms += CONTROL_PERIOD_MS;
                if (auto_arm_stable_ms >= AUTO_ARM_STABLE_MS)
                {
                    auto_arm_stable_ms = 0U;
                    UartTrySend("AUTO-ARM: upright and steady\r\n");
                    TryArm();
                }
            }
            else
            {
                auto_arm_stable_ms = 0U;
            }
        }
        else
        {
            auto_arm_stable_ms = 0U;
        }
#endif
        return;
    }

    if (fabsf(angle_deg) > FALL_ANGLE_LIMIT_DEG)
    {
        Disarm(BOT_FALLEN);
        UartTrySend("FALLEN: motors disabled\r\n");
        return;
    }

    {
        float error = angle_deg - target_angle_deg;
        float control;

        integral_error += error * CONTROL_DT_S;
        integral_error =
            ClampFloat(integral_error, -INTEGRAL_LIMIT, INTEGRAL_LIMIT);

        control = (kp * error)
                + (ki * integral_error)
                + (kd * gyro_rate_dps);

        motor_output = ClampInt16(
            (int32_t)control,
            (int16_t)-maximum_pwm,
            maximum_pwm);
        ApplyMotorOutputs(motor_output, motor_output);
    }
}

static void StopMotors(void)
{
    __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_3, 0U);
    __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_4, 0U);

    HAL_GPIO_WritePin(
        MOTOR_AIN1_GPIO_Port,
        MOTOR_AIN1_Pin | MOTOR_AIN2_Pin | MOTOR_BIN1_Pin | MOTOR_BIN2_Pin,
        GPIO_PIN_RESET);
    HAL_GPIO_WritePin(TB_STBY_GPIO_Port, TB_STBY_Pin, GPIO_PIN_RESET);
    motor_output = 0;
}

static void ApplyMotorOutputs(int16_t left, int16_t right)
{
    HAL_GPIO_WritePin(TB_STBY_GPIO_Port, TB_STBY_Pin, GPIO_PIN_SET);
    ApplyOneMotor(true, left, left_motor_sign);
    ApplyOneMotor(false, right, right_motor_sign);
}

static void ApplyOneMotor(
    bool motor_a,
    int16_t command,
    int8_t direction_sign)
{
    int32_t signed_command = (int32_t)command * direction_sign;
    uint32_t duty;
    GPIO_PinState input_1;
    GPIO_PinState input_2;

    signed_command =
        ClampInt16(signed_command, -PWM_TIMER_MAX, PWM_TIMER_MAX);
    duty = (uint32_t)((signed_command < 0) ? -signed_command : signed_command);

    /*
     * Deadband compensation, remapped instead of clamped.
     *
     * Clamping everything below the deadband up to it (the old behaviour) made
     * every command from 1 to deadband-1 come out identical, so near the
     * balance point - where the commands are small and the control matters
     * most - the drive was effectively on/off and the robot limit-cycled.
     *
     * Rescaling 0..PWM_TIMER_MAX onto deadband..PWM_TIMER_MAX skips the
     * stiction band while keeping the response proportional to the command.
     */
    if (duty > 0U)
    {
        duty = (uint32_t)motor_deadband
             + ((duty * (uint32_t)(PWM_TIMER_MAX - motor_deadband))
                / (uint32_t)PWM_TIMER_MAX);
    }

    if (signed_command > 0)
    {
        input_1 = GPIO_PIN_SET;
        input_2 = GPIO_PIN_RESET;
    }
    else if (signed_command < 0)
    {
        input_1 = GPIO_PIN_RESET;
        input_2 = GPIO_PIN_SET;
    }
    else
    {
        input_1 = GPIO_PIN_RESET;
        input_2 = GPIO_PIN_RESET;
    }

    if (motor_a)
    {
        HAL_GPIO_WritePin(MOTOR_AIN1_GPIO_Port, MOTOR_AIN1_Pin, input_1);
        HAL_GPIO_WritePin(MOTOR_AIN2_GPIO_Port, MOTOR_AIN2_Pin, input_2);
        __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_3, duty);
    }
    else
    {
        HAL_GPIO_WritePin(MOTOR_BIN1_GPIO_Port, MOTOR_BIN1_Pin, input_1);
        HAL_GPIO_WritePin(MOTOR_BIN2_GPIO_Port, MOTOR_BIN2_Pin, input_2);
        __HAL_TIM_SET_COMPARE(&htim4, TIM_CHANNEL_4, duty);
    }
}

static void SetState(BotState new_state)
{
    bot_state = new_state;
    UpdateLeds();
}

static void TryArm(void)
{
    if (bot_state == BOT_MPU_FAULT)
    {
        UartTrySend("ERR: MPU fault; reset after checking wiring\r\n");
        return;
    }

    /* Measured against the balance point, not absolute zero, so that a
     * non-zero TARGET does not make the arm window lopsided (and does not
     * let auto-arm retry forever against a check it can never pass). */
    if (fabsf(angle_deg - target_angle_deg) > ARM_ANGLE_LIMIT_DEG)
    {
        UartTrySend("ERR: hold within +/-8 degrees of TARGET before ARM\r\n");
        return;
    }

    StopMotorTest();
    integral_error = 0.0f;
    motor_output = 0;
    auto_arm_stable_ms = 0U;
    auto_arm_inhibited = false;   /* arming clears an earlier STOP */
    HAL_GPIO_WritePin(TB_STBY_GPIO_Port, TB_STBY_Pin, GPIO_PIN_SET);
    SetState(BOT_ARMED);
    UartTrySend("ARMED\r\n");
}

static void Disarm(BotState new_state)
{
    StopMotorTest();
    StopMotors();
    integral_error = 0.0f;
    SetState(new_state);
}

static void ProcessButton(uint32_t now_ms)
{
    bool button_is_pressed =
        (HAL_GPIO_ReadPin(USER_Btn_GPIO_Port, USER_Btn_Pin) == GPIO_PIN_SET);

    if (button_is_pressed
        && !previous_button_state
        && ((now_ms - last_button_event_ms) >= 250U))
    {
        last_button_event_ms = now_ms;
        if (bot_state == BOT_ARMED)
        {
            auto_arm_inhibited = true;   /* stop must mean stop */
            auto_arm_stable_ms = 0U;
            Disarm(BOT_READY);
            UartTrySend("STOPPED (auto-arm off; press B1 again to re-arm)\r\n");
        }
        else
        {
            TryArm();
        }
    }

    previous_button_state = button_is_pressed;
}

static void ProcessSerialCommand(void)
{
    char command[UART_RX_CAPACITY];
    uint16_t length;

    if (!uart_line_ready)
    {
        return;
    }

    __disable_irq();
    (void)strncpy(command, uart_rx_line, sizeof(command) - 1U);
    command[sizeof(command) - 1U] = '\0';
    uart_line_ready = false;
    __enable_irq();

    length = (uint16_t)strlen(command);
    for (uint16_t index = 0U; index < length; index++)
    {
        command[index] = (char)toupper((unsigned char)command[index]);
    }

    while ((length > 0U)
        && isspace((unsigned char)command[length - 1U]))
    {
        command[length - 1U] = '\0';
        length--;
    }

    if (strcmp(command, "ARM") == 0)
    {
        TryArm();
        return;
    }
    if ((strcmp(command, "STOP") == 0)
        || (strcmp(command, "DISARM") == 0))
    {
        auto_arm_inhibited = true;   /* stop must mean stop */
        auto_arm_stable_ms = 0U;
        Disarm(BOT_READY);
        UartTrySend("STOPPED (auto-arm off; send ARM or press B1)\r\n");
        return;
    }
    if (strcmp(command, "STATUS") == 0)
    {
        SendStatus();
        return;
    }
    if (strcmp(command, "HELP") == 0)
    {
        SendHelp();
        return;
    }

    if (strncmp(command, "KP ", 3U) == 0)
    {
        float value;
        if (ParseFloat(command + 3U, 0.0f, 100.0f, &value))
        {
            kp = value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: KP range 0..100\r\n");
        }
        return;
    }
    if (strncmp(command, "KI ", 3U) == 0)
    {
        float value;
        if (ParseFloat(command + 3U, 0.0f, 100.0f, &value))
        {
            ki = value;
            integral_error = 0.0f;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: KI range 0..100\r\n");
        }
        return;
    }
    if (strncmp(command, "KD ", 3U) == 0)
    {
        float value;
        if (ParseFloat(command + 3U, 0.0f, 20.0f, &value))
        {
            kd = value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: KD range 0..20\r\n");
        }
        return;
    }
    if (strncmp(command, "TARGET ", 7U) == 0)
    {
        float value;
        if (ParseFloat(command + 7U, -10.0f, 10.0f, &value))
        {
            target_angle_deg = value;
            integral_error = 0.0f;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: TARGET range -10..10\r\n");
        }
        return;
    }
    if (strncmp(command, "DEAD ", 5U) == 0)
    {
        long value;
        if (ParseLong(command + 5U, 0L, 300L, &value))
        {
            motor_deadband = (int16_t)value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: DEAD range 0..300\r\n");
        }
        return;
    }
    if (strncmp(command, "MAXPWM ", 7U) == 0)
    {
        long value;
        if (ParseLong(command + 7U, 100L, PWM_TIMER_MAX, &value))
        {
            maximum_pwm = (int16_t)value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: MAXPWM range 100..799\r\n");
        }
        return;
    }
    if (strncmp(command, "SSIGN ", 6U) == 0)
    {
        long value;
        if (ParseLong(command + 6U, -1L, 1L, &value) && (value != 0L))
        {
            if (sensor_sign != (int8_t)value)
            {
                sensor_sign = (int8_t)value;
                angle_deg = -angle_deg;
                gyro_rate_dps = -gyro_rate_dps;
            }
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: SSIGN must be 1 or -1\r\n");
        }
        return;
    }
    if (strncmp(command, "LSIGN ", 6U) == 0)
    {
        long value;
        if (ParseLong(command + 6U, -1L, 1L, &value) && (value != 0L))
        {
            left_motor_sign = (int8_t)value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: LSIGN must be 1 or -1\r\n");
        }
        return;
    }
    if (strncmp(command, "RSIGN ", 6U) == 0)
    {
        long value;
        if (ParseLong(command + 6U, -1L, 1L, &value) && (value != 0L))
        {
            right_motor_sign = (int8_t)value;
            SendStatus();
        }
        else
        {
            UartTrySend("ERR: RSIGN must be 1 or -1\r\n");
        }
        return;
    }

    if (strncmp(command, "TEST L ", 7U) == 0)
    {
        long value;
        if ((bot_state != BOT_ARMED)
            && ParseLong(
                command + 7U,
                -MOTOR_TEST_LIMIT,
                MOTOR_TEST_LIMIT,
                &value))
        {
            StartMotorTest((int16_t)value, 0);
        }
        else
        {
            UartTrySend("ERR: STOP first; TEST L range -250..250\r\n");
        }
        return;
    }
    if (strncmp(command, "TEST R ", 7U) == 0)
    {
        long value;
        if ((bot_state != BOT_ARMED)
            && ParseLong(
                command + 7U,
                -MOTOR_TEST_LIMIT,
                MOTOR_TEST_LIMIT,
                &value))
        {
            StartMotorTest(0, (int16_t)value);
        }
        else
        {
            UartTrySend("ERR: STOP first; TEST R range -250..250\r\n");
        }
        return;
    }
    if (strncmp(command, "TEST BOTH ", 10U) == 0)
    {
        long value;
        if ((bot_state != BOT_ARMED)
            && ParseLong(
                command + 10U,
                -MOTOR_TEST_LIMIT,
                MOTOR_TEST_LIMIT,
                &value))
        {
            StartMotorTest((int16_t)value, (int16_t)value);
        }
        else
        {
            UartTrySend("ERR: STOP first; TEST BOTH range -250..250\r\n");
        }
        return;
    }

    UartTrySend("ERR: unknown command; type HELP\r\n");
}

static void StartMotorTest(int16_t left, int16_t right)
{
    StopMotors();
    motor_test_active = true;
    motor_test_stop_ms = HAL_GetTick() + MOTOR_TEST_DURATION_MS;
    ApplyMotorOutputs(left, right);
    UartTrySend("TEST: motors run for 400 ms\r\n");
}

static void StopMotorTest(void)
{
    if (!motor_test_active)
    {
        return;
    }

    motor_test_active = false;
    StopMotors();
}

static void SendStatus(void)
{
    char status[UART_TX_CAPACITY];
    int32_t angle_cdeg = (int32_t)(angle_deg * 100.0f);
    int32_t gyro_cdps = (int32_t)(gyro_rate_dps * 100.0f);
    int32_t target_cdeg = (int32_t)(target_angle_deg * 100.0f);
    int32_t kp_x100 = (int32_t)(kp * 100.0f);
    int32_t ki_x100 = (int32_t)(ki * 100.0f);
    int32_t kd_x100 = (int32_t)(kd * 100.0f);

    (void)snprintf(
        status,
        sizeof(status),
        "S=%s ANG=%ld GYR=%ld OUT=%d TGT=%ld "
        "KP=%ld KI=%ld KD=%ld DEAD=%d MAX=%d SS=%d LS=%d RS=%d\r\n",
        StateName(bot_state),
        (long)angle_cdeg,
        (long)gyro_cdps,
        (int)motor_output,
        (long)target_cdeg,
        (long)kp_x100,
        (long)ki_x100,
        (long)kd_x100,
        (int)motor_deadband,
        (int)maximum_pwm,
        (int)sensor_sign,
        (int)left_motor_sign,
        (int)right_motor_sign);
    UartTrySend(status);
}

static void SendHelp(void)
{
    UartTrySend(
        "ARM STOP STATUS | KP/KI/KD n | TARGET n | DEAD n | MAXPWM n\r\n"
        "SSIGN/LSIGN/RSIGN +/-1 | TEST L/R/BOTH n (-250..250, wheels raised)\r\n");
}

static void UartTrySend(const char *text)
{
    size_t length;

    if (huart3.gState != HAL_UART_STATE_READY)
    {
        return;
    }

    length = strlen(text);
    if (length >= sizeof(uart_tx_buffer))
    {
        length = sizeof(uart_tx_buffer) - 1U;
    }

    /*
     * text may already point to uart_tx_buffer (SendStatus), so memmove is
     * intentionally used instead of memcpy.
     */
    (void)memmove(uart_tx_buffer, text, length);
    uart_tx_buffer[length] = '\0';
    (void)HAL_UART_Transmit_IT(
        &huart3,
        (uint8_t *)uart_tx_buffer,
        (uint16_t)length);
}

static void UartSendBlocking(const char *text)
{
    (void)HAL_UART_Transmit(
        &huart3,
        (uint8_t *)text,
        (uint16_t)strlen(text),
        500U);
}

static bool ParseFloat(
    const char *text,
    float minimum,
    float maximum,
    float *value)
{
    char *end;
    float parsed = strtof(text, &end);

    while (isspace((unsigned char)*end))
    {
        end++;
    }

    if ((end == text)
        || (*end != '\0')
        || !isfinite(parsed)
        || (parsed < minimum)
        || (parsed > maximum))
    {
        return false;
    }

    *value = parsed;
    return true;
}

static bool ParseLong(
    const char *text,
    long minimum,
    long maximum,
    long *value)
{
    char *end;
    long parsed = strtol(text, &end, 10);

    while (isspace((unsigned char)*end))
    {
        end++;
    }

    if ((end == text)
        || (*end != '\0')
        || (parsed < minimum)
        || (parsed > maximum))
    {
        return false;
    }

    *value = parsed;
    return true;
}

static int16_t ReadBigEndianInt16(const uint8_t *bytes)
{
    return (int16_t)(((uint16_t)bytes[0] << 8) | bytes[1]);
}

static int16_t ClampInt16(
    int32_t value,
    int16_t minimum,
    int16_t maximum)
{
    if (value < minimum)
    {
        return minimum;
    }
    if (value > maximum)
    {
        return maximum;
    }
    return (int16_t)value;
}

static float ClampFloat(float value, float minimum, float maximum)
{
    if (value < minimum)
    {
        return minimum;
    }
    if (value > maximum)
    {
        return maximum;
    }
    return value;
}

static float NormalizeAngle(float angle)
{
    while (angle > 180.0f)
    {
        angle -= 360.0f;
    }
    while (angle < -180.0f)
    {
        angle += 360.0f;
    }
    return angle;
}

static const char *StateName(BotState state)
{
    switch (state)
    {
        case BOT_BOOT:
            return "BOOT";
        case BOT_READY:
            return "READY";
        case BOT_ARMED:
            return "ARMED";
        case BOT_FALLEN:
            return "FALLEN";
        case BOT_MPU_FAULT:
            return "MPU_FAULT";
        default:
            return "UNKNOWN";
    }
}

static void UpdateLeds(void)
{
    HAL_GPIO_WritePin(
        LD1_GPIO_Port,
        LD1_Pin,
        (bot_state == BOT_ARMED) ? GPIO_PIN_SET : GPIO_PIN_RESET);
    HAL_GPIO_WritePin(
        LD2_GPIO_Port,
        LD2_Pin,
        (bot_state == BOT_READY) ? GPIO_PIN_SET : GPIO_PIN_RESET);
    HAL_GPIO_WritePin(
        LD3_GPIO_Port,
        LD3_Pin,
        ((bot_state == BOT_FALLEN) || (bot_state == BOT_MPU_FAULT))
            ? GPIO_PIN_SET
            : GPIO_PIN_RESET);
}

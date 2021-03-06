// Copyright © 2015-2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by the GPL-2 license described in the
// LICENSE file.

package diag

import (
	"fmt"
	"net/rpc"
	"time"

	"github.com/platinasystems/go/internal/eeprom"
	"github.com/platinasystems/go/internal/i2c"
	"github.com/platinasystems/go/internal/log"
)

var clientA *rpc.Client
var dialed int = 0
var j [MAXOPS]I
var s [MAXOPS]R
var i = I{false, i2c.RW(0), 0, 0, b, 0, 0, 0}
var x int
var b = [34]byte{0}

const MAXOPS = 30

var sd i2c.SMBusData

type I struct {
	InUse     bool
	RW        i2c.RW
	RegOffset uint8
	BusSize   i2c.SMBusSize
	Data      [34]byte
	Bus       int
	Addr      int
	Delay     int
}
type R struct {
	D [34]byte
	E error
}

func diagI2c() error {

	var ucd9090dAdr uint8 = 0x34
	var ledgpiodAdr uint8 = 0x75

	d := eeprom.Device{
		BusIndex:   0,
		BusAddress: 0x55,
	}
	d.GetInfo()
	switch d.Fields.DeviceVersion {
	case 0xff:
		ucd9090dAdr = 0x7e
		ledgpiodAdr = 0x22
	case 0x00:
		ucd9090dAdr = 0x7e
		ledgpiodAdr = 0x22
	default:
		ucd9090dAdr = 0x34
		ledgpiodAdr = 0x75
	}

	var r string
	var result bool

	fmt.Printf("\n%15s|%25s|%10s|%10s|%10s|%10s|%6s|%35s\n", "function", "parameter", "units", "value", "min", "max", "result", "description")
	fmt.Printf("---------------|-------------------------|----------|----------|----------|----------|------|-----------------------------------\n")

	/* diagTest: i2c mon
	check that all i2c monitoring pins read high, stuck high pins will be discovered during i2c ping tests
	*/
	pinstate, _ := gpioGet("I2C1_SCL_MON")
	r = CheckPassB(pinstate, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "i2c1_scl_mon", "-", pinstate, i2cmon_min, i2cmon_max, r, "check mon pin is high")

	pinstate, _ = gpioGet("I2C1_SDA_MON")
	r = CheckPassB(pinstate, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "i2c1_sda_mon", "-", pinstate, i2cmon_min, i2cmon_max, r, "check mon pin is high")

	pinstate, _ = gpioGet("I2C2_SCL_MON")
	r = CheckPassB(pinstate, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "i2c2_scl_mon", "-", pinstate, i2cmon_min, i2cmon_max, r, "check mon pin is high")

	pinstate, _ = gpioGet("I2C2_SDA_MON")
	r = CheckPassB(pinstate, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "i2c2_sda_mon", "-", pinstate, i2cmon_min, i2cmon_max, r, "check mon pin is high")

	/* diagTest: host i2c
	enable host access to main_i2c bus and check that bmc can access mfg eeprom on cpu card
	repeat with fru_i2c bus
	*/
	gpioSet("CPU_TO_MAIN_I2C_EN", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x51, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "cpu_to_main_i2c_en_on", "-", result, i2cping_response_min, i2cping_response_max, r, "enable host bus, ping host eeprom")

	gpioSet("CPU_TO_MAIN_I2C_EN", false)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x51, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "cpu_to_main_i2c_en_off", "-", result, i2cping_noresponse_min, i2cping_noresponse_max, r, "disable host bus, ping host eeprom")
	gpioSet("CPU_TO_FRU_I2C_EN", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x51, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "cpu_to_fru_i2c_en_on", "-", result, i2cping_response_min, i2cping_response_max, r, "enable host bus, ping host eeprom")

	gpioSet("CPU_TO_FRU_I2C_EN", false)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x51, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "cpu_to_fru_i2c_en_off", "-", result, i2cping_noresponse_min, i2cping_noresponse_max, r, "disable host bus, ping host eeprom")
	/* diagTest: i2c power cycle
	disable i2c power and check that i2c devices cannot be accessed
	enable i2c power and check that i2c devices can be accessed
	*/
	gpioSet("P3V3_I2C_EN", false)
	gpioSet("CPU_TO_MAIN_I2C_EN", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x74, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "p3v3_i2c_en_off", "-", result, i2cping_noresponse_min, i2cping_noresponse_max, r, "disable i2c power, ping main_mux0")

	gpioSet("P3V3_I2C_EN", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x74, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "p3v3_i2c_en_on", "-", result, i2cping_response_min, i2cping_response_max, r, "enable i2c power, ping main_mux0")
	gpioSet("CPU_TO_MAIN_I2C_EN", false)

	/* diagTest: i2c resets
	activate i2c reset and validate associated devices cannot be accessed
	*/
	gpioSet("MAIN_I2C_MUX_RST_L", false)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x76, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "main_i2c_mux_rst_l_on", "-", result, i2cping_noresponse_min, i2cping_noresponse_max, r, "enable reset, ping main_mux0")

	gpioSet("MAIN_I2C_MUX_RST_L", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x76, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "main_i2c_mux_rst_l_off", "-", result, i2cping_response_min, i2cping_response_max, r, "disable reset, ping main_mux0")

	gpioSet("FRU_I2C_MUX_RST_L", false)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x72, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "fru_i2c_mux_rst_l_on", "-", result, i2cping_noresponse_min, i2cping_noresponse_max, r, "enable reset, ping fru_mux0")

	gpioSet("FRU_I2C_MUX_RST_L", true)
	time.Sleep(50 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x72, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "fru_i2c_mux_rst_l_off", "-", result, i2cping_response_min, i2cping_response_max, r, "disable reset, ping fru_mux0")

	/* diagTest: P3V3_FAN_EN power cycle
		disable fan board 3.3V power and check that i2c devices cannot be accessed
	        enable fan board 3.3Vpower and check that i2c devices can be accessed
	*/
	gpioSet("P3V3_FAN_EN", false)
	time.Sleep(50 * time.Millisecond)
	diagI2cWrite1Byte(0x01, 0x72, 0x04)
	time.Sleep(10 * time.Millisecond)
	diagI2cWrite1Byte(0x01, 0x20, 0x00)
	result, _ = diagI2cPing(0x01, 0x20, 0x00, 1)
	r = CheckPassB(result, false)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "p3v3_fan_en_off", "-", result, i2cping_response_min, i2cping_response_max, r, "disable fan3.3V, ping fan brd gpio")

	gpioSet("P3V3_FAN_EN", true)
	time.Sleep(50 * time.Millisecond)
	diagI2cWrite1Byte(0x01, 0x20, 0x00)
	result, _ = diagI2cPing(0x01, 0x20, 0x00, 1)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "p3v3_fan_en_on", "-", result, i2cping_response_min, i2cping_response_max, r, "enable fan3.3V, ping fan brd gpio")

	diagI2cWrite1Byte(0x01, 0x72, 0x00)

	/* diagTest: i2c devices
	check all i2c devices are accessible
	*/
	result, _ = diagI2cPing(0x00, 0x76, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_main_mux0", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x01)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x00, ucd9090dAdr, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_ucd9090", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x02)
	time.Sleep(10 * time.Millisecond)
	diagI2cWrite1Byte(0x00, ledgpiodAdr, 0x00)
	result, _ = diagI2cPing(0x00, ledgpiodAdr, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_led_pca9539", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x04)
	time.Sleep(10 * time.Millisecond)
	diagI2cWrite1Byte(0x00, 0x27, 0x00)
	result, _ = diagI2cPing(0x00, 0x27, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_board_id_gpio", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x20)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x6e, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_th_clk_gen", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x40)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x21, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_th1v0_dcdc", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x40)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x22, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_thcore_dcdc", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x80)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x00, 0x2f, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_hwm", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x00, 0x76, 0x00)

	result, _ = diagI2cPing(0x01, 0x72, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_fru_mux0", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x01, 0x72, 0x01)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x50, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_psu0", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x01, 0x72, 0x02)
	time.Sleep(10 * time.Millisecond)
	result, _ = diagI2cPing(0x01, 0x50, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_psu1", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x01, 0x72, 0x04)
	time.Sleep(10 * time.Millisecond)
	diagI2cWrite1Byte(0x01, 0x20, 0x00)
	result, _ = diagI2cPing(0x01, 0x20, 0x00, 10)
	r = CheckPassB(result, true)
	fmt.Printf("%15s|%25s|%10s|%10t|%10t|%10t|%6s|%35s\n", "i2c", "ping_fan_board", "-", result, i2cping_response_min, i2cping_response_max, r, "ping device 10x")

	diagI2cWrite1Byte(0x01, 0x72, 0x00)
	return nil
}

func diagSwitchConsole() error {

	//i2c STOP
	sd[0] = 0
	j[0] = I{true, i2c.Write, 0, 0, sd, int(0x99), int(1), 0}
	err := DoI2cRpc()
	if err != nil {
		return err
	}

	//switch console
	gpioSet("CPU_TO_MAIN_I2C_EN", true)
	time.Sleep(50 * time.Millisecond)
	diagI2cWriteOffsetByte(0x00, 0x74, 0x06, 0xFB)
	gpioSet("CPU_TO_MAIN_I2C_EN", false)
	gpioSet("FP_BTN_UARTSEL_EN_L", true)
	time.Sleep(50 * time.Millisecond)

	//i2c START
	sd[0] = 0
	j[0] = I{true, i2c.Write, 0, 0, sd, int(0x99), int(0), 0}
	err = DoI2cRpc()
	if err != nil {
		return err
	}

	return nil
}

func clearJ() {
	x = 0
	for k := 0; k < MAXOPS; k++ {
		j[k] = i
	}
}

func DoI2cRpc() error {
	if dialed == 0 {
		client, err := rpc.DialHTTP("tcp", "127.0.0.1"+":1233")
		if err != nil {
			log.Print("dialing:", err)
			return err
		}
		clientA = client
		dialed = 1
		time.Sleep(time.Millisecond * time.Duration(50))
	}
	err := clientA.Call("I2cReq.ReadWrite", &j, &s)
	if err != nil {
		log.Print("i2cReq error:", err)
		return err
	}
	clearJ()
	return nil
}

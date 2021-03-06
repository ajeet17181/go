// Copyright © 2015-2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by the GPL-2 license described in the
// LICENSE file.

// Package uptimed publishes the system uptime every 60 seconds to the local
// redis server.
package uptimed

import (
	"bytes"
	"fmt"
	"syscall"
	"time"

	"github.com/platinasystems/go/goes/cmd"
	"github.com/platinasystems/go/goes/lang"
	"github.com/platinasystems/go/internal/redis/publisher"
)

const (
	Name    = "uptimed"
	Apropos = "record system uptime in redis"
	Usage   = "uptimed"
)

var apropos = lang.Alt{
	lang.EnUS: Apropos,
}

func New() Command { return make(Command) }

type Command chan struct{}

func (Command) Apropos() lang.Alt { return apropos }

func (c Command) Close() error {
	close(c)
	return nil
}

func (Command) Kind() cmd.Kind { return cmd.Daemon }

func (c Command) Main(...string) error {
	var si syscall.Sysinfo_t
	err := syscall.Sysinfo(&si)
	if err != nil {
		return err
	}

	pub, err := publisher.New()
	if err != nil {
		return err
	}
	defer pub.Close()

	pub.Print("uptime: ", update())
	t := time.NewTicker(60 * time.Second)
	defer t.Stop()
	for {
		select {
		case <-c:
			return nil
		case <-t.C:
			pub.Print("uptime: ", update())
		}
	}
	return nil
}

func (Command) String() string { return Name }
func (Command) Usage() string  { return Usage }

func update() string {
	var si syscall.Sysinfo_t
	if err := syscall.Sysinfo(&si); err != nil {
		return err.Error()
	}
	buf := new(bytes.Buffer)
	updecades := si.Uptime / (60 * 60 * 24 * 365 * 10)
	upyears := (si.Uptime / (60 * 60 * 24 * 365)) % 10
	upweeks := (si.Uptime / (60 * 60 * 24 * 7)) % 52
	updays := (si.Uptime / (60 * 60 * 24)) % 7
	upminutes := si.Uptime / 60
	uphours := upminutes / 60
	uphours = uphours % 24
	upminutes = upminutes % 60
	if si.Uptime < 60 {
		fmt.Fprint(buf, si.Uptime, " seconds")
	}
	if updecades > 0 {
		fmt.Fprint(buf, updecades, " decade")
		if updecades > 1 {
			fmt.Fprint(buf, "s")
		}
		fmt.Fprint(buf, ", ")
	}
	if upyears > 0 {
		fmt.Fprint(buf, upyears, " year")
		if upyears > 1 {
			fmt.Fprint(buf, "s")
		}
		fmt.Fprint(buf, ", ")
	}
	if upweeks > 0 {
		fmt.Fprint(buf, upweeks, " week")
		if upweeks > 1 {
			fmt.Fprint(buf, "s")
		}
		fmt.Fprint(buf, ", ")
	}
	if updays > 0 {
		fmt.Fprint(buf, updays, " day")
		if updays > 1 {
			fmt.Fprint(buf, "s")
		}
		fmt.Fprint(buf, ", ")
	}
	if uphours > 0 {
		fmt.Fprint(buf, uphours, " hour")
		if uphours > 1 {
			fmt.Fprint(buf, "s")
		}
		fmt.Fprint(buf, ", ")
	}
	if upminutes > 0 {
		fmt.Fprint(buf, upminutes, " minute")
		if upminutes > 1 {
			fmt.Fprint(buf, "s")
		}
	}
	return buf.String()
}

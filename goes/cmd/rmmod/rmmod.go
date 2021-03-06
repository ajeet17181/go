// Copyright © 2015-2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by the GPL-2 license described in the
// LICENSE file.

package rmmod

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"syscall"
	"unsafe"

	"github.com/platinasystems/go/goes/lang"
	"github.com/platinasystems/go/internal/flags"
)

const (
	Name    = "rmmod"
	Apropos = "remove a module from the Linux Kernel"
	Usage   = "rmmod [OPTION]... MODULE..."
	Man     = `
DESCRIPTION
	Remove the named MODULE from the Linux Kernel.
	(MODULE must support unloading)

OPTIONS
	-v	verbose
	-f	force
	-q	silently ignore errors`
)

var (
	apropos = lang.Alt{
		lang.EnUS: Apropos,
	}
	man = lang.Alt{
		lang.EnUS: Man,
	}
)

func New() Command { return Command{} }

type Command struct{}

func (Command) Apropos() lang.Alt { return apropos }
func (Command) Man() lang.Alt     { return man }
func (Command) String() string    { return Name }
func (Command) Usage() string     { return Usage }

func (Command) Complete(args ...string) (c []string) {
	f, err := os.Open("/proc/modules")
	if err != nil {
		return
	}
	defer f.Close()
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := scanner.Text()
		x := strings.Fields(line)
		if len(args) == 0 ||
			strings.HasPrefix(x[0], args[len(args)-1]) {
			c = append(c, x[0])
		}
	}
	return
}

func (Command) Main(args ...string) error {
	flag, args := flags.New(args, "-f", "-q", "-v")
	if len(args) == 0 {
		return fmt.Errorf("MODULE: missing")
	}
	u := 0
	if flag.ByName["-f"] {
		u |= syscall.O_TRUNC
	}
	for _, name := range args {
		bp, err := syscall.BytePtrFromString(name)
		if err != nil {
			return err
		}
		_, _, e := syscall.RawSyscall(syscall.SYS_DELETE_MODULE,
			uintptr(unsafe.Pointer(bp)), uintptr(u), 0)
		if e != 0 {
			if !flag.ByName["-q"] {
				return fmt.Errorf("%v", e)
			}
		} else if flag.ByName["-v"] {
			fmt.Println("Removed", name)
		}
	}
	return nil
}

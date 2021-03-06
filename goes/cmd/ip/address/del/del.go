// Copyright © 2015-2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by the GPL-2 license described in the
// LICENSE file.

package del

import (
	"fmt"

	"github.com/platinasystems/go/goes/lang"
)

const (
	Name    = "del"
	Apropos = "FIXME"
	Usage   = "FIXME"
	Man     = `
DESCRIPTION
	FIXME
`
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

func (Command) Main(args ...string) error {
	fmt.Println("FIXME", Name, args)
	return nil
}

func (Command) String() string { return Name }
func (Command) Usage() string  { return Usage }

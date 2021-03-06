// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build linux

package unix

import (
	"github.com/platinasystems/go/elib"
	"github.com/platinasystems/go/elib/iomux"
	"github.com/platinasystems/go/internal/netlink"
	"github.com/platinasystems/go/vnet"
	"github.com/platinasystems/go/vnet/ethernet"

	"fmt"
	"strings"
	"sync"
	"syscall"
	"unsafe"
)

type tuntap_interface struct {
	m  *Main
	mu sync.Mutex
	// Namespace this interface is currently in.
	namespace *net_namespace
	// Raw socket bound to this interface used for provisioning.
	provision_fd   int
	dev_net_tun_fd int
	iomux.File     // /dev/net/tun fd for this interface.
	hi             vnet.Hi
	si             vnet.Si
	name           ifreq_name
	ifindex        uint32 // linux interface index

	// Tuntap interface has been created (via TUNSETIFF ioctl).
	created bool
	// True when vnet/kernel interface flag sync has started.
	flag_sync_in_progress bool
	// True when vnet/kernel interface flags have been successfully synchronized.
	flag_sync_done bool
	flags          iff_flag
	operState      netlink.IfOperState

	mtuBytes   uint
	mtuBuffers uint

	active_count int32
	to_tx        chan *tx_packet_vector
	pv           *tx_packet_vector

	suspend_saved_out *vnet.RefIn
}

//go:generate gentemplate -d Package=unix -id ifVec -d VecType=interfaceVec -d Type=*tuntap_interface github.com/platinasystems/go/elib/vec.tmpl

func (m *Main) interface_for_si(si vnet.Si) *tuntap_interface {
	return m.vnet_tuntap_interface_by_si[si]
}
func (i *tuntap_interface) Name() string   { return i.name.String() }
func (i *tuntap_interface) String() string { return i.Name() }

func (i *tuntap_interface) set_name(name string) {
	v := i.m.v
	v.HwIf(i.hi).SetName(v, name)
}

func (i *tuntap_interface) setMtu(m *Main, mtu uint) {
	i.mtuBytes = mtu
	i.mtuBuffers = mtu / m.bufferPool.Size
	if mtu%m.bufferPool.Size != 0 {
		i.mtuBuffers++
	}
}

func (i *tuntap_interface) close() {
	i.mu.Lock()
	defer i.mu.Unlock()
	if i.provision_fd > 0 {
		syscall.Close(i.provision_fd)
		i.provision_fd = -1
	}
	if i.dev_net_tun_fd > 0 {
		iomux.Del(i)
		syscall.Close(i.dev_net_tun_fd)
		i.dev_net_tun_fd = -1
	}
}

func (i *tuntap_interface) add_del_namespace(m *Main, ns *net_namespace, is_del bool) {
	if is_del {
		i.close()
	} else {
		is_discovery := !i.created && i.namespace == nil
		if is_discovery {
			return
		}
		i.namespace = ns
		// Close sockets before re-opening in new namespace.
		i.close()
		if err := i.open_sockets(); err != nil {
			panic(err)
		}
		if err := i.create(); err != nil {
			panic(err)
		}
		if err := i.bind(); err != nil {
			panic(err)
		}
		i.start_up()
	}
}

type tuntap_main struct {
	// Selects whether we create tun or tap interfaces.
	isTun      bool
	mtuBytes   uint
	bufferPool *vnet.BufferPool
}

func (m *tuntap_main) Init(v *vnet.Vnet) {
	m.bufferPool = vnet.DefaultBufferPool
	v.AddBufferPool(m.bufferPool)
}

const (
	// TUNSETIFF ifReq flags
	iff_tun          = 1 << 0
	iff_tap          = 1 << 1
	iff_multi_queue  = 1 << 8
	iff_attach_queue = 1 << 9
	iff_detach_queue = 1 << 10
	iff_persist      = 1 << 11
	iff_no_pi        = 1 << 12
	iff_one_queue    = 1 << 13
	iff_vnet_hdr     = 1 << 14
	iff_tun_excl     = 1 << 15
	iff_nofilter     = 1 << 12
)

type ifreq_name [16]byte

func (n ifreq_name) String() string { return strings.TrimRight(string(n[:]), "\x00") }

// Linux interface flags
type iff_flag int

const (
	iff_up_bit, iff_up iff_flag = iota, 1 << iota
	iff_broadcast_bit, iff_broadcast
	iff_debug_bit, iff_debug
	iff_loopback_bit, iff_loopback
	iff_pointopoint_bit, iff_pointopoint
	iff_notrailers_bit, iff_notrailers
	iff_running_bit, iff_running
	iff_noarp_bit, iff_noarp
	iff_promisc_bit, iff_promisc
	iff_allmulti_bit, iff_allmulti
	iff_master_bit, iff_master
	iff_slave_bit, iff_slave
	iff_multicast_bit, iff_multicast
	iff_portsel_bit, iff_portsel
	iff_automedia_bit, iff_automedia
	iff_dynamic_bit, iff_dynamic
	iff_lower_up_bit, iff_lower_up
	iff_dormant_bit, iff_dormant
	iff_echo_bit, iff_echo
)

var iff_flag_names = [...]string{
	iff_up_bit:          "admin-up",
	iff_broadcast_bit:   "broadcast",
	iff_debug_bit:       "debug",
	iff_loopback_bit:    "loopback",
	iff_pointopoint_bit: "point-to-point",
	iff_notrailers_bit:  "no-trailers",
	iff_running_bit:     "running",
	iff_noarp_bit:       "no-arp",
	iff_promisc_bit:     "promiscuous",
	iff_allmulti_bit:    "all-multicast",
	iff_master_bit:      "master",
	iff_slave_bit:       "slave",
	iff_multicast_bit:   "multicast",
	iff_portsel_bit:     "portsel",
	iff_automedia_bit:   "automedia",
	iff_dynamic_bit:     "dynamic",
	iff_lower_up_bit:    "link-up",
	iff_dormant_bit:     "dormant",
	iff_echo_bit:        "echo",
}

func (f iff_flag) String() string { return elib.FlagStringer(iff_flag_names[:], elib.Word(f)) }

type ifreq_flags struct {
	name  ifreq_name
	flags uint16
}

type ifreq_int struct {
	name ifreq_name
	i    int
}

type ifreq_sockaddr_any struct {
	name     ifreq_name
	sockaddr syscall.RawSockaddrAny
}

type ifreq_type int

const (
	ifreq_TUNSETIFF     ifreq_type = syscall.TUNSETIFF
	ifreq_TUNSETPERSIST ifreq_type = syscall.TUNSETPERSIST
	ifreq_GETIFINDEX    ifreq_type = syscall.SIOCGIFINDEX
	ifreq_GETIFFLAGS    ifreq_type = syscall.SIOCGIFFLAGS
	ifreq_SETIFFLAGS    ifreq_type = syscall.SIOCSIFFLAGS
	ifreq_GETIFHWADDR   ifreq_type = syscall.SIOCGIFHWADDR
	ifreq_SETIFHWADDR   ifreq_type = syscall.SIOCSIFHWADDR
	ifreq_SETIFMTU      ifreq_type = syscall.SIOCSIFMTU
	ifreq_SIFTXQLEN     ifreq_type = syscall.SIOCSIFTXQLEN
)

var ifreq_type_names = map[ifreq_type]string{
	ifreq_TUNSETIFF:     "TUNSETIFF",
	ifreq_TUNSETPERSIST: "TUNSETPERSIST",
	ifreq_GETIFINDEX:    "GETIFINDEX",
	ifreq_GETIFFLAGS:    "GETIFFLAGS",
	ifreq_SETIFFLAGS:    "SETIFFLAGS",
	ifreq_GETIFHWADDR:   "GETIFHWADDR",
	ifreq_SETIFHWADDR:   "SETIFHWADDR",
	ifreq_SETIFMTU:      "SETIFMTU",
}

func (t ifreq_type) String() string {
	if s, ok := ifreq_type_names[t]; ok {
		return s
	}
	return fmt.Sprintf("0x%x", int(t))
}

// Create tuntap interfaces for all vnet interfaces not marked as special.
func (m *Main) okHi(hi vnet.Hi) (ok bool) { return m.v.HwIfer(hi).IsUnix() }
func (m *Main) okSi(si vnet.Si) bool      { return m.okHi(m.v.SupHi(si)) }

func (i *tuntap_interface) ioctl_helper(fd int, req ifreq_type, arg uintptr, is_set_flags_down bool) (err error) {
	_, _, e := syscall.Syscall(syscall.SYS_IOCTL, uintptr(fd), uintptr(req), arg)

	// Ignore set if flags "no such device" error on if down.
	// This can happen when an interfaces moves to a new namespace and is harmless.
	if is_set_flags_down && e == syscall.ENODEV {
		return
	}
	if e != 0 {
		err = fmt.Errorf("tuntap ioctl %s: %s", req, e)
	}
	return
}
func (i *tuntap_interface) ioctl(fd int, req ifreq_type, arg uintptr) (err error) {
	return i.ioctl_helper(fd, req, arg, false)
}

func (intf *tuntap_interface) flags_synced() bool { return intf.created && intf.flag_sync_done }

// Set flags and operational state when vnet-owned tuntap interface becomes ready.
func (intf *tuntap_interface) sync_flags() {
	intf.flag_sync_in_progress = true
	if err := intf.set_flags(); err != nil {
		panic(err)
	}
	intf.forceOperState(true)
}

func (intf *tuntap_interface) check_flag_sync_done(msg *netlink.IfInfoMessage) {
	ok := iff_flag(msg.IfInfomsg.Flags)&(iff_up|iff_running|iff_lower_up) == intf.flags
	intf.flag_sync_done = ok
	intf.flag_sync_in_progress = !ok
}

func (intf *tuntap_interface) setOperState() { intf.forceOperState(false) }
func (intf *tuntap_interface) forceOperState(is_force bool) {
	os := netlink.IF_OPER_DOWN
	if intf.si.IsAdminUp(intf.m.v) && intf.hi.IsLinkUp(intf.m.v) {
		os = netlink.IF_OPER_UP
	}
	if os != intf.operState {
		if !intf.flags_synced() && !is_force {
			return
		}
		intf.operState = os
		msg := netlink.NewIfInfoMessage()
		msg.Header.Type = netlink.RTM_SETLINK
		msg.Header.Flags = netlink.NLM_F_REQUEST
		msg.Index = uint32(intf.ifindex)
		msg.L2IfType = uint16(netlink.ARPHRD_ETHER)
		msg.Attrs[netlink.IFLA_OPERSTATE] = os
		intf.namespace.NetlinkTx(msg, false)
	}
}

func (m *Main) SwIfAddDel(v *vnet.Vnet, si vnet.Si, isDel bool) (err error) {
	hi := m.v.SupHi(si)
	if !m.okHi(hi) {
		// Unknown interface punts get sent to error node.
		m.rx_node.set_next(si, rx_node_next_error)
		return
	}

	// Tuntap interfaces are never deleted; only created.
	if isDel {
		return
	}

	if si.IsSwSubInterface(m.v) {
		return
	}

	intf := &tuntap_interface{
		m:  m,
		hi: hi,
		si: si,
	}

	name := si.Name(v)
	copy(intf.name[:], name)

	if m.vnet_tuntap_interface_by_si == nil {
		m.vnet_tuntap_interface_by_si = make(map[vnet.Si]*tuntap_interface)
	}
	m.vnet_tuntap_interface_by_si[si] = intf
	if m.vnet_tuntap_interface_by_address == nil {
		m.vnet_tuntap_interface_by_address = make(map[string]*tuntap_interface)
	}
	m.vnet_tuntap_interface_by_address[string(hi.GetAddress(v))] = intf
	return
}

func (m *Main) netlink_discovery_done_for_all_namespaces() (err error) {
	nm := &m.net_namespace_main

	// Create any VNET interfaces that were not found via netlink discovery.
	for si, intf := range m.vnet_tuntap_interface_by_si {
		if _, ok := nm.interface_by_si[si]; !ok {
			intf.namespace = &nm.default_namespace
			err = intf.init(m)
			if err != nil {
				return
			}
		}
	}

	// Initialize other previously existing vnet tuntap interfaces.
	for _, nsi := range nm.interface_by_si {
		if intf := nsi.tuntap; intf != nil {
			intf.namespace = nsi.namespace
			err = intf.init(m)
			if err != nil {
				return
			}

			intf.get_flags()
		}
	}

	// Perform all defered registrations for unix interfaces.
	for _, hw := range m.registered_hwifer_by_si {
		m.RegisterHwInterface(hw)
	}

	return
}

func (intf *tuntap_interface) open_sockets() (err error) {
	ns := intf.namespace
	err, _ = elib.WithNamespace(ns.ns_fd, ns.m.default_namespace.ns_fd, syscall.CLONE_NEWNET, func() (err error) {
		if intf.dev_net_tun_fd, err = syscall.Open("/dev/net/tun", syscall.O_RDWR, 0); err != nil {
			err = fmt.Errorf("tuntap open /dev/net/tun: %s", err)
			return
		}
		if intf.provision_fd, err = syscall.Socket(syscall.AF_PACKET, syscall.SOCK_RAW, int(eth_p_all)); err != nil {
			err = fmt.Errorf("tuntap socket AF_PACKET: %s", err)
		}
		return
	})
	if err = syscall.SetsockoptInt(intf.provision_fd, syscall.SOL_SOCKET, syscall.SO_RCVBUF, 4<<20); err != nil {
		err = fmt.Errorf("tuntap SO_RCVBUF: %s", err)
	}
	return
}

// Create interface (set flags) and make persistent (e.g. interface stays around when we die).
func (intf *tuntap_interface) create() (err error) {
	r := ifreq_flags{name: intf.name}
	r.flags = iff_no_pi
	if intf.m.isTun {
		r.flags |= iff_tun
	} else {
		r.flags |= iff_tap
	}
	intf.created = true
	if err = intf.ioctl(intf.dev_net_tun_fd, ifreq_TUNSETIFF, uintptr(unsafe.Pointer(&r))); err != nil {
		return
	}
	if err = intf.ioctl(intf.dev_net_tun_fd, ifreq_TUNSETPERSIST, 1); err != nil {
		return
	}
	return
}

// Bind the provisioning socket to the interface.
func (intf *tuntap_interface) bind() (err error) {
	sa := syscall.SockaddrLinklayer{
		Ifindex:  int(intf.ifindex),
		Protocol: eth_p_all,
	}
	if err = syscall.Bind(intf.provision_fd, &sa); err != nil {
		err = fmt.Errorf("tuntap bind: %s", err)
	}
	return
}

func (intf *tuntap_interface) start_up() {
	intf.to_tx = make(chan *tx_packet_vector, vnet.MaxVectorLen)
	intf.Fd = intf.dev_net_tun_fd
	iomux.Add(intf)
}

func (intf *tuntap_interface) init(m *Main) (err error) {
	err = intf.open_sockets()
	defer func() {
		if err != nil {
			intf.close()
		}
	}()

	// Create interface (set flags) and make persistent (e.g. interface stays around when we die).
	if err = intf.create(); err != nil {
		return
	}

	intf.bind()

	if eifer, ok := m.v.HwIfer(intf.hi).(ethernet.HwInterfacer); ok {
		ei := eifer.GetInterface()

		// Set MTU.
		{
			intf.mtuBytes = ei.MaxPacketSize()
			if intf.mtuBytes == 0 {
				intf.mtuBytes = m.mtuBytes
			}
			r := ifreq_int{name: intf.name}
			r.i = int(intf.mtuBytes)
			if err = intf.ioctl(intf.provision_fd, ifreq_SETIFMTU, uintptr(unsafe.Pointer(&r))); err != nil {
				return
			}
			intf.setMtu(m, intf.mtuBytes)
		}

		// Increase transmit queue.  Default of 500 in drivers/net/tun.c causes packet loss at high rates.
		{
			r := ifreq_int{name: intf.name}
			r.i = 5000
			if err = intf.ioctl(intf.provision_fd, ifreq_SIFTXQLEN, uintptr(unsafe.Pointer(&r))); err != nil {
				return
			}
		}

		// For tap interfaces, set ethernet address of interface.
		if !m.isTun {
			r := ifreq_sockaddr_any{name: intf.name}
			r.sockaddr.Addr.Family = syscall.ARPHRD_ETHER

			// Only set address if it changes.  If address is reset to same value, kernel will remove arps for some reason.
			if err = intf.ioctl(intf.provision_fd, ifreq_GETIFHWADDR, uintptr(unsafe.Pointer(&r))); err != nil {
				err = fmt.Errorf("%s: %s", err, &ei.Address)
				return
			}
			same_address := true
			for i := range ei.Address {
				same_address = r.sockaddr.Addr.Data[i] == int8(ei.Address[i])
				if !same_address {
					break
				}
			}
			if !same_address {
				for i := range ei.Address {
					r.sockaddr.Addr.Data[i] = int8(ei.Address[i])
				}
				if err = intf.ioctl(intf.provision_fd, ifreq_SETIFHWADDR, uintptr(unsafe.Pointer(&r))); err != nil {
					err = fmt.Errorf("%s: %s", err, &ei.Address)
					return
				}
			}
		}
	}

	// Hook up unix rx node to interface transmit node.
	next := m.v.AddNamedNext(&m.rx_node, intf.Name())
	m.rx_node.set_next(intf.si, rx_node_next(next))

	intf.start_up()

	return
}

func (intf *tuntap_interface) set_flags() (err error) {
	r := ifreq_int{
		name: intf.name,
		i:    int(intf.flags),
	}
	is_set_flags_down := intf.flags&iff_up == 0
	err = intf.ioctl_helper(intf.provision_fd, ifreq_SETIFFLAGS, uintptr(unsafe.Pointer(&r)), is_set_flags_down)
	return
}

func (intf *tuntap_interface) get_flags() (err error) {
	r := ifreq_int{
		name: intf.name,
	}
	err = intf.ioctl(intf.provision_fd, ifreq_GETIFFLAGS, uintptr(unsafe.Pointer(&r)))
	intf.flags = iff_flag(r.i)
	isUp := intf.flags&iff_up != 0
	err = intf.si.SetAdminUp(intf.m.v, isUp)
	intf.flag_sync_in_progress = false
	intf.flag_sync_done = true
	intf.forceOperState(true)
	return
}

func (m *Main) maybeChangeFlag(intf *tuntap_interface, isUp bool, flag iff_flag) (err error) {
	change := false
	switch {
	case isUp && intf.flags&flag != flag:
		change = true
		intf.flags |= flag
	case !isUp && intf.flags&flag != 0:
		change = true
		intf.flags &^= flag
	}
	if change && intf.flags_synced() {
		err = intf.set_flags()
	}
	return
}

func (m *Main) SwIfAdminUpDown(v *vnet.Vnet, si vnet.Si, isUp bool) (err error) {
	if !m.okSi(si) || si.IsSwSubInterface(v) {
		return
	}
	intf := m.interface_for_si(si)
	err = m.maybeChangeFlag(intf, isUp, iff_up|iff_running)
	if err != nil {
		return
	}
	intf.setOperState()
	return
}

func (m *Main) HwIfLinkUpDown(v *vnet.Vnet, hi vnet.Hi, isUp bool) (err error) {
	if !m.okHi(hi) {
		return
	}
	intf := m.interface_for_si(v.HwIf(hi).Si())
	err = m.maybeChangeFlag(intf, isUp, iff_lower_up)
	if err != nil {
		return
	}
	intf.setOperState()
	return
}

var eth_p_all = uint16(vnet.Uint16(syscall.ETH_P_ALL).FromHost())

func (m *Main) Init() (err error) {
	// Suitable defaults for an Ethernet-like tun/tap device.
	m.mtuBytes = 4096 + 256

	m.v.RegisterSwIfAddDelHook(m.SwIfAddDel)
	m.v.RegisterSwIfAdminUpDownHook(m.SwIfAdminUpDown)
	m.v.RegisterHwIfLinkUpDownHook(m.HwIfLinkUpDown)
	return
}

// Copyright © 2015-2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by the GPL-2 license described in the
// LICENSE file.

package netns

const Man = `
DESCRIPTION
	A network namespace is logically another copy of the network stack,
	with its own routes, firewall rules, and network devices.

	By default a process inherits its network namespace from its parent.
	Initially all the processes share the same default network namespace
	from the init process.

	By convention a named network namespace is an object at
	/var/run/netns/NAME that can be opened. The file descriptor resulting
	from opening /var/run/netns/NAME refers to the specified network
	namespace. Holding that file descriptor open keeps the network
	namespace alive. The file descriptor can be used with the setns(2)
	system call to change the network namespace associated with a task.

	For applications that are aware of network namespaces, the convention
	is to look for global network configuration files first in
	/etc/netns/NAME/ then in /etc/.  For example, if you want a different
	version of /etc/resolv.conf for a network namespace used to isolate
	your vpn you would name it /etc/netns/myvpn/resolv.conf.

	ip netns exec automates handling of this configuration, file convention
	for network namespace unaware applications, by creating a mount
	namespace and bind mounting all of the per network namespace configure
	files into their traditional location in /etc.

	ip netns list
		Show all of the named network namespaces

		This command displays all of the network namespaces in
		/var/run/netns


	ip netns add NAME
		Create a new named network namespace

		If NAME is available in /var/run/netns/ this command creates a
		new network namespace and assigns NAME.


	ip [-all] netns delete [ NAME ]
		Delete the name of a network namespace(s)

		If NAME is present in /var/run/netns it is umounted and the
		mount point is removed. If this is the last user of the network
		namespace the network namespace will be freed and all physical
		devices will be moved to the default one, otherwise the network
		namespace persists until it has no more users. ip netns delete
		may fail if the mount point is in use in another mount names‐
		pace.

		If -all option was specified then all the network namespace
		names will be removed.

		It is possible to lose the physical device when it was moved to
		netns and then this netns was deleted with a running process:

			ip netns add net0
			ip link set dev eth0 netns net0
			ip netns exec net0 SOME_PROCESS_IN_BACKGROUND
			ip netns del net0

		and eth0 will appear in the default netns only after
		SOME_PROCESS_IN_BACKGROUND will exit or will be killed. To
		prevent this the processes running in net0 should be killed
		before deleting the netns:

			ip netns pids net0 | xargs kill
			ip netns del net0

	ip netns set NAME NETNSID
		Assign an id to a peer network namespace

		This command assigns a id to a peer network namespace. This id
		is valid only in the current network namespace.  This id will
		be used by the kernel in some netlink messages. If no id is
		assigned when the kernel needs it, it will be automatically
		assigned by the kernel.  Once it is assigned, it's not possible
		to change it.

	ip netns identify [PID]
		Report network namespaces names for process

		This command walks through /var/run/netns and finds all the
		network namespace names for network namespace of the specified
		process, if PID is not specified then the current process will
		be used.

	ip netns list-id
		List network namespace ids (nsid)

		Network namespace ids are used to identify a peer network
		namespace. This command displays nsid of the current network
		namespace and provides the corresponding iproute2 netns name
		(from /var/run/netns) if any.

	ip netns list-pids NAME
		Report processes in the named network namespace

		This command walks through proc and finds all of the process
		who have the named network namespace as their primary network
		namespace.

	ip [-all] netns exec [ NAME ] cmd ...
		Run cmd in the named network namespace

		This command allows applications that are network namespace
		unaware to be run in something other than the default network
		namespace with all of the configuration for the specified
		network namespace appearing in the customary global locations.
		A network namespace and bind mounts are used to move files from
		their network namespace specific location to their default
		locations without affecting other processes.

		If -all option was specified then cmd will be executed
		synchronously on the each named network namespace even if cmd
		fails on some of them. Network namespace name is printed on
		each cmd executing.

	ip netns monitor
		Report as network namespace names are added and deleted

		This command watches network namespace name addition and
		deletion events and prints a line for each event it sees.


EXAMPLES
	ip netns list
		Shows the list of current named network namespaces

	ip netns add vpn
		Creates a network namespace and names it vpn

	ip netns exec vpn ip link set lo up
		Bring up the loopback interface in the vpn network namespace.

SEE ALSO
	man ip || ip -man

AUTHOR
	Original Manpage by Eric W. Biederman
`

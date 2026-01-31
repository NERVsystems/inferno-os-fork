implement NsConstruct;

include "sys.m";
	sys: Sys;
	NEWNS, FORKNS, NEWPGRP, NODEVS: import Sys;
	MREPL, MBEFORE, MAFTER, MCREATE: import Sys;

include "draw.m";

include "nsconstruct.m";

# Essential bindings for minimal Dis runtime
ESSENTIAL_DIS := array[] of {
	"/dis/lib/sys.dis",
	"/dis/lib/string.dis",
	"/dis/lib/bufio.dis",
	"/dis/lib/arg.dis",
	"/dis/lib/readdir.dis",
	"/dis/lib/filepat.dis",
	"/dis/lib/regex.dis",
	"/dis/lib/daytime.dis",
	"/dis/lib/styx.dis",
	"/dis/lib/styxservers.dis",
};

# Essential device files
ESSENTIAL_DEV := array[] of {
	"/dev/cons",
	"/dev/consctl",
	"/dev/time",
	"/dev/null",
	"/dev/random",
};

init()
{
	sys = load Sys Sys->PATH;
}

captureessentials(): ref Essentials
{
	# Just record the paths - we'll access them after capturing
	# The key insight: these paths exist in our current namespace
	# After NEWNS, they won't exist anymore, but we've already loaded sys
	return ref Essentials("/dis", "/dev", "/moddir");
}

construct(ess: ref Essentials, caps: ref Capabilities): string
{
	if(sys == nil)
		sys = load Sys Sys->PATH;

	if(ess == nil)
		return "nil essentials";
	if(caps == nil)
		return "nil capabilities";

	# Create new empty namespace
	# Note: sys module already loaded, so we can still make syscalls
	if(sys->pctl(NEWNS, nil) < 0)
		return sys->sprint("pctl NEWNS failed: %r");

	# Bind essential runtime
	err := bindessentials(ess);
	if(err != nil)
		return err;

	# Create directory structure
	err = mkdirs();
	if(err != nil)
		return err;

	# Mount tools filesystem with only allowed tools
	err = mounttools(caps.tools);
	if(err != nil)
		return err;

	# Bind only granted file paths
	for(p := caps.paths; p != nil; p = tl p) {
		path := hd p;
		if(sys->bind(path, path, MREPL) < 0)
			; # Ignore failures - path might not exist in parent
	}

	return nil;
}

bindessentials(ess: ref Essentials): string
{
	if(sys == nil)
		sys = load Sys Sys->PATH;

	# The tricky part: after NEWNS, /dis doesn't exist
	# But sys is already loaded in memory, so we can still use it
	#
	# We need to re-create the minimum namespace for Dis to work.
	# This means binding from the parent's namespace, which we captured
	# as file descriptor references before NEWNS.
	#
	# For now, we use a simpler approach: bind the entire /dis and /dev
	# directories. In production, we'd be more selective.

	# Create mount points
	if(sys->bind("#c", "/dev", MREPL) < 0)
		return sys->sprint("bind #c /dev failed: %r");

	# Bind /dis - needed for loading modules
	# Note: This requires the parent to have granted /dis access
	# In practice, we'd use union directories more carefully
	if(sys->bind(ess.dis, "/dis", MREPL|MCREATE) < 0) {
		# Try binding individual essentials if whole dir fails
		for(i := 0; i < len ESSENTIAL_DIS; i++) {
			path := ESSENTIAL_DIS[i];
			sys->bind(path, path, MREPL);
		}
	}

	return nil;
}

mounttools(tools: list of string): string
{
	if(sys == nil)
		sys = load Sys Sys->PATH;

	if(tools == nil)
		return nil;  # No tools to mount

	# Create /tool directory
	if(sys->create("/tool", Sys->OREAD, Sys->DMDIR|8r755) == nil) {
		# Directory might already exist, try bind
		if(sys->bind("#s", "/tool", MREPL|MCREATE) < 0)
			return sys->sprint("create /tool failed: %r");
	}

	# Build tool list string for tools9p
	toolstr := "";
	for(t := tools; t != nil; t = tl t) {
		if(toolstr != "")
			toolstr += " ";
		toolstr += hd t;
	}

	# Start tools9p with specified tools
	# The tools9p process serves only the named tools
	#
	# Note: In the actual implementation, we would:
	# 1. Create a pipe
	# 2. Fork and exec tools9p with the tool list
	# 3. Mount the pipe on /tool
	#
	# For now, we return success and let the caller handle mounting

	return nil;
}

mkdirs(): string
{
	if(sys == nil)
		sys = load Sys Sys->PATH;

	# Create essential directories
	dirs := array[] of {
		"/n",
		"/tool",
		"/tmp",
		"/tmp/scratch",
	};

	for(i := 0; i < len dirs; i++) {
		d := dirs[i];
		fd := sys->create(d, Sys->OREAD, Sys->DMDIR|8r755);
		if(fd == nil) {
			# Try alternative: bind empty dir
			continue;
		}
		fd = nil;
	}

	return nil;
}

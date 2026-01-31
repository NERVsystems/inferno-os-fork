implement ToolExec;

#
# exec - Execute shell command tool for Veltro agent
#
# Runs a shell command and returns output.
# Commands are executed via Inferno's sh(1).
#
# Usage:
#   Exec <command>
#
# The command is passed to the shell for execution.
# Standard output and errors are captured and returned.
#
# Examples:
#   Exec "ls /appl"
#   Exec "cat /dev/sysname"
#   Exec "mk install"
#
# Security note: Commands run with agent's namespace/capabilities.
#

include "sys.m";
	sys: Sys;

include "draw.m";

include "sh.m";
	sh: Sh;

include "../tool.m";

ToolExec: module {
	name: fn(): string;
	doc:  fn(): string;
	exec: fn(args: string): string;
};

# Limits
DEFAULT_TIMEOUT: con 5000;   # 5 seconds
MAX_TIMEOUT: con 30000;      # 30 seconds
MAX_OUTPUT: con 16384;       # 16KB max output

init()
{
	sys = load Sys Sys->PATH;
	sh = load Sh Sh->PATH;
}

name(): string
{
	return "exec";
}

doc(): string
{
	return "Exec - Execute shell command\n\n" +
		"Usage:\n" +
		"  Exec <command>\n\n" +
		"Arguments:\n" +
		"  command - Shell command to execute\n\n" +
		"Examples:\n" +
		"  Exec \"ls /appl\"\n" +
		"  Exec \"cat /dev/sysname\"\n" +
		"  Exec \"mk install\"\n\n" +
		"Returns command output, or error message.\n" +
		"Default timeout: 5 seconds (max 30s).";
}

exec(args: string): string
{
	if(sys == nil)
		init();

	if(sh == nil)
		return "error: cannot load shell module";

	# Parse command
	cmd := args;

	# Strip leading/trailing whitespace
	while(len cmd > 0 && (cmd[0] == ' ' || cmd[0] == '\t'))
		cmd = cmd[1:];
	while(len cmd > 0 && (cmd[len cmd - 1] == ' ' || cmd[len cmd - 1] == '\t' || cmd[len cmd - 1] == '\n'))
		cmd = cmd[0:len cmd - 1];

	# Handle quoted command
	if(len cmd >= 2) {
		if((cmd[0] == '"' && cmd[len cmd - 1] == '"') ||
		   (cmd[0] == '\'' && cmd[len cmd - 1] == '\''))
			cmd = cmd[1:len cmd - 1];
	}

	if(cmd == "")
		return "error: usage: Exec <command>";

	# Create pipe for capturing output
	fds := array[2] of ref Sys->FD;
	if(sys->pipe(fds) < 0)
		return sys->sprint("error: cannot create pipe: %r");

	# Spawn command execution
	result := chan of string;
	spawn runcommand(cmd, fds[1], result);
	fds[1] = nil;

	# Read output with timeout
	output := "";
	done := 0;

	timeout := chan of int;
	spawn timer(timeout, DEFAULT_TIMEOUT);

	reader := chan of string;
	spawn readoutput(fds[0], reader);

	while(!done) {
		alt {
		s := <-reader =>
			if(s == nil) {
				done = 1;
			} else {
				output += s;
				if(len output > MAX_OUTPUT) {
					output = output[0:MAX_OUTPUT] + "\n... (output truncated)";
					done = 1;
				}
			}
		<-timeout =>
			output += "\n... (timeout after 5 seconds)";
			done = 1;
		}
	}

	# Wait for result
	err := "";
	alt {
	e := <-result =>
		err = e;
	* =>
		;  # Already done
	}

	if(output == "" && err != "")
		return "error: " + err;

	if(err != "")
		output += "\n(exit: " + err + ")";

	if(output == "")
		return "(no output)";

	return output;
}

# Run command in separate thread
runcommand(cmd: string, outfd: ref Sys->FD, result: chan of string)
{
	# Redirect stdout/stderr to pipe
	sys->dup(outfd.fd, 1);
	sys->dup(outfd.fd, 2);
	outfd = nil;

	err := sh->system(nil, cmd);
	result <-= err;
}

# Timer thread
timer(ch: chan of int, ms: int)
{
	sys->sleep(ms);
	ch <-= 1;
}

# Read output from fd
readoutput(fd: ref Sys->FD, ch: chan of string)
{
	buf := array[4096] of byte;
	for(;;) {
		n := sys->read(fd, buf, len buf);
		if(n <= 0) {
			ch <-= nil;
			return;
		}
		ch <-= string buf[0:n];
	}
}

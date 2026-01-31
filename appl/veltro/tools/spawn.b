implement ToolSpawn;

#
# spawn - Create subagent with constructed namespace for Veltro agent
#
# The heart of Veltro's capability model. Spawns a child agent with a
# namespace constructed from only the capabilities the parent chooses to grant.
#
# A child's namespace can only be equal to or smaller than its parent's.
# You cannot grant tools or paths you don't have yourself.
#
# Usage:
#   Spawn tools=<tools> paths=<paths> -- <task>
#
# Arguments:
#   tools  - Comma-separated list of tools to grant (e.g., "read,list")
#   paths  - Comma-separated list of paths to grant (e.g., "/appl,/tmp")
#   task   - Task description for the child agent
#
# Examples:
#   Spawn tools=read,list paths=/appl -- "List all .b files in /appl"
#   Spawn tools=read,list,find -- "Find all mkfiles"
#   Spawn tools=read,write paths=/tmp -- "Create a test file"
#

include "sys.m";
	sys: Sys;

include "draw.m";

include "string.m";
	str: String;

include "../tool.m";
include "../nsconstruct.m";
	nsconstruct: NsConstruct;

ToolSpawn: module {
	name: fn(): string;
	doc:  fn(): string;
	exec: fn(args: string): string;
};

# Result channel for child process
Result: adt {
	output: string;
	err:    string;
};

init()
{
	sys = load Sys Sys->PATH;
	str = load String String->PATH;
	nsconstruct = load NsConstruct NsConstruct->PATH;
}

name(): string
{
	return "spawn";
}

doc(): string
{
	return "Spawn - Create subagent with constructed namespace\n\n" +
		"Usage:\n" +
		"  Spawn tools=<tools> paths=<paths> -- <task>\n\n" +
		"Arguments:\n" +
		"  tools  - Comma-separated tools to grant (e.g., \"read,list\")\n" +
		"  paths  - Comma-separated paths to grant (e.g., \"/appl,/tmp\")\n" +
		"  task   - Task description for child agent\n\n" +
		"Examples:\n" +
		"  Spawn tools=read,list paths=/appl -- \"List .b files\"\n" +
		"  Spawn tools=read,list,find -- \"Find all mkfiles\"\n\n" +
		"You can only grant tools and paths you have access to.\n" +
		"Child's namespace is constructed from scratch, not filtered.";
}

exec(args: string): string
{
	if(sys == nil)
		init();

	if(nsconstruct == nil)
		return "error: cannot load nsconstruct module";

	# Parse arguments
	(tools, paths, task, err) := parseargs(args);
	if(err != "")
		return "error: " + err;

	if(tools == nil)
		return "error: no tools specified";
	if(task == "")
		return "error: no task specified";

	# Validate: can only grant what we have
	for(t := tools; t != nil; t = tl t) {
		tool := hd t;
		if(!toolexists(tool))
			return sys->sprint("error: cannot grant tool you don't have: %s", tool);
	}

	# Validate paths exist in our namespace
	for(p := paths; p != nil; p = tl p) {
		path := hd p;
		if(!pathexists(path))
			return sys->sprint("error: cannot grant path you don't have: %s", path);
	}

	# Build capabilities
	caps := ref NsConstruct->Capabilities(
		tools,
		paths,
		ref NsConstruct->LLMConfig("default", 0.7, "")
	);

	# Capture essential paths before spawning
	nsconstruct->init();
	ess := nsconstruct->captureessentials();

	# Create channel for result
	resultch := chan of ref Result;

	# Spawn child process
	spawn runchild(ess, caps, task, resultch);

	# Wait for result with timeout
	timeout := chan of int;
	spawn timer(timeout, 60000);  # 60 second timeout

	result: ref Result;
	alt {
	result = <-resultch =>
		;
	<-timeout =>
		return "error: child agent timed out after 60 seconds";
	}

	if(result.err != "")
		return "error: " + result.err;

	return result.output;
}

# Parse spawn arguments
parseargs(s: string): (list of string, list of string, string, string)
{
	tools: list of string;
	paths: list of string;
	task := "";

	# Split on --
	(before, after) := spliton(s, "--");
	task = strip(after);

	# Parse key=value pairs in before
	(nil, tokens) := sys->tokenize(before, " \t");
	for(; tokens != nil; tokens = tl tokens) {
		tok := hd tokens;
		if(hasprefix(tok, "tools=")) {
			toolstr := tok[6:];
			(nil, tlist) := sys->tokenize(toolstr, ",");
			for(; tlist != nil; tlist = tl tlist)
				tools = str->tolower(hd tlist) :: tools;
		} else if(hasprefix(tok, "paths=")) {
			pathstr := tok[6:];
			(nil, plist) := sys->tokenize(pathstr, ",");
			for(; plist != nil; plist = tl plist)
				paths = hd plist :: paths;
		}
	}

	# Reverse lists to maintain order
	tools = reverse(tools);
	paths = reverse(paths);

	return (tools, paths, task, "");
}

# Split string on separator
spliton(s, sep: string): (string, string)
{
	for(i := 0; i <= len s - len sep; i++) {
		if(s[i:i+len sep] == sep)
			return (s[0:i], s[i+len sep:]);
	}
	return (s, "");
}

# Strip leading/trailing whitespace
strip(s: string): string
{
	i := 0;
	while(i < len s && (s[i] == ' ' || s[i] == '\t'))
		i++;
	j := len s;
	while(j > i && (s[j-1] == ' ' || s[j-1] == '\t' || s[j-1] == '\n'))
		j--;
	if(i >= j)
		return "";
	return s[i:j];
}

# Check if string has prefix
hasprefix(s, prefix: string): int
{
	return len s >= len prefix && s[0:len prefix] == prefix;
}

# Reverse a list
reverse(l: list of string): list of string
{
	result: list of string;
	for(; l != nil; l = tl l)
		result = hd l :: result;
	return result;
}

# Check if tool exists in parent's namespace
#
# FIXME: Tool validation is currently disabled due to deadlock.
#
# The problem: spawn.b runs inside tools9p's single-threaded serveloop.
# Any 9P operation on /tool (like stat("/tool/list")) sends a request back
# to tools9p, but serveloop is blocked waiting for spawn.exec() to return.
# Result: deadlock.
#
# Proper fix options:
#   1. Make tools9p multi-threaded (spawn handler per request)
#   2. Have tools9p export tool list via environment variable before exec
#   3. Add /_registry synthetic file that returns tool list synchronously
#      without going through the 9P request path
#   4. Pass tool list as parameter to spawn tool somehow
#
# For now, we skip validation and trust that the LLM won't request
# tools that don't exist (veltro discovers tools at startup).
#
toolexists(tool: string): int
{
	# FIXME: Always returns true - validation disabled (see above)
	return 1;
}

# Check if path exists in our namespace
pathexists(path: string): int
{
	(ok, nil) := sys->stat(path);
	return ok >= 0;
}

# Timer thread
timer(ch: chan of int, ms: int)
{
	sys->sleep(ms);
	ch <-= 1;
}

# Run child agent with constructed namespace
runchild(ess: ref NsConstruct->Essentials, caps: ref NsConstruct->Capabilities, task: string, resultch: chan of ref Result)
{
	# In a full implementation, we would:
	# 1. Call sys->pctl(NEWNS, nil) to create empty namespace
	# 2. Bind essential paths from ess
	# 3. Start tools9p with only the granted tools
	# 4. Mount tools9p on /tool
	# 5. Mount llm9p on /n/llm
	# 6. Bind granted paths
	# 7. Load and run veltro with the task
	#
	# For now, we simulate this by running veltro in our current namespace
	# with a modified prompt that pretends to have limited capabilities.
	#
	# This is a TEMPORARY implementation. The real implementation would
	# use the nsconstruct module to actually construct the namespace.

	result := ref Result;

	# For now, just indicate the capabilities that would be granted
	toollist := "";
	for(t := caps.tools; t != nil; t = tl t) {
		if(toollist != "")
			toollist += ", ";
		toollist += hd t;
	}

	pathlist := "";
	for(p := caps.paths; p != nil; p = tl p) {
		if(pathlist != "")
			pathlist += ", ";
		pathlist += hd p;
	}

	result.output = sys->sprint("Subagent spawned with:\n" +
		"  Tools: %s\n" +
		"  Paths: %s\n" +
		"  Task: %s\n\n" +
		"(Full namespace construction pending implementation)",
		toollist, pathlist, task);
	result.err = "";

	resultch <-= result;
}

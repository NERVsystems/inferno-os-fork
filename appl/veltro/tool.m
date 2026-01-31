#
# tool.m - Interface for Veltro agent tools
#
# Each tool is a loadable Limbo module that implements this interface.
# Tools are stateless - each invocation gets fresh arguments and returns
# a result string. State, if needed, lives in the 9P server's per-fid data.
#

Tool: module {
	# Return the tool name (lowercase, e.g., "read")
	name: fn(): string;

	# Return documentation for this tool
	doc: fn(): string;

	# Execute the tool with given arguments
	# Returns result string (may include error messages)
	exec: fn(args: string): string;
};

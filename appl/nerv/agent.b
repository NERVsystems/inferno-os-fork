# NervNode Agent - Namespace-Bounded LLM Agent
#
# This agent runs inside Inferno and accesses the LLM and tools
# entirely through the filesystem namespace. Its capabilities are
# bounded by what's mounted in its namespace.
#
# Usage:
#   mount -A tcp!llm-server!5641 /n/llm
#   mount -A tcp!osm-server!5640 /n/osm
#   agent "Find the coordinates of the Eiffel Tower"

implement Agent;

include "sys.m";
    sys: Sys;

include "bufio.m";
    bufio: Bufio;
    Iobuf: import bufio;

include "draw.m";

include "string.m";
    str: String;

Agent: module {
    init: fn(ctxt: ref Draw->Context, argv: list of string);
};

# Agent configuration
LLM_QUERY := "/n/llm/prompt/query";
LLM_SYSTEM := "/n/llm/system/query";

# Safety limits
MAX_ITERATIONS := 5;       # Maximum iterations before forced stop
MAX_ERRORS := 3;           # Maximum consecutive errors before stop
MAX_HISTORY := 10;         # Maximum actions to remember

# Action record for history
Action: adt {
    cmd:     string;   # Command that was run
    path:    string;   # Primary path involved
    outcome: string;   # "OK" or "ERR"
    detail:  string;   # Result or error message
};

# System prompt that teaches the agent about its namespace
SYSTEM_PROMPT := "You are an agent with access to a filesystem namespace. " +
    "You interact with tools by reading and writing files. " +
    "To use a tool: echo 'input' > /path/to/tool/query && cat /path/to/tool/query\n" +
    "Some tools have multiple parameter files instead of a single query file. " +
    "Use 'ls' to explore tool directories if unsure. " +
    "Respond with ONLY the shell commands needed. No explanations.";

init(ctxt: ref Draw->Context, argv: list of string)
{
    sys = load Sys Sys->PATH;
    bufio = load Bufio Bufio->PATH;
    str = load String String->PATH;

    if(bufio == nil || str == nil) {
        sys->fprint(sys->fildes(2), "agent: failed to load modules\n");
        raise "fail:modules";
    }

    sys->print("NervNode Agent starting\n");

    # Get task from command line
    if(len argv < 2) {
        sys->fprint(sys->fildes(2), "usage: agent 'task description'\n");
        raise "fail:usage";
    }

    task := "";
    argv = tl argv;
    for(; argv != nil; argv = tl argv) {
        if(task != "")
            task += " ";
        task += hd argv;
    }

    sys->print("Task: %s\n", task);

    # Show current namespace
    sys->print("\nAvailable namespace:\n");
    showns("/n");

    # Set system prompt
    if(setsystem(SYSTEM_PROMPT) < 0) {
        sys->print("Warning: could not set system prompt\n");
    }

    # Run agent loop
    runagent(task);
}

# Show namespace contents (like ls -R)
showns(path: string)
{
    fd := sys->open(path, Sys->OREAD);
    if(fd == nil)
        return;

    sys->print("%s:\n", path);

    for(;;) {
        (n, dir) := sys->dirread(fd);
        if(n <= 0)
            break;
        for(i := 0; i < n; i++) {
            name := dir[i].name;
            if(dir[i].mode & Sys->DMDIR)
                sys->print("  %s/\n", name);
            else
                sys->print("  %s\n", name);
        }
    }
    sys->print("\n");

    # Recurse into subdirectories
    fd = sys->open(path, Sys->OREAD);
    if(fd == nil)
        return;
    for(;;) {
        (n, dir) := sys->dirread(fd);
        if(n <= 0)
            break;
        for(i := 0; i < n; i++) {
            if(dir[i].mode & Sys->DMDIR) {
                subpath := path + "/" + dir[i].name;
                showns(subpath);
            }
        }
    }
}

# Set the LLM system prompt
setsystem(prompt: string): int
{
    fd := sys->open(LLM_SYSTEM, Sys->OWRITE);
    if(fd == nil)
        return -1;

    data := array of byte prompt;
    n := sys->write(fd, data, len data);
    return n;
}

# Query the LLM
query(prompt: string): string
{
    # Write prompt
    fd := sys->open(LLM_QUERY, Sys->OWRITE);
    if(fd == nil) {
        sys->fprint(sys->fildes(2), "agent: cannot open %s: %r\n", LLM_QUERY);
        return "";
    }

    data := array of byte prompt;
    if(sys->write(fd, data, len data) < 0) {
        sys->fprint(sys->fildes(2), "agent: write error: %r\n");
        return "";
    }

    # Read response
    fd = sys->open(LLM_QUERY, Sys->OREAD);
    if(fd == nil) {
        sys->fprint(sys->fildes(2), "agent: cannot read response: %r\n");
        return "";
    }

    buf := array[65536] of byte;
    response := "";
    while((n := sys->read(fd, buf, len buf)) > 0) {
        response += string buf[0:n];
    }

    return response;
}

# Build the prompt for the agent
buildprompt(task: string): string
{
    # Get namespace listing
    nslist := getnslist("/n");

    prompt := "Your namespace:\n" + nslist + "\n\n";
    prompt += "Task: " + task;

    return prompt;
}

# Get namespace listing as a string (recursive, but only llm/ and osm/)
getnslist(path: string): string
{
    result := "";

    fd := sys->open(path, Sys->OREAD);
    if(fd == nil)
        return result;

    result += path + ":\n";

    for(;;) {
        (n, dir) := sys->dirread(fd);
        if(n <= 0)
            break;
        for(i := 0; i < n; i++) {
            name := dir[i].name;
            if(dir[i].mode & Sys->DMDIR) {
                result += "  " + name + "/\n";
                # Recurse into llm and osm only
                if(name == "llm" || name == "osm")
                    result += getnslist(path + "/" + name);
            } else {
                result += "  " + name + "\n";
            }
        }
    }

    return result;
}

# Run the agent loop with safety limits
runagent(task: string)
{
    iterations := 0;
    consecutive_errors := 0;
    history: list of ref Action;  # Action history (most recent first)
    facts: list of string;        # Learned facts

    sys->print("\n=== Agent v3 Starting (max %d iterations, with memory) ===\n", MAX_ITERATIONS);

    while(iterations < MAX_ITERATIONS && consecutive_errors < MAX_ERRORS) {
        iterations++;
        sys->print("\n=== Iteration %d/%d ===\n", iterations, MAX_ITERATIONS);

        # Build prompt with namespace and task
        prompt := buildprompt(task);

        # Always include summary if we have history
        if(history != nil || facts != nil) {
            summary := buildsummary(history, facts);
            prompt += "\n\n" + summary;
        }

        if(iterations == 1)
            sys->print("Prompt:\n%s\n", prompt);

        response := query(prompt);
        if(response == "") {
            sys->fprint(sys->fildes(2), "agent: no response from LLM (error %d/%d)\n",
                consecutive_errors+1, MAX_ERRORS);
            consecutive_errors++;
            history = addaction(history, "query", "/n/llm/prompt/query", "ERR", "empty response");
            continue;
        }

        sys->print("\n=== LLM Response ===\n%s\n", response);

        # Execute commands and collect actions
        sys->print("\n=== Executing Commands ===\n");
        (nerrs, actions, newfacts) := executecommands_v2(response);

        # Add actions to history
        for(; actions != nil; actions = tl actions)
            history = hd actions :: history;

        # Add any new facts
        for(; newfacts != nil; newfacts = tl newfacts)
            facts = hd newfacts :: facts;

        # Trim history to MAX_HISTORY
        history = trimhistory(history, MAX_HISTORY);

        if(nerrs > 0) {
            consecutive_errors += nerrs;
            sys->print("Errors this iteration: %d (consecutive: %d/%d)\n",
                nerrs, consecutive_errors, MAX_ERRORS);
        } else {
            consecutive_errors = 0;  # Reset consecutive counter, but keep history
            if(hascompletion(response)) {
                sys->print("\n=== Task Complete ===\n");
                break;
            }
        }
    }

    if(iterations >= MAX_ITERATIONS)
        sys->print("\n=== Safety Limit Reached (%d iterations) ===\n", MAX_ITERATIONS);
    if(consecutive_errors >= MAX_ERRORS)
        sys->print("\n=== Too Many Errors (%d consecutive) ===\n", consecutive_errors);

    sys->print("\n=== Agent Complete ===\n");
}

# Build summary from history and facts
buildsummary(history: list of ref Action, facts: list of string): string
{
    s := "=== Context from previous actions ===\n";

    # Add facts first
    if(facts != nil) {
        s += "Facts:\n";
        for(f := facts; f != nil; f = tl f)
            s += "  " + hd f + "\n";
    }

    # Collect errors with counts
    errcounts: list of (string, int);
    for(h := history; h != nil; h = tl h) {
        a := hd h;
        if(a.outcome == "ERR") {
            key := a.path + ": " + a.detail;
            errcounts = inccount(errcounts, key);
        }
    }

    if(errcounts != nil) {
        s += "Errors:\n";
        for(; errcounts != nil; errcounts = tl errcounts) {
            (key, count) := hd errcounts;
            s += sys->sprint("  %s (x%d)\n", key, count);
        }
    }

    # Show last few actions
    s += "Recent actions:\n";
    actioncount := 0;
    for(ha := history; ha != nil && actioncount < 5; ha = tl ha) {
        a := hd ha;
        s += sys->sprint("  %s %s → %s", a.cmd, a.path, a.outcome);
        if(a.outcome == "OK" && a.cmd == "ls" && len a.detail < 80)
            s += " (" + a.detail + ")";
        s += "\n";
        actioncount++;
    }

    return s;
}

# Increment count for key in list
inccount(counts: list of (string, int), key: string): list of (string, int)
{
    result: list of (string, int);
    found := 0;
    for(; counts != nil; counts = tl counts) {
        (k, c) := hd counts;
        if(k == key) {
            result = (k, c+1) :: result;
            found = 1;
        } else {
            result = (k, c) :: result;
        }
    }
    if(!found)
        result = (key, 1) :: result;
    return result;
}

# Trim history to max length
trimhistory(history: list of ref Action, max: int): list of ref Action
{
    if(max <= 0)
        return nil;
    count := 0;
    result: list of ref Action;
    for(; history != nil && count < max; history = tl history) {
        result = hd history :: result;
        count++;
    }
    # Reverse to maintain order
    rev: list of ref Action;
    for(; result != nil; result = tl result)
        rev = hd result :: rev;
    return rev;
}

# Add action to history
addaction(history: list of ref Action, cmd, path, outcome, detail: string): list of ref Action
{
    a := ref Action(cmd, path, outcome, detail);
    return a :: history;
}

# Check if response indicates task completion
hascompletion(response: string): int
{
    # Look for explicit completion indicators
    if(len response >= 4 && response[0:4] == "DONE")
        return 1;
    if(len response >= 8 && response[0:8] == "Complete")
        return 1;

    # Don't consider ls commands as completing a task
    lines := splitlines(response);
    for(; lines != nil; lines = tl lines) {
        line := trim(hd lines);
        if(line == "" || line[0] == '#')
            continue;
        if(len line >= 3 && line[0:3] == "```")
            continue;
        if(len line >= 2 && line[0:2] == "ls")
            return 0;  # ls is exploratory, not completion
    }

    # For cat commands that read results, consider potentially complete
    # (if no errors, the result was obtained)
    return 1;
}

# Execute shell commands from the LLM response
# Returns (error_count, actions, facts)
executecommands_v2(response: string): (int, list of ref Action, list of string)
{
    errors := 0;
    actions: list of ref Action;
    facts: list of string;

    lines := splitlines(response);
    for(; lines != nil; lines = tl lines) {
        line := hd lines;
        line = trim(line);

        # Skip empty lines and comments
        if(line == "" || line[0] == '#')
            continue;

        # Skip markdown code block markers
        if(len line >= 3 && line[0:3] == "```")
            continue;

        # Split on && and execute each part
        cmds := splitand(line);
        for(; cmds != nil; cmds = tl cmds) {
            cmd := trim(hd cmds);
            if(cmd == "")
                continue;

            (ok, path, detail, fact) := execcmd_v2(cmd);
            if(ok < 0) {
                errors++;
                actions = ref Action(getcmdtype(cmd), path, "ERR", detail) :: actions;
            } else {
                actions = ref Action(getcmdtype(cmd), path, "OK", detail) :: actions;
            }

            # Add any discovered facts
            if(fact != "")
                facts = fact :: facts;
        }
    }

    # Reverse actions to maintain order
    rev: list of ref Action;
    for(; actions != nil; actions = tl actions)
        rev = hd actions :: rev;

    return (errors, rev, facts);
}

# Get command type from command string
getcmdtype(cmd: string): string
{
    if(len cmd > 5 && cmd[0:5] == "echo ")
        return "write";
    if(len cmd > 4 && cmd[0:4] == "cat ")
        return "read";
    if(len cmd >= 2 && cmd[0:2] == "ls")
        return "ls";
    return "unknown";
}

# Execute a single command
# Returns (0, "") on success, (-1, "error message") on error
execcmd(cmd: string): (int, string)
{
    cmd = trim(cmd);
    if(cmd == "")
        return (0, "");

    # Execute echo > file commands
    if(len cmd > 5 && cmd[0:5] == "echo ")
        return exececho(cmd);

    # Execute cat commands
    if(len cmd > 4 && cmd[0:4] == "cat ")
        return execcat(cmd[4:]);

    # Execute ls commands
    if(len cmd >= 2 && cmd[0:2] == "ls")
        return execls(cmd);

    sys->print("Skipping unknown command: %s\n", cmd);
    return (0, "");
}

# Execute a single command (v2)
# Returns (ok, path, detail, fact)
# fact is empty unless we learned something (e.g., from ls)
execcmd_v2(cmd: string): (int, string, string, string)
{
    cmd = trim(cmd);
    if(cmd == "")
        return (0, "", "", "");

    # Execute echo > file commands
    if(len cmd > 5 && cmd[0:5] == "echo ")
        return exececho_v2(cmd);

    # Execute cat commands
    if(len cmd > 4 && cmd[0:4] == "cat ")
        return execcat_v2(cmd[4:]);

    # Execute ls commands
    if(len cmd >= 2 && cmd[0:2] == "ls")
        return execls_v2(cmd);

    sys->print("Skipping unknown command: %s\n", cmd);
    return (0, cmd, "unknown", "");
}

# Execute ls command (v2)
# Returns (ok, path, listing, fact)
execls_v2(cmd: string): (int, string, string, string)
{
    path := "/n";
    if(len cmd > 3)
        path = trim(cmd[3:]);

    sys->print("Exec: ls %s\n", path);

    fd := sys->open(path, Sys->OREAD);
    if(fd == nil) {
        errmsg := "file does not exist";
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, path, errmsg, "");
    }

    listing := "";
    for(;;) {
        (n, dir) := sys->dirread(fd);
        if(n <= 0)
            break;
        for(i := 0; i < n; i++) {
            name := dir[i].name;
            if(listing != "")
                listing += " ";
            listing += name;
            if(dir[i].mode & Sys->DMDIR)
                sys->print("  %s/\n", name);
            else
                sys->print("  %s\n", name);
        }
    }

    # Generate fact if this looks like a tool directory
    fact := "";
    if(hasfile(listing, "result") && !hasfile(listing, "query")) {
        fact = path + " is Type B (use param files + result)";
    } else if(hasfile(listing, "query")) {
        fact = path + " is Type A (use query file)";
    }

    return (0, path, listing, fact);
}

# Check if listing contains a file name
hasfile(listing, name: string): int
{
    words := splitwords(listing);
    for(; words != nil; words = tl words) {
        if(hd words == name)
            return 1;
    }
    return 0;
}

# Split string on whitespace
splitwords(s: string): list of string
{
    words: list of string;
    start := -1;
    for(i := 0; i <= len s; i++) {
        if(i == len s || s[i] == ' ' || s[i] == '\t' || s[i] == '\n') {
            if(start >= 0 && i > start) {
                words = s[start:i] :: words;
            }
            start = -1;
        } else if(start < 0) {
            start = i;
        }
    }
    # Reverse
    rev: list of string;
    for(; words != nil; words = tl words)
        rev = hd words :: rev;
    return rev;
}

# Execute echo command (v2)
# Returns (ok, path, detail, fact)
exececho_v2(cmd: string): (int, string, string, string)
{
    sys->print("Exec: %s\n", cmd);

    # Find the > or >>
    redir := -1;
    for(i := 0; i < len cmd; i++) {
        if(cmd[i] == '>') {
            redir = i;
            break;
        }
    }

    if(redir < 0) {
        sys->print("  (no redirection found)\n");
        return (-1, cmd, "missing redirection", "");
    }

    # Extract data and file
    data := cmd[5:redir];  # after "echo "
    file := cmd[redir+1:];

    # Clean up data (remove quotes)
    data = trim(data);
    if(len data >= 2) {
        if((data[0] == '"' && data[len data - 1] == '"') ||
           (data[0] == '\'' && data[len data - 1] == '\'')) {
            data = data[1:len data - 1];
        }
    }

    # Clean up file
    file = trim(file);
    if(len file > 0 && file[0] == '>')  # handle >>
        file = file[1:];
    file = trim(file);

    sys->print("  Writing '%s' to %s\n", data, file);

    # Write to file
    fd := sys->open(file, Sys->OWRITE);
    if(fd == nil) {
        errmsg := "file does not exist";
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, file, errmsg, "");
    }

    bytes := array of byte data;
    n := sys->write(fd, bytes, len bytes);
    if(n < 0) {
        errmsg := "write failed";
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, file, errmsg, "");
    }
    sys->print("  Wrote %d bytes\n", n);
    return (0, file, sys->sprint("%d bytes", n), "");
}

# Execute cat command (v2)
# Returns (ok, path, content, fact)
execcat_v2(file: string): (int, string, string, string)
{
    file = trim(file);

    sys->print("Exec: cat %s\n", file);

    fd := sys->open(file, Sys->OREAD);
    if(fd == nil) {
        errmsg := "file does not exist";
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, file, errmsg, "");
    }

    buf := array[8192] of byte;
    content := "";
    sys->print("  Result:\n");
    while((n := sys->read(fd, buf, len buf)) > 0) {
        content += string buf[0:n];
        sys->print("%s", string buf[0:n]);
    }
    sys->print("\n");

    # Truncate for history
    if(len content > 100)
        content = content[0:100] + "...";

    return (0, file, content, "");
}

# Execute ls command
execls(cmd: string): (int, string)
{
    path := "/n";
    if(len cmd > 3)
        path = trim(cmd[3:]);

    sys->print("Exec: ls %s\n", path);

    fd := sys->open(path, Sys->OREAD);
    if(fd == nil) {
        errmsg := sys->sprint("ls %s: file does not exist", path);
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, errmsg);
    }

    for(;;) {
        (n, dir) := sys->dirread(fd);
        if(n <= 0)
            break;
        for(i := 0; i < n; i++) {
            name := dir[i].name;
            if(dir[i].mode & Sys->DMDIR)
                sys->print("  %s/\n", name);
            else
                sys->print("  %s\n", name);
        }
    }
    return (0, "");
}

# Split a command line on &&
splitand(s: string): list of string
{
    result: list of string;
    start := 0;
    i := 0;
    while(i < len s) {
        if(i+1 < len s && s[i] == '&' && s[i+1] == '&') {
            if(i > start)
                result = s[start:i] :: result;
            start = i + 2;
            i = start;
        } else {
            i++;
        }
    }
    if(start < len s)
        result = s[start:] :: result;

    # Reverse the list
    rev: list of string;
    for(; result != nil; result = tl result)
        rev = hd result :: rev;
    return rev;
}

# Execute an echo command (echo "data" > file)
# Returns (0, "") on success, (-1, "error message") on error
exececho(cmd: string): (int, string)
{
    # Very simple parser for: echo "data" > file
    # or: echo 'data' > file
    sys->print("Exec: %s\n", cmd);

    # Find the > or >>
    redir := -1;
    for(i := 0; i < len cmd; i++) {
        if(cmd[i] == '>') {
            redir = i;
            break;
        }
    }

    if(redir < 0) {
        sys->print("  (no redirection found)\n");
        return (-1, "echo command missing redirection (>)");
    }

    # Extract data and file
    data := cmd[5:redir];  # after "echo "
    file := cmd[redir+1:];

    # Clean up data (remove quotes)
    data = trim(data);
    if(len data >= 2) {
        if((data[0] == '"' && data[len data - 1] == '"') ||
           (data[0] == '\'' && data[len data - 1] == '\'')) {
            data = data[1:len data - 1];
        }
    }

    # Clean up file
    file = trim(file);
    if(len file > 0 && file[0] == '>')  # handle >>
        file = file[1:];
    file = trim(file);

    sys->print("  Writing '%s' to %s\n", data, file);

    # Write to file
    fd := sys->open(file, Sys->OWRITE);
    if(fd == nil) {
        errmsg := sys->sprint("cannot write to %s: file does not exist", file);
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, errmsg);
    }

    bytes := array of byte data;
    n := sys->write(fd, bytes, len bytes);
    if(n < 0) {
        errmsg := sys->sprint("write to %s failed", file);
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, errmsg);
    }
    sys->print("  Wrote %d bytes\n", n);
    return (0, "");
}

# Execute a cat command
# Returns (0, "") on success, (-1, "error message") on error
execcat(file: string): (int, string)
{
    file = trim(file);

    sys->print("Exec: cat %s\n", file);

    fd := sys->open(file, Sys->OREAD);
    if(fd == nil) {
        errmsg := sys->sprint("cat %s: file does not exist", file);
        sys->fprint(sys->fildes(2), "  Error: %s\n", errmsg);
        return (-1, errmsg);
    }

    buf := array[8192] of byte;
    sys->print("  Result:\n");
    while((n := sys->read(fd, buf, len buf)) > 0) {
        sys->print("%s", string buf[0:n]);
    }
    sys->print("\n");
    return (0, "");
}

# Helper: split string into lines
splitlines(s: string): list of string
{
    lines: list of string;
    start := 0;
    for(i := 0; i < len s; i++) {
        if(s[i] == '\n') {
            if(i > start)
                lines = s[start:i] :: lines;
            start = i + 1;
        }
    }
    if(start < len s)
        lines = s[start:] :: lines;

    # Reverse the list
    result: list of string;
    for(; lines != nil; lines = tl lines)
        result = hd lines :: result;
    return result;
}

# Helper: trim whitespace
trim(s: string): string
{
    # Trim leading whitespace
    start := 0;
    for(; start < len s; start++) {
        c := s[start];
        if(c != ' ' && c != '\t' && c != '\n' && c != '\r')
            break;
    }

    # Trim trailing whitespace
    end := len s;
    for(; end > start; end--) {
        c := s[end-1];
        if(c != ' ' && c != '\t' && c != '\n' && c != '\r')
            break;
    }

    if(start >= end)
        return "";
    return s[start:end];
}

# Placeholder - Tool registry
implement Registry;

include "sys.m";
    sys: Sys;

include "draw.m";

Registry: module {
    init: fn(ctxt: ref Draw->Context, argv: list of string);
    register: fn(name: string, addr: string);
    lookup: fn(name: string): string;
};

Tool: adt {
    name:   string;
    addr:   string;
    schema: string;
    desc:   string;
};

tools: list of ref Tool;

init(ctxt: ref Draw->Context, argv: list of string)
{
    sys = load Sys Sys->PATH;
    sys->print("NervNode Registry module loaded\n");
}

register(name: string, addr: string)
{
    t := ref Tool(name, addr, "", "");
    tools = t :: tools;
}

lookup(name: string): string
{
    for(l := tools; l != nil; l = tl l) {
        t := hd l;
        if(t.name == name)
            return t.addr;
    }
    return "";
}

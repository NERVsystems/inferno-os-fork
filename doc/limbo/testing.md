# Limbo Testing Framework

A Go-style testing framework for Limbo programs, providing structured test execution, assertions, and reporting.

## Overview

The testing framework provides:
- **T adt** - Test context with assertions and logging
- **limbtest** - Test runner command for discovering and executing tests
- **Go-style output** - Familiar `=== RUN`, `--- PASS/FAIL/SKIP` format

## Quick Start

### 1. Write a Test File

Create a file ending in `_test.b`:

```limbo
implement MyTest;

include "sys.m";
    sys: Sys;
include "draw.m";
include "testing.m";
    testing: Testing;
    T: import testing;

MyTest: module {
    init: fn(nil: ref Draw->Context, args: list of string);
};

passed := 0;
failed := 0;
skipped := 0;

# Helper to run tests
run(name: string, testfn: ref fn(t: ref T))
{
    t := testing->newT(name);
    {
        testfn(t);
    } exception {
    "fail:fatal" => ;
    "fail:skip" => ;
    "*" => t.failed = 1;
    }
    if(testing->done(t)) passed++;
    else if(t.skipped) skipped++;
    else failed++;
}

# Test functions
testExample(t: ref T)
{
    t.asserteq(1 + 1, 2, "basic math");
    t.assertseq("hello", "hello", "strings match");
}

testSkipped(t: ref T)
{
    t.skip("not implemented yet");
}

init(nil: ref Draw->Context, args: list of string)
{
    sys = load Sys Sys->PATH;
    testing = load Testing Testing->PATH;
    testing->init();

    # Parse -v flag
    for(a := args; a != nil; a = tl a)
        if(hd a == "-v") testing->verbose(1);

    # Run tests
    run("Example", testExample);
    run("Skipped", testSkipped);

    # Report results
    if(testing->summary(passed, failed, skipped) > 0)
        raise "fail:tests failed";
}
```

### 2. Compile and Run

```sh
# Inside Inferno
limbo -I /module mycode_test.b
limbtest mycode_test.dis

# Or compile and run in one step
limbtest -c mycode_test.b
```

### 3. View Results

```
=== RUN   Example
--- PASS: Example (0.00s)
=== RUN   Skipped
--- SKIP: Skipped (0.00s)
    not implemented yet

PASS
1 passed, 1 skipped
```

## Testing Module API

### Initialization

```limbo
include "testing.m";
    testing: Testing;
    T: import testing;

testing = load Testing Testing->PATH;
testing->init();
```

### Configuration

```limbo
testing->verbose(1);      # Enable verbose output
v := testing->getverbose(); # Get current setting
```

### Creating Tests

```limbo
t := testing->newT("TestName");  # Creates test, prints "=== RUN TestName"
```

### T Methods

#### Logging
```limbo
t.log("message");              # Add to test output
```

#### Assertions (return 1 on success, 0 on failure)
```limbo
t.assert(condition, "message");           # Boolean condition
t.asserteq(got, want, "message");         # Integer equality
t.assertne(got, notexpect, "message");    # Integer inequality
t.assertseq(got, want, "message");        # String equality
t.assertsne(got, notexpect, "message");   # String inequality
t.assertnil(got, "message");              # String is nil
t.assertnotnil(got, "message");           # String is not nil
```

#### Failure Handling
```limbo
t.error("message");    # Mark failed, continue execution
t.fatal("message");    # Mark failed, raise "fail:fatal"
t.skip("reason");      # Mark skipped, raise "fail:skip"
```

### Finalizing Tests

```limbo
ok := testing->done(t);  # Print result, return 1 if passed
```

### Summary

```limbo
exitcode := testing->summary(passed, failed, skipped);
```

## limbtest Command

### Usage

```
limbtest [-v] [-c] [paths...]
```

### Flags

- `-v` - Verbose mode (show all log output)
- `-c` - Compile `.b` files before running

### Path Patterns

```sh
limbtest                      # Run *.dis tests in current dir
limbtest /tests               # Run tests in /tests directory
limbtest /tests/...           # Recursive (all subdirectories)
limbtest mytest.dis           # Run specific test
limbtest -c mytest.b          # Compile and run
```

## Test File Conventions

### Naming
- Test files: `*_test.b` (source) or `*_test.dis` (compiled)
- Test functions: `testXxx(t: ref T)` (by convention)

### Structure

Every test file should:
1. Implement a module with `init()`
2. Load and initialize the testing module
3. Define test functions accepting `ref T`
4. Run tests with exception handling
5. Call `testing->summary()` and raise on failure

### Boilerplate Helper

The `run()` helper function handles exception wrapping:

```limbo
run(name: string, testfn: ref fn(t: ref T))
{
    t := testing->newT(name);
    {
        testfn(t);
    } exception {
    "fail:fatal" => ;
    "fail:skip" => ;
    "*" => t.failed = 1;
    }
    if(testing->done(t)) passed++;
    else if(t.skipped) skipped++;
    else failed++;
}
```

## Table-Driven Tests

Use arrays for data-driven testing:

```limbo
testAddition(t: ref T)
{
    cases := array[] of {
        (1, 2, 3),
        (0, 0, 0),
        (-1, 1, 0),
    };

    for(i := 0; i < len cases; i++) {
        (a, b, want) := cases[i];
        got := add(a, b);
        t.asserteq(got, want, sys->sprint("add(%d, %d)", a, b));
    }
}
```

## Best Practices

1. **One assertion per concept** - Group related assertions in one test
2. **Descriptive messages** - Include context in assertion messages
3. **Use skip for incomplete tests** - Better than commenting out
4. **Clean up resources** - Use `defer` patterns or explicit cleanup
5. **Test both success and failure** - Verify error cases too

## Limbo-Specific Notes

- In Limbo, `""` (empty string) equals `nil`
- Use `t.assertnotnil()` only for non-empty strings
- Function references work within a module but not across modules
- Each test file handles its own test execution (no global registry)

## Output Format

The framework produces Go-style output:

```
=== RUN   TestName
--- PASS: TestName (0.12s)
=== RUN   TestFailing
--- FAIL: TestFailing (0.01s)
    assertion message
=== RUN   TestSkipped
--- SKIP: TestSkipped (0.00s)
    skip reason

FAIL
1 passed, 1 failed, 1 skipped
```

## Files

- `module/testing.m` - Module interface
- `appl/lib/testing.b` - Library implementation
- `appl/cmd/limbtest.b` - Test runner
- `tests/testing/testing_test.b` - Framework self-tests
- `tests/example_test.b` - Example test file

## Building

```sh
# Build the testing library
cd appl/lib && mk testing.dis

# Build the test runner
cd appl/cmd && mk limbtest.dis

# Build tests
cd tests && mk
```

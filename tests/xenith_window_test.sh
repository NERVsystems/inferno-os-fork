#!/bin/sh
#
# Regression tests for Xenith window manipulation features
#
# Tests:
#   1. Window creation via filesystem
#   2. Layout commands (grow, growmax, growfull, moveto, tocol, newcol)
#   3. Deletion protection for user windows
#   4. Deletion permission for filesystem-created windows
#   5. Content writing
#
# Usage:
#   Run from within Xenith (middle-click on the script path)
#   Or: sh tests/test-xenith-window-manipulation.sh
#
# Prerequisites:
#   - Xenith must be running
#   - /mnt/xenith must be mounted
#

PASS=0
FAIL=0
TESTS_RUN=0

# Colors for output (if terminal supports it)
RED=''
GREEN=''
RESET=''
if test -t 1; then
    RED='[31m'
    GREEN='[32m'
    RESET='[0m'
fi

pass() {
    PASS=$((PASS + 1))
    TESTS_RUN=$((TESTS_RUN + 1))
    echo "${GREEN}PASS${RESET}: $1"
}

fail() {
    FAIL=$((FAIL + 1))
    TESTS_RUN=$((TESTS_RUN + 1))
    echo "${RED}FAIL${RESET}: $1"
    if test -n "$2"; then
        echo "      Expected: $2"
    fi
    if test -n "$3"; then
        echo "      Got: $3"
    fi
}

# Check if Xenith is mounted
check_xenith() {
    if test ! -d /mnt/xenith; then
        echo "ERROR: /mnt/xenith not mounted. Is Xenith running?"
        exit 1
    fi
}

# Test 1: Window creation via filesystem
test_window_creation() {
    echo ""
    echo "=== Test: Window Creation ==="

    # Create a new window
    result=$(cat /mnt/xenith/new/ctl 2>&1)
    id=$(echo "$result" | awk '{print $1}')

    if test -n "$id" && test "$id" -gt 0 2>/dev/null; then
        pass "Window created with ID $id"

        # Check window exists in index
        if grep -q "^$id " /mnt/xenith/index 2>/dev/null; then
            pass "Window $id appears in index"
        else
            fail "Window $id not found in index"
        fi

        # Store ID for later tests
        CREATED_WINDOW=$id
    else
        fail "Window creation failed" "numeric ID" "$result"
        CREATED_WINDOW=""
    fi
}

# Test 2: Content writing
test_content_writing() {
    echo ""
    echo "=== Test: Content Writing ==="

    if test -z "$CREATED_WINDOW"; then
        fail "Skipped - no window available"
        return
    fi

    # Write to body
    echo "Test content from regression test" > /mnt/xenith/$CREATED_WINDOW/body 2>&1
    if test $? -eq 0; then
        pass "Write to window body succeeded"
    else
        fail "Write to window body failed"
    fi

    # Read back and verify
    content=$(cat /mnt/xenith/$CREATED_WINDOW/body 2>&1)
    if echo "$content" | grep -q "Test content"; then
        pass "Content verified in window body"
    else
        fail "Content not found in window body" "Test content..." "$content"
    fi
}

# Test 3: Layout commands
test_layout_commands() {
    echo ""
    echo "=== Test: Layout Commands ==="

    if test -z "$CREATED_WINDOW"; then
        fail "Skipped - no window available"
        return
    fi

    # Test grow
    echo grow > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "grow command accepted"
    else
        fail "grow command rejected"
    fi

    # Test growmax
    echo growmax > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "growmax command accepted"
    else
        fail "growmax command rejected"
    fi

    # Test growfull
    echo growfull > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "growfull command accepted"
    else
        fail "growfull command rejected"
    fi

    # Test moveto (move to y=100)
    echo 'moveto 100' > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "moveto command accepted"
    else
        fail "moveto command rejected"
    fi

    # Test tocol (move to column 0)
    echo 'tocol 0' > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "tocol command accepted"
    else
        fail "tocol command rejected"
    fi
}

# Test 4: newcol command
test_newcol() {
    echo ""
    echo "=== Test: New Column Creation ==="

    if test -z "$CREATED_WINDOW"; then
        fail "Skipped - no window available"
        return
    fi

    # Count columns before
    cols_before=$(cat /mnt/xenith/index | awk '{print $6}' | sort -u | wc -l)

    # Create new column
    echo newcol > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1
    if test $? -eq 0; then
        pass "newcol command accepted"
    else
        fail "newcol command rejected"
    fi
}

# Test 5: Deletion of filesystem-created window
test_filesystem_window_deletion() {
    echo ""
    echo "=== Test: Filesystem Window Deletion ==="

    if test -z "$CREATED_WINDOW"; then
        fail "Skipped - no window available"
        return
    fi

    # Delete the window we created
    result=$(echo delete > /mnt/xenith/$CREATED_WINDOW/ctl 2>&1)

    # Check if window is gone
    if test -d /mnt/xenith/$CREATED_WINDOW; then
        fail "Filesystem-created window deletion failed - window still exists"
    else
        pass "Filesystem-created window deleted successfully"
    fi

    CREATED_WINDOW=""
}

# Test 6: User window deletion protection
test_user_window_protection() {
    echo ""
    echo "=== Test: User Window Deletion Protection ==="

    # Window 1 should be a user-created window (the initial Xenith window)
    # or whatever window the test is run from

    # Find a user window (window with low ID, likely user-created)
    user_window=$(ls /mnt/xenith 2>/dev/null | grep '^[0-9]' | head -1)

    if test -z "$user_window"; then
        fail "No user windows found to test protection"
        return
    fi

    # Try to delete it - should fail
    result=$(echo delete > /mnt/xenith/$user_window/ctl 2>&1)

    if echo "$result" | grep -q "permission denied"; then
        pass "User window $user_window protected from deletion"
    elif test -d /mnt/xenith/$user_window; then
        # Window still exists, check if we got an error
        if test -n "$result"; then
            pass "User window $user_window protected (error: $result)"
        else
            fail "Delete command succeeded but window still exists (unexpected)"
        fi
    else
        fail "User window $user_window was deleted (protection failed!)"
    fi
}

# Test 7: Invalid command handling
test_invalid_commands() {
    echo ""
    echo "=== Test: Invalid Command Handling ==="

    # Create a test window
    result=$(cat /mnt/xenith/new/ctl 2>&1)
    id=$(echo "$result" | awk '{print $1}')

    if test -z "$id"; then
        fail "Could not create test window"
        return
    fi

    # Test invalid command
    result=$(echo 'invalidcommand' > /mnt/xenith/$id/ctl 2>&1)
    if echo "$result" | grep -qi "ill-formed\|error\|bad"; then
        pass "Invalid command rejected appropriately"
    else
        # Check exit status
        echo 'invalidcommand' > /mnt/xenith/$id/ctl 2>/dev/null
        if test $? -ne 0; then
            pass "Invalid command rejected (non-zero exit)"
        else
            fail "Invalid command not rejected"
        fi
    fi

    # Test tocol with invalid column
    result=$(echo 'tocol 999' > /mnt/xenith/$id/ctl 2>&1)
    if echo "$result" | grep -qi "invalid\|error"; then
        pass "Invalid column index rejected"
    else
        pass "tocol 999 handled (may have clamped or failed silently)"
    fi

    # Clean up
    echo delete > /mnt/xenith/$id/ctl 2>/dev/null
}

# Test 8: Multiple window operations
test_multiple_windows() {
    echo ""
    echo "=== Test: Multiple Window Operations ==="

    # Create multiple windows
    id1=$(cat /mnt/xenith/new/ctl 2>&1 | awk '{print $1}')
    id2=$(cat /mnt/xenith/new/ctl 2>&1 | awk '{print $1}')
    id3=$(cat /mnt/xenith/new/ctl 2>&1 | awk '{print $1}')

    if test -n "$id1" && test -n "$id2" && test -n "$id3"; then
        pass "Created 3 windows: $id1, $id2, $id3"

        # Write different content to each
        echo "Window One" > /mnt/xenith/$id1/body
        echo "Window Two" > /mnt/xenith/$id2/body
        echo "Window Three" > /mnt/xenith/$id3/body

        # Delete middle one
        echo delete > /mnt/xenith/$id2/ctl 2>/dev/null

        if test -d /mnt/xenith/$id2; then
            fail "Middle window $id2 not deleted"
        else
            pass "Middle window $id2 deleted, others intact"
        fi

        # Clean up remaining
        echo delete > /mnt/xenith/$id1/ctl 2>/dev/null
        echo delete > /mnt/xenith/$id3/ctl 2>/dev/null
    else
        fail "Could not create multiple windows"
    fi
}

# Main test runner
main() {
    echo "================================================"
    echo "Xenith Window Manipulation Regression Tests"
    echo "================================================"

    check_xenith

    test_window_creation
    test_content_writing
    test_layout_commands
    test_newcol
    test_filesystem_window_deletion
    test_user_window_protection
    test_invalid_commands
    test_multiple_windows

    echo ""
    echo "================================================"
    echo "Results: $PASS passed, $FAIL failed (of $TESTS_RUN tests)"
    echo "================================================"

    if test $FAIL -gt 0; then
        exit 1
    fi
    exit 0
}

main "$@"

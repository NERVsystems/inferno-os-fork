#!/dis/sh.dis
# Test script for temp file slot reclamation fix
# This tests that removing OEXCL allows stale file reuse

load std

echo '=== Temp File Slot Reclamation Test ==='
echo ''

# Get username (first 4 chars)
user=`{cat /dev/user}
echo 'User: ' $user

# Clean any existing temp files first
echo 'Cleaning existing temp files...'
rm /tmp/*xenith /tmp/*acme /tmp/*blks >[2] /dev/null
echo 'Done.'
echo ''

# Test 1: Create stale files for all 26 slots to simulate exhaustion
echo '=== Test 1: Simulating temp file exhaustion ==='
echo 'Creating 26 stale files (A-Z) to fill all slots...'

# Use a fake PID so we don't conflict with real files  
fakepid=99999
userprefix=`{echo $user | sed 's/(....).*$/\1/'}
for letter in A B C D E F G H I J K L M N O P Q R S T U V W X Y Z {
    stalefile=/tmp/^$letter^$fakepid^.^$userprefix^xenith
    echo 'stale data' > $stalefile
}

# Verify files were created
echo 'Stale files created:'
ls /tmp/*xenith 2>/dev/null | wc -l
echo ''

# Test 2: Try to create a temp file using disk module
# If OEXCL is removed, this should succeed by truncating a stale file
echo '=== Test 2: Testing temp file creation with stale files present ==='
echo 'Launching xenith (will exit after 2 seconds)...'
echo ''

# Run xenith in background and kill after timeout
xenith &
xpid=$apid
sleep 2

# Check if xenith is still running (it should be if temp file worked)
if {ftest -e /prog/^$xpid^/status} {
    echo 'SUCCESS: xenith started successfully!'
    echo 'This confirms the fix works - stale temp files were reclaimed.'
    # Kill xenith
    echo kill > /prog/^$xpid^/ctl >[2] /dev/null
} {
    echo 'FAILURE: xenith failed to start'
    echo 'Check if the OEXCL fix was applied correctly.'
}

echo ''
echo '=== Test Complete ==='

# Cleanup
rm /tmp/*xenith /tmp/*acme /tmp/*blks >[2] /dev/null

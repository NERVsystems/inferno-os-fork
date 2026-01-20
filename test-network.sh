#!/bin/bash
# TCP/IP Network Stack Tests for ARM64 Inferno

echo "=========================================="
echo "TCP/IP Network Stack Tests"
echo "=========================================="
echo ""

cd "$(dirname "$0")"

echo "Test 1: Check network devices exist"
./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -20
ls /net
ls /net/tcp
EOF

echo ""
echo "Test 2: Can we allocate a TCP connection?"
./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -10
cat /net/tcp/clone
EOF

echo ""
echo "Test 3: Can we listen on a port?"
timeout 5 ./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -20
listen -A tcp!*!19999 {echo "connection received"} &
sleep 2
cat /net/tcp/*/local
EOF

echo ""
echo "Test 4: Can we dial an external host (google.com)?"
timeout 10 ./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -30
dial tcp!google.com!80 /tmp/conn
if {ftest -f /tmp/conn} {
    echo "Connection succeeded!"
    cat /tmp/conn
} {
    echo "Connection failed"
}
EOF

echo ""
echo "Test 5: Can we make HTTP request?"
timeout 10 ./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -40
{
    echo 'GET / HTTP/1.0'
    echo 'Host: example.com'
    echo ''
} | dial -A tcp!example.com!80
EOF

echo ""
echo "Test 6: Can we export a filesystem via 9P?"
timeout 5 ./emu/MacOSX/o.emu -r. <<'EOF' 2>&1 | grep -v DEBUG | head -20
listen -A tcp!*!19999 {export /dis} &
sleep 2
ps | grep export
EOF

echo ""
echo "=========================================="
echo "Network Tests Complete"
echo "=========================================="

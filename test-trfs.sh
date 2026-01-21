#!/bin/bash
timeout 15 ./emu/MacOSX/o.emu -r. -c0 <<'EOF'
mount -ac {mntgen} /n &
sleep 2
ps
trfs '#U*' /n/test1 &
sleep 2
ls /n/test1
exit
EOF

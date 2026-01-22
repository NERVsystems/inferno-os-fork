# Makefile exists for snap
#
ROOT=/home/pi/github/infernode
objtype=arm

all: utils/mk/mk
	./utils/mk/mk install

mk: makemk.sh
	./makemk.sh

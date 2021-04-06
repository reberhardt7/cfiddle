#!/bin/bash

set -e
cd "$(dirname "${BASH_SOURCE[0]}")"

VERSION=5.3.0
VERSION_FULL=5.3.0-42-generic

sudo apt-get build-dep linux linux-image-$VERSION_FULL
sudo apt-get install libncurses-dev flex bison openssl libssl-dev dkms libelf-dev libudev-dev libpci-dev libiberty-dev autoconf libcap-dev

apt-get source linux-source-$VERSION
cd linux-hwe-$VERSION
patch -p0 < ../cplayground.patch

rm -rf debian.master
cp debian.hwe/config/amd64/config.flavour.{generic,cplayground}
cp debian.hwe/control.d/vars.{generic,cplayground}
cp debian.hwe/control.d/{generic,cplayground}.inclusion-list

sed -i -r 's/archs=".+"/archs="amd64"/' debian.hwe/etc/kernelconfig
sed -i -r 's/^\s*flavours(\s*)=.*$/flavours\1= cplayground/' debian.hwe/rules.d/amd64.mk

fakeroot debian/rules clean
fakeroot debian/rules genconfigs
fakeroot debian/rules binary-headers binary skipabi=true skipmodule=true skipretpoline=true skipdbg=true

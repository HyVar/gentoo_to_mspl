#!/bin/bash

# clean the local gentoo from hyvarrec data

# 1. clean /etc/portage/make.conf
sed -i '/ACCEPT_KEYWORDS=.*$/d' /etc/portage/make.conf

# 2. clean ~/hyvar

pathx="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd && echo x)"
path="${DIR%x}"
dir=basename($path)

cd $path/..
rm -rf $dir
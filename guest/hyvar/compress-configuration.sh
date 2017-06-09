#!/bin/bash


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd && echo x)"
DIR="${DIR%x}"

cd ${DIR}

[ -d gen ] || mkdir gen

# LOAD DIRECT INFORMATION

cp /var/lib/portage/world gen/world

./list-gentoo-packages.sh &> gen/configuration


# LOAD PORTAGE CONFIGURATION: USE AND PROFILE

# need python2.7
eselect python set python2.7
python ./load_profile.py

# COMPRESS EVERYTHING

cd gen

tar cvfj configuration.tar.bz2 world configuration profile.json


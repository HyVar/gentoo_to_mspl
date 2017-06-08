#!/bin/bash


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd && echo x)"
DIR="${DIR%x}"

cd ${DIR}

[ -d gen ] || mkdir gen

# LOAD DIRECT INFORMATION

# world
gzip -c /var/lib/portage/world > gen/world.gz

# configuration
./list-gentoo-packages.sh &> /tmp/configuration
gzip -c /tmp/configuration > gen/configuration.gz


# LOAD PORTAGE CONFIGURATION: USE AND PROFILE

python ./load_profile.py
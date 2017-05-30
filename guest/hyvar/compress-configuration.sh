#!/bin/bash

cd /home/osboxes/hyvar

[ -d gen ] || mkdir gen

# world
gzip -c /var/lib/portage/world > gen/world.gz

# configuration
./list-gentoo-packages.sh &> /tmp/configuration
gzip -c /tmp/configuration > gen/configuration.gz

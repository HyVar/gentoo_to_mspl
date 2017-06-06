#!/bin/bash
# get the configuration from the guest VM

FILES=''
DIRS=''

FILES=$FILES' host/configuration/json/configuration.json'
FILES=$FILES' host/configuration/json/new_configuration.json'
FILES=$FILES' host/configuration/json/world.json'
FILES=$FILES' host/configuration/configuration.gz'
FILES=$FILES' host/configuration/package.use'
FILES=$FILES' host/configuration/update.sh'
FILES=$FILES' host/configuration/world.gz'
FILES=$FILES' host/portage/portage.tar.bz2'

DIRS=$DIRS' host/portage/json/catalog'
DIRS=$DIRS' host/portage/json/hyvarrec'
DIRS=$DIRS' host/portage/json/mspl'
DIRS=$DIRS' host/portage/gen'

for i in $FILES
do
	[ -e $i ] && rm $i
done

for i in $DIRS
do
	[ -d $i ] && rm -r $i
done

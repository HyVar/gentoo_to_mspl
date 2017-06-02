#!/bin/bash


cd /home/osboxes/hyvar

[ -d gen ] || mkdir gen

# get the deprecated files
mkdir -p /tmp/deprecated
for path in $(find /var/db/pkg -name "*.ebuild"); do
  path=${path#/var/db/pkg}
  CATEGORY=${path%%*/}
  FILE=${path#*/}
  TEST=${FILE##*-}
  PACKAGE=${FILE%*-}
  if [ ${TEST: -1} = "r" ]; then
  	PACKAGE=${PACKAGE%*-}
  fi
  PACKAGE=/tmp/deprecated/${PACKAGE}
  mkdir -p ${PACKAGE}
  cp ${path} ${PACKAGE} 
done
egencache --update --repo deprecated


tar cvfj gen/portage.tar.bz2 /usr/portage/metadata/md5-cache /tmp/deprecated/metadata/md5-cache

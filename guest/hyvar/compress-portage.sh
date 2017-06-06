#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd && echo x)"
DIR="${DIR%x}"

cd ${DIR}

[ -d gen ] || mkdir gen


function manage_portage {
  cp -R /usr/portage/metadata/md5-cache gen/  
}


function manage_deprecated { # not working as well as expected
  # create the base structure of the deprecated repos
  [ -e /tmp/deprecated ] && rm -rf /tmp/deprecated
  mkdir -p /tmp/deprecated/metadata
  echo "masters = gentoo" >> /tmp/deprecated/metadata/layout.conf

  # get the deprecated files

  for path in $(find /var/db/pkg -name "*.ebuild"); do
    local_path=${path#/var/db/pkg/}
    if [ -e /usr/portage/${local_path} ]; then # do not copy files that already exist
      continue
    fi
    CATEGORY=${local_path%%/*}
    FILE=${local_path##*/}
    TEST=${FILE##*-}
    PACKAGE_GROUP=${FILE%-*}
    if [ ${TEST:0:1} = "r" ]; then
  	  PACKAGE_GROUP=${PACKAGE_GROUP%-*}
    fi
    directory=/tmp/deprecated/${CATEGORY}/${PACKAGE_GROUP}
    new_path=${directory}/${FILE}

    mkdir -p ${directory}
    cp ${path} ${new_path}
    perl -i -00pe 's{\s*SRC_URI="[^"]*"}{}g' -- ${new_path} # do not download the implementation
    cd ${directory}
    ebuild ${FILE} manifest
  done
  egencache --update --repo deprecated
  cp -R /tmp/deprecated/metadata/md5-cache gen/
}

manage_portage
#manage_deprecated

tar cvfj gen/portage.tar.bz2 gen/md5-cache

#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd && echo x)"
DIR="${DIR%x}"

cd ${DIR}

[ -d gen ] || mkdir gen


function manage_portage {
  cp -R /usr/portage/metadata/md5-cache gen/  
}


function manage_deprecated {
  # get the deprecated files
  for path in $(find /var/db/pkg -name "*.ebuild"); do
    TMP=${path#/var/db/pkg/}
    CATEGORY=${TMP%%/*}
    FILE=${TMP##*/}
    new_path="gen/md5-cache/${CATEGORY}/${FILE%.ebuild}"

    if [ ! -e "${new_path}" ]; then # do not copy files that already exist
      echo "adding deprecated ebuild: ${path}"
      bash load_deprecated_ebuild.sh "${path}" "${new_path}" 2> /dev/null # no warning reporting
    fi
  done
}

manage_portage
manage_deprecated

tar cvfj gen/portage.tar.bz2 gen/md5-cache

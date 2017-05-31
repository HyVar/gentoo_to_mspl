#!/bin/bash

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org

 ssh -p ${PORT} -o PubkeyAuthentication=no ${HOST} 'echo ${PSWD} | sudo -S ~/hyvar/compress-portage.sh'
 scp -o PubkeyAuthentication=no -P ${PORT}  ${HOST}:/home/osboxes/hyvar/gen/portage.tar.bz2 host/portage
 cd host
 ./uncompress-portage.sh
 ./portage2hyvarrec.sh --no_opt
fi


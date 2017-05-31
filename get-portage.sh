#!/bin/bash

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org
 PSWD_USER=osboxes.org

 if [ -e host/portage/portage.tar.bz2 ]; then
  exit
 fi

 sshpass -p $PSWD_USER ssh -p ${PORT} -o PubkeyAuthentication=no ${HOST} "echo ${PSWD} | sudo -S sh ~/hyvar/compress-portage.sh"
 sshpass -p $PSWD_USER scp -o PubkeyAuthentication=no -P ${PORT}  ${HOST}:/home/osboxes/hyvar/gen/portage.tar.bz2 host/portage
 cd host
 sh uncompress-portage.sh
 sh portage2hyvarrec.sh
fi


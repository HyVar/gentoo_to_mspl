#!/bin/bash

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org

 ssh -o PubkeyAuthentication=no -p ${PORT} ${HOST} 'echo ${PSWD} | sudo -S -- sh -c "[ -e /etc/portage/package.use ] && rm -rf /etc/portage/package.use"'
 scp -o PubkeyAuthentication=no -P ${PORT} host/configuration/package.use host/configuration/update.sh ${HOST}:
 ssh -o PubkeyAuthentication=no -p ${PORT} ${HOST} 'echo ${PSWD} | sudo -S mv ~/package.use /etc/portage/'
 ssh -o PubkeyAuthentication=no -p ${PORT} ${HOST} 'echo ${PSWD} | sudo -S sh update.sh'

fi
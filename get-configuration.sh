#!/bin/bash
# get the configuration from the guest VM

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org
 PSWD_USER=osboxes.org

 sshpass -p $PSWD_USER ssh -p ${PORT} -o PubkeyAuthentication=no ${HOST} "echo ${PSWD} | sudo -S sh ~/hyvar/compress-configuration.sh"
 sshpass -p $PSWD_USER scp -o PubkeyAuthentication=no -P ${PORT}  ${HOST}:/home/osboxes/hyvar/gen/world.gz host/configuration
 sshpass -p $PSWD_USER scp -o PubkeyAuthentication=no -P ${PORT}  ${HOST}:/home/osboxes/hyvar/gen/configuration.gz host/configuration
 cd host
 sh uncompress-configuration.sh
fi


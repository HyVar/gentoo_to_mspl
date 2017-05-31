#!/bin/bash

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org

 ssh -p ${PORT} -o PubkeyAuthentication=no ${HOST} 'echo ${PSWD} | sudo -S ~/hyvar/compress-configuration.sh'
 scp -o PubkeyAuthentication=no -P ${PORT}  osboxes@localhost:/home/osboxes/hyvar/gen/world.gz host/configuration
 scp -o PubkeyAuthentication=no -P ${PORT}  osboxes@localhost:/home/osboxes/hyvar/gen/configuration.gz host/configuration
 cd host
 ./uncompress-configuration.sh
fi


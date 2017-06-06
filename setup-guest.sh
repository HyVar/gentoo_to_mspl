#!/bin/bash

if [ -z ${2+x} ]; then
 echo "usage: $0 where-to-connect port";
 exit;
else
 HOST=$1
 PORT=$2
 PSWD=osboxes.org
 PSWD_USER=osboxes.org

 sshpass -p $PSWD_USER ssh -o PubkeyAuthentication=no -p ${PORT} ${HOST} "echo ${PSWD} | sudo -S -- sh -c 'echo ACCEPT_KEYWORDS=\\\"~amd64\\\" >> /etc/portage/make.conf'"
 sshpass -p $PSWD_USER scp -o PubkeyAuthentication=no -P ${PORT}  -r guest/*  ${HOST}:
 sshpass -p $PSWD_USER ssh -o PubkeyAuthentication=no -p ${PORT} ${HOST} "echo ${PSWD} | sudo -S -- mv ~/hyvar/repos.conf /etc/portage/"

fi

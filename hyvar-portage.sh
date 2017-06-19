#!/bin/bash

######################################################################
### CONFIGURATION
######################################################################

GUEST="localhost"
GUEST_PORT="9022"

GUEST_USER="osboxes"
GUEST_PWD_ROOT="osboxes.org"
GUEST_PWD_USER="osboxes.org"

GUEST_SCRIPT_DIRECTORY_NAME="hyvar"


GUEST_INSTALL_DIR="/home/${GUEST_USER}/${GUEST_SCRIPT_DIRECTORY_NAME}"
GUEST_GEN_DIR="${GUEST_INSTALL_DIR}/gen/"

HOST_GUEST_INSTALL_DIR="./guest/${GUEST_SCRIPT_DIRECTORY_NAME}"
HOST_HOST_INSTALL_DIR="./host/hyvar/portage"
HOST_HOST_GEN_DIR="./host/hyvar/gen"

######################################################################
### UTILITY FUNCTIONS
######################################################################

check_environment() {
	if [ ! -e "${HOST_HOST_INSTALL_DIR}" ]; then
		mkdir -p "${HOST_HOST_INSTALL_DIR}"
	fi
	if [ ! -e "${HOST_HOST_GEN_DIR}" ]; then
		mkdir -p "${HOST_HOST_GEN_DIR}"
	fi
}

clean_host() {
	if [ -e "${HOST_HOST_INSTALL_DIR}" ]; then
		rm -rf "${HOST_HOST_INSTALL_DIR}"
	fi
	if [ -e "${HOST_HOST_GEN_DIR}" ]; then
		rm -rf "${HOST_HOST_GEN_DIR}"
	fi	
}

clean_guest() {
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no ${GUEST_USER}@${GUEST} "echo ${GUEST_PWD_ROOT} | sudo -S sh ${GUEST_INSTALL_DIR}/clean.sh ${GUEST_INSTALL_DIR} ${GUEST_GEN_DIR}"

}


######################################################################
### BASE FUNCTIONS
######################################################################


setup_guest() {
	sshpass -p ${GUEST_PWD_USER} scp -o PubkeyAuthentication=no -P ${GUEST_PORT}  -r "${HOST_GUEST_INSTALL_DIR}"  "${GUEST_USER}@${GUEST}:${GUEST_INSTALL_DIR}"
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no "${GUEST_USER}@${GUEST}" "echo ${GUEST_PWD_ROOT} | sudo -S sh ${GUEST_INSTALL_DIR}/setup.sh ${GUEST_GEN_DIR}"
}

sync_guest() {
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no ${GUEST_USER}@${GUEST} "echo ${GUEST_PWD_ROOT} | sudo -S python ${GUEST_INSTALL_DIR}/sync.py ${GUEST_GEN_DIR}"
	sshpass -p ${GUEST_PWD_USER} rsync -rLptgoDz -e "ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no" ${GUEST_USER}@${GUEST}:${GUEST_GEN_DIR} ${HOST_HOST_INSTALL_DIR}
	#sshpass -p ${GUEST_PWD_USER} scp -o PubkeyAuthentication=no -P ${GUEST_PORT}  ${GUEST_USER}@${GUEST}:${GUEST_GEN_DIR} ${HOST_HOST_INSTALL_DIR}
}



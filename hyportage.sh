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


HOST_SCRIPT_DIRECTORY=$(realpath "./host/scripts")
HOST_SCRIPT_TRANSLATE="${HOST_SCRIPT_DIRECTORY}/translate-portage.py"
HOST_SCRIPT_RECONFIGURE="${HOST_SCRIPT_DIRECTORY}/reconfigure.py"

HOST_GUEST_INSTALL_DIR=$(realpath "./guest/${GUEST_SCRIPT_DIRECTORY_NAME}")
HOST_HOST_INSTALL_DIR=$(realpath "./host/data/portage")
HOST_HOST_GEN_DIR=$(realpath "./host/data/hyvar")



######################################################################
### BASE FUNCTIONS
######################################################################

function print_usage {
	echo "${0} action [options] ..."
	echo "  valid actions:"
	echo "   setup_guest   install files on the guest machine"
	echo "   sync_guest    upload portage files from guest"
	echo "   clean_guest   remove all installed files from guest"
	echo "   setup_host    create the directory structure on host"
	echo "   clean_host    remove all generated files from host"
	echo "   translate     translate uploaded portage files into internal representation"
	echo "   emerge        compute valid new configuration with the specified packages installed/removed"
	echo "     valid options:"
	echo "       -v     verbose mode"
	echo "       -p n   uses n parallel processes when possible"
}



function setup_guest {
	sshpass -p ${GUEST_PWD_USER} scp -o PubkeyAuthentication=no -P ${GUEST_PORT}  -r "${HOST_GUEST_INSTALL_DIR}"  "${GUEST_USER}@${GUEST}:${GUEST_INSTALL_DIR}"
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no "${GUEST_USER}@${GUEST}" "echo ${GUEST_PWD_ROOT} | sudo -S sh ${GUEST_INSTALL_DIR}/setup.sh ${GUEST_GEN_DIR}"
}

function sync_guest {
	check_environment
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no ${GUEST_USER}@${GUEST} "echo ${GUEST_PWD_ROOT} | sudo -S python ${GUEST_INSTALL_DIR}/sync.py ${GUEST_GEN_DIR}"
	sshpass -p ${GUEST_PWD_USER} rsync -rLptgoDz -e "ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no" ${GUEST_USER}@${GUEST}:${GUEST_GEN_DIR} ${HOST_HOST_INSTALL_DIR}
	#sshpass -p ${GUEST_PWD_USER} scp -o PubkeyAuthentication=no -P ${GUEST_PORT}  ${GUEST_USER}@${GUEST}:${GUEST_GEN_DIR} ${HOST_HOST_INSTALL_DIR}
}

function clean_guest {
	sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no ${GUEST_USER}@${GUEST} "echo ${GUEST_PWD_ROOT} | sudo -S sh ${GUEST_INSTALL_DIR}/clean.sh ${GUEST_INSTALL_DIR} ${GUEST_GEN_DIR}"

}



function setup_host {
	if [ ! -e "${HOST_HOST_INSTALL_DIR}" ]; then
		mkdir -p "${HOST_HOST_INSTALL_DIR}"
	fi
	if [ ! -e "${HOST_HOST_GEN_DIR}" ]; then
		mkdir -p "${HOST_HOST_GEN_DIR}"
	fi
}

function clean_host {
	if [ -e "${HOST_HOST_INSTALL_DIR}" ]; then
		rm -rf "${HOST_HOST_INSTALL_DIR}"
	fi
	if [ -e "${HOST_HOST_GEN_DIR}" ]; then
		rm -rf "${HOST_HOST_GEN_DIR}"
	fi	
}



function translate {
	shift 1
	python "${HOST_SCRIPT_TRANSLATE}" $@ "${HOST_HOST_INSTALL_DIR}" "${HOST_HOST_GEN_DIR}"
	#python scripts/portage2hyvarrec/gentoo_rec.py "$@" portage/json portage/json/hyvarrec
}

function emerge {
	echo "not implemented yet"
}


######################################################################
### MAIN
######################################################################

if [ -n "${1}" ]; then
	case "${1}" in
		setup_guest)
			setup_guest
			;;
		sync_guest)
			sync_guest
			;;
		clean_guest)
			clean_guest
			;;
		setup_host)
			setup_host
			;;
		clean_host)
			clean_host
			;;
		translate)
			translate
			;;
		*)
			echo "unknown action \"${1}\""
			print_usage
	esac
fi
#!/bin/bash

LOCAL_DIR="$( cd "$(dirname "${BASH_SOURCE[0]}" )" && pwd )"

######################################################################
### CONFIGURATION
######################################################################

# Configures how to connect to the guest VM
GUEST="localhost"
GUEST_PORT="9022"

GUEST_USER="osboxes"
GUEST_PWD_ROOT="osboxes.org"
GUEST_PWD_USER="osboxes.org"


# States where scripts can be found, and where to save data.
# Change only if you know what you are doing
GUEST_SCRIPT_DIRECTORY_NAME="hyvar"

GUEST_INSTALL_DIR="/home/${GUEST_USER}/${GUEST_SCRIPT_DIRECTORY_NAME}"
GUEST_GEN_DIR="${GUEST_INSTALL_DIR}/gen/"


HOST_SCRIPT_DIRECTORY="${LOCAL_DIR}/host/scripts"
HOST_SCRIPT_TRANSLATE="${HOST_SCRIPT_DIRECTORY}/hyportage.py"
HOST_SCRIPT_EMERGE="${HOST_SCRIPT_DIRECTORY}/hyportage.py --mode=emerge"

HOST_GUEST_INSTALL_DIR="${LOCAL_DIR}/guest/${GUEST_SCRIPT_DIRECTORY_NAME}"
HOST_HOST_INSTALL_DIR="${LOCAL_DIR}/host/data/portage"
HOST_HOST_GEN_DIR="${LOCAL_DIR}/host/data/hyportage"

HOST_EMERGE_SCRIPT_DIR="${LOCAL_DIR}/host/data/install"

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
	echo "   reconfigure   trigger the reconfiguration attempt"
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
	if sshpass -p ${GUEST_PWD_USER} ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no ${GUEST_USER}@${GUEST} "echo ${GUEST_PWD_ROOT} | sudo -S python ${GUEST_INSTALL_DIR}/extract_portage.py ${GUEST_GEN_DIR}";
	then
		sshpass -p ${GUEST_PWD_USER} rsync -rLptgoDz -e "ssh -p ${GUEST_PORT} -o PubkeyAuthentication=no" ${GUEST_USER}@${GUEST}:${GUEST_GEN_DIR} ${HOST_HOST_INSTALL_DIR}
	else
		echo "extracting data from portage failed"
	fi
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
	if [ ! -e "${HOST_EMERGE_SCRIPT_DIR}" ]; then
		mkdir -p "${HOST_EMERGE_SCRIPT_DIR}"
	fi
}

function clean_host {
	if [ -e "${HOST_HOST_INSTALL_DIR}" ]; then
		rm -rf "${HOST_HOST_INSTALL_DIR}"
	fi
	if [ -e "${HOST_HOST_GEN_DIR}" ]; then
		rm -rf "${HOST_HOST_GEN_DIR}"
	fi	
	if [ -e "${HOST_EMERGE_SCRIPT_DIR}" ]; then
		rm -rf "${HOST_EMERGE_SCRIPT_DIR}"
	fi
}



function translate {
	shift 1
	PYTHONPATH="${HOST_GUEST_INSTALL_DIR}:${PYTHONPATH}" python "${HOST_SCRIPT_TRANSLATE}" "${HOST_HOST_INSTALL_DIR}" "${HOST_HOST_GEN_DIR}" "${HOST_EMERGE_SCRIPT_DIR}" --mode=update $@
}

function reconfigure {
	shift 1
	#export PYTHONPATH="${HOST_GUEST_INSTALL_DIR}":"${PYTHONPATH}"
	PYTHONPATH="${HOST_GUEST_INSTALL_DIR}:${PYTHONPATH}" nice -n 20 python "${HOST_SCRIPT_EMERGE}" "${HOST_SCRIPT_TRANSLATE}" "${HOST_HOST_INSTALL_DIR}" "${HOST_HOST_GEN_DIR}" "${HOST_EMERGE_SCRIPT_DIR}" --mode=emerge $@
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
			translate "$@"
			;;
		reconfigure)
			reconfigure "$@"
			;;
		*)
			echo "unknown action \"${1}\""
			print_usage
	esac
fi

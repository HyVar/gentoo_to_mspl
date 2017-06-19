#!/bin/bash

# clean the local gentoo from hyvarrec data

GUEST_INSTALL_DIR="${1}"
GUEST_GEN_DIR="${2}"

[ -e ${GUEST_INSTALL_DIR} ] && rm -rf ${GUEST_INSTALL_DIR}
[ -e ${GUEST_GEN_DIR} ] && rm -rf ${GUEST_GEN_DIR}\"


#!/bin/bash


# in parameter, we have the
# 1. the ebuild file to analyse
# 2. the output file name
# we perform no control on how this script is used, as it should not be called directly



#####################################
# utility functions
#####################################


set_portage_vars() {
  PORTAGE_ECLASS_LOCATIONS="/usr/portage"
  PORTAGE_REPO_NAME="portage"

  BUILD_DIR="/var/tmp/portage"

  IMPLEMENTATION_DIR="/usr/lib/portage"
  PORTAGE_BIN_PATH="${IMPLEMENTATION_DIR}/python2.7"   # where all the .sh files are defined
  #PORTAGE_PYM_PATH="${IMPLEMENTATION_DIR}/pym"   # where all the .py files are defined
  PORTAGE_PYM_PATH="/usr/lib/python2.7"   # location changed in the osboxes VM

  EPREFIX="" # portage/pym/portage/const.py

  PORTAGE_BUILDDIR=${BUILD_DIR}
  PORTAGE_TMPDIR=${BUILD_DIR}

  WORKDIR="${PORTAGE_BUILDDIR}/work"    #Path to the ebuild's root build directory. For example: "${PORTAGE_BUILDDIR}/work".
  T="${PORTAGE_BUILDDIR}/temp"          #Path to a temporary directory which may be used by the ebuild. For example: "${PORTAGE_BUILDDIR}/temp".
  D="${PORTAGE_BUILDDIR}/image"         #Path to the temporary install directory. For example: "${PORTAGE_BUILDDIR}/image".
  HOME="${PORTAGE_BUILDDIR}/homedir"    #Path to a temporary directory for use by any programs invoked by an ebuild that may read or modify the home directory. For example: "${PORTAGE_BUILDDIR}/homedir".

  BUILD_PREFIX="${PORTAGE_TMPDIR}/portage"
  PKG_TMPDIR="${BUILD_PREFIX}/._unmerge_"
}


open_log() {
  # Open the file in parameter for the log of emerge
  exec 4<>"$1"
  PORTAGE_PIPE_FD=4
}

# setting the base ebuild variables
set_ebuild_vars() {
  local_path=${EBUILD#/var/db/pkg/}

  CATEGORY="${local_path%%/*}"
  FILE="${local_path##*/}"
  TEST="${FILE##*-}" # revision or version
  TMP="${FILE%-*}"
  # setup the different variables
  PVR=${FILE%.ebuild}
  if [ "${TEST:0:1}" = "r" ]; then
    PR="${TEST}"
    PN="${TMP%-*}"
    PV="${TMP##*-}"
  else
    PR="r0"
    PN="${TMP}"
    PV="${TEST}"
  fi
  P="${PN}-${PV}"

  EBUILD_FOLDER=${EBUILD%/*}
  PORTDIR=${EBUILD_FOLDER%/*}
  PORTDIR=${PORTDIR%/*}

  FILESDIR="${PORTDIR}/${CATEGORY}/${PN}/files"    #Path to the ebuild's files/ directory, commonly used for small patches and files. For example: "${PORTDIR}/${CATEGORY}/${PN}/files".

  EAPI=6 # test, I guess it is safe to assume here that only use EAPI 2 (we just analyse dependencies here)
}


sanitize_string() {
  STRING=$(echo "${1}" | tr '\t\r\n' ' ')
}



debug() {
  echo "P        = ${P}               #Package name and version (excluding revision, if any), for example vim-6.3."
  echo "PN       = ${PN}              #Package name, for example vim."
  echo "PV       = ${PV}              #Package version (excluding revision, if any), for example 6.3. It should reflect the upstream versioning scheme."
  echo "PR       = ${PR}              #Package revision, or r0 if no revision exists."
  echo "PVR      = ${PVR}             #Package version and revision (if any), for example 6.3, 6.3-r1."
  echo "PF       = ${PF}              #Full package name, \${PN}-\${PVR}, for example vim-6.3-r1."
  echo "A        = ${A}               #All the source files for the package (excluding those which are not available because of USE flags)."
  echo "CATEGORY = ${CATEGORY}        #Package's category, for example app-editors."
  echo "FILESDIR = ${FILESDIR}        #Path to the ebuild's files/ directory, commonly used for small patches and files. For example: \"\${PORTDIR}/\${CATEGORY}/\${PN}/files\"."
  echo "WORKDIR  = ${WORKDIR}         #Path to the ebuild's root build directory. For example: \"\${PORTAGE_BUILDDIR}/work\"."
  echo "T        = ${T}               #Path to a temporary directory which may be used by the ebuild. For example: \"\${PORTAGE_BUILDDIR}/temp\"."
  echo "D        = ${D}               #Path to the temporary install directory. For example: \"\${PORTAGE_BUILDDIR}/image\"."
  echo "HOME     = ${HOME}            #Path to a temporary directory for use by any programs invoked by an ebuild that may read or modify the home directory. For example: \"\${PORTAGE_BUILDDIR}/homedir\"."
  echo "ROOT     = ${ROOT}            #The absolute path to the root directory into which the package is to be merged. Only allowed in pkg_* phases. See ROOT"
  echo "DISTDIR  = ${DISTDIR}         #Contains the path to the directory where all the files fetched for the package are stored."
  echo "EPREFIX  = ${EPREFIX}         #The normalised offset-prefix path of an offset installation."
  echo "ED       = ${ED}              #Shorthand for \${D%/}\${EPREFIX}/."
  echo "EROOT    = ${EROOT}           #Shorthand for \${ROOT%/}\${EPREFIX}/." 
}


# copy-paste of get_libdir function to make things work
get_libdir() {
  local CONF_LIBDIR
  if [ -n  "${CONF_LIBDIR_OVERRIDE}" ] ; then
    # if there is an override, we want to use that... always.
    echo ${CONF_LIBDIR_OVERRIDE}
  else
    get_abi_LIBDIR
  fi
}


#####################################
# extract the information
#####################################

EBUILD=$(readlink -f "${1}")
OUTPUT=$(readlink -f "${2}")

# reset the parameters so not to trigger any ebuild operation
set --

set_portage_vars
set_ebuild_vars

open_log "/dev/null"

source "${PORTAGE_BIN_PATH}/ebuild.sh"


#####################################
# print
#####################################

[ -e ${OUTPUT} ] && rm -rf ${OUTPUT}
mkdir -p $(dirname ${OUTPUT})

if [ -n "${DEPEND}" ]; then
  sanitize_string "${DEPEND}"
  echo "DEPEND=${STRING}" >> "${OUTPUT}"
fi

if [ -n "${IUSE}" ]; then
  sanitize_string "${IUSE}"
  echo "IUSE=${STRING}" >> "${OUTPUT}"
fi

if [ -n "${DEPEND}" ]; then
  sanitize_string "${KEYWORDS}"
  echo "KEYWORDS=${STRING}" >> "${OUTPUT}"
fi

if [ -n "${RDEPEND}" ]; then
  sanitize_string "${RDEPEND}"
  echo "RDEPEND=${STRING}" >> "${OUTPUT}"
fi

if [ -n "${SLOT}" ]; then
  sanitize_string "${SLOT}"
  echo "SLOT=${STRING}" >> "${OUTPUT}"
fi

if [ -n "${REQUIRED_USE}" ]; then
  sanitize_string "${REQUIRED_USE}"
  echo "REQUIRED_USE=${STRING}" >> "${OUTPUT}"
fi

#!/bin/bash

# this file loads a make.defaults or make.conf file (following the portage specification),
#  expands the IUSE and USE variables, and outputs the bash variable environment


######################################################################
# 1. LOADS THE MAKE.CONF / MAKE.DEFAULTS FILE
######################################################################

if [ -n "${1}" ]; then
	#echo "Loading ${1}" >> log.txt
	source ${1}
fi


######################################################################
# 2. UTILITY FUNCTIONS
######################################################################

# classic iter implementation in bash
iter() {
	local FUNCTION=$1
	local LIST=$2
	shift 2
	for i in ${LIST}; do
		${FUNCTION} "${i}" $@
	done
}

# expand a list variable into its content, and iterate a function on it
expand_list() {
	local LIST_NAME="$1"
	local FUNCTION="$2"
	shift 2
	eval local LIST="\$${LIST_NAME}"
	#echo "${LIST_NAME}=${LIST}"
	iter ${FUNCTION} "${LIST}" $@
}


# check if a string is in a list
contains() {
	LIST=$1
	EL=$2
	[[ ${LIST} =~ (^|[[:space:]])"${EL}"($|[[:space:]]) ]] && return 0 || return 1
}


# add element to list
extends() {
	LIST_NAME="$1"
	EL="$2"
	echo "add \"${EL}\" to the list \"${LIST_NAME}\""
	eval LIST="\$${LIST_NAME}"
	if [ -n "${LIST}" ]; then
		eval ${LIST_NAME}="'${LIST} ${EL}'"
	else
		eval ${LIST_NAME}="'${EL}'"
	fi
}


# extract the "-" sign if present from a variable
extract_sign() {
	local SIGNED_LIST_NAME="$1"
	local SIGN_NAME="$2"
	local LIST_NAME="$3"
	if [ ${SIGNED_LIST_NAME:0:1} == "-" ]; then
		eval ${SIGN_NAME}="-"
		eval ${LIST_NAME}="'${SIGNED_LIST_NAME:1}'"
	else
		eval ${SIGN_NAME}=""
		eval ${LIST_NAME}="'${SIGNED_LIST_NAME}'"
	fi
}


# function that declares the parameter as a use flag
declare_use_flag() {
	extends IUSE "$1"
}

# function to add the parameter in the use flag selection
select_use_flag() {
	extends USE "$1"
}

# function that adds a variable to the set of profile-only variables
set_as_profile_only() {
	extends FLAT_PROFILE_ONLY_VARIABLES "$1"
}

######################################################################
# 3. FUNCTIONS TO MANAGE THE VARIABLE EXPANSION
######################################################################


######################################################################
# 3.1. USE FLAG DECLARATION

# declares the use flags in any IUSE list variable
manage_iuse_list() {
	echo "manage list ${1} with function ${2}"
	iter "$2" "$1"
}

# declare the use flags in the USE_EXPAND_IMPLICIT
# note that these use flags may be or may not be prefixed depending if the containing variable is in USE_EXPAND OR USE_EXPAND_UNPREFIXED
manage_use_expand_implicit_get_prefix_from_variable() {
	$(contains "${USE_EXPAND}" "$1") && PREFIX="${1,,}_" || PREFIX=""
}

manage_use_expand_implicit_inner() {
	local LIST_NAME="$1"
	local FUNCTION="$2"
	manage_use_expand_implicit_get_prefix_from_variable "${LIST_NAME}"
	eval LIST="\$${LIST_NAME}"
	#echo "${LIST_NAME}=${LIST}"
	printf -v LIST "${PREFIX}%s" ${LIST}
	iter "${FUNCTION}" "${LIST}"
}

manage_use_expand_implicit() {
	iter manage_use_expand_implicit_inner
}

######################################################################
# 3.2. USE FLAG SELECTION

manage_use_expand_inner() {
	local SIGNED_LIST_NAME="$1"
	local FUNCTION="$2"
	extract_sign "${SIGNED_LIST_NAME}" "LOCAL_SIGN" "LOCAL_LIST_NAME"
	local PREFIX="${LOCAL_LIST_NAME,,}_"
	eval local LIST="\$${LOCAL_LIST_NAME}"
	[ -n "${LIST}" ] && printf -v LIST "${LOCAL_SIGN}${PREFIX}%s " ${LIST}
	#echo "${SIGNED_LIST_NAME}=${LIST}"
	iter "${FUNCTION}" "${LIST}"
}


manage_use_expand_unprefixed_inner() {
	local SIGNED_LIST_NAME="$1"
	local FUNCTION="$2"
	extract_sign "${SIGNED_LIST_NAME}" "LOCAL_SIGN" "LOCAL_LIST_NAME"
	eval local LIST="\$${LOCAL_LIST_NAME}"
	[ -n "${LIST}" ] && printf -v LIST "${LOCAL_SIGN}%s " ${LIST}
	#echo "${SIGNED_LIST_NAME}=${LIST}"
	iter "${FUNCTION}" "${LIST}"
}


######################################################################
# 3.2. USE FLAG HIDING

manage_profile_only_variables_inner() { # does not expand USE_EXPAND_IMPLICIT correctly
	#echo "LIST_NAME=$1"
	if contains "${USE_DECLARATION_EXPAND}" "$1"; then
		expand_list "$1" manage_use_expand_implicit_inner set_as_profile_only
	else
		expand_list "$1" set_as_profile_only
	fi
}



######################################################################
# 4. MAIN
######################################################################


######################################################################
# 4.1. CONFIGURE THE VARIABLE SEMANTICS

USE_DECLARATION_DIRECT="IUSE_IMPLICIT USE_EXPAND_VALUES_ARCH USE_EXPAND_VALUES_ELIBC USE_EXPAND_VALUES_KERNEL USE_EXPAND_VALUES_USERLAND"
USE_DECLARATION_EXPAND="USE_EXPAND_IMPLICIT"

USE_DECLARATION_HIDDEN_FROM_USER="PROFILE_ONLY_VARIABLES"

USE_SELECTION_EXPAND_WITH_PREFIX="USE_EXPAND"
USE_SELECTION_EXPAND_WITHOUT_PREFIX="USE_EXPAND_UNPREFIXED"


######################################################################
# 4.2. EXPANDS THE VARIABLES


iter expand_list "${USE_DECLARATION_DIRECT}" declare_use_flag # works
iter expand_list "${USE_DECLARATION_EXPAND}" manage_use_expand_implicit_inner declare_use_flag # works

iter expand_list "${USE_DECLARATION_HIDDEN_FROM_USER}" manage_profile_only_variables_inner

iter expand_list "${USE_SELECTION_EXPAND_WITH_PREFIX}" manage_use_expand_inner select_use_flag
iter expand_list "${USE_SELECTION_EXPAND_WITHOUT_PREFIX}" manage_use_expand_unprefixed_inner select_use_flag


# display

#echo "IUSE=${IUSE}"
#echo "USE=${USE}"

set -o posix ; set




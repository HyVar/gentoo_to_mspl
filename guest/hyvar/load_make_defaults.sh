#!/bin/bash

# this file loads a make.defaults or make.conf file (following the portage specification),
#  expands the IUSE and USE variables, and outputs the bash variable environment

# This files translates the loading functions in the portage/config.py file
#

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
	return $([[ ${LIST} =~ (^|[[:space:]])("${EL}"|"-${EL}")($|[[:space:]]) ]])
}


# add element to list
extends() {
	LIST_NAME="$2"
	EL="$1"
	#echo "add \"${EL}\" to the list \"${LIST_NAME}\""
	eval LIST="\$${LIST_NAME}"
	if [ -n "${LIST}" ]; then
		eval ${LIST_NAME}="'${LIST} ${EL}'"
	else
		eval ${LIST_NAME}="'${EL}'"
	fi
}


# extract the "-" sign if present from a variable
KEEP_SIGN=true
extract_sign() {
	local SIGNED_LIST_NAME="$1"
	local SIGN_NAME="$2"
	local LIST_NAME="$3"
	eval ${SIGN_NAME}=""
	if [ ${SIGNED_LIST_NAME:0:1} == "-" ]; then
		if ${KEEP_SIGN} ; then
			eval ${SIGN_NAME}="-"
		fi
		eval ${LIST_NAME}="'${SIGNED_LIST_NAME:1}'"
	else
		eval ${LIST_NAME}="'${SIGNED_LIST_NAME}'"
	fi
}


# function that declares the parameter as a use flag
declare_use_flag() {
	extends "$1" IUSE
}

# function to add the parameter in the use flag selection
select_use_flag() {
	extends "$1" USE
}

# function that adds a variable to the set of profile-only variables
set_as_profile_only() {
	extends "$1" FLAT_PROFILE_ONLY_VARIABLES
}

######################################################################
# 3. FUNCTIONS TO MANAGE THE VARIABLE EXPANSION
######################################################################


######################################################################
# 3.1. USE FLAG DECLARATION EXPANSION

# declare the use flags in the USE_EXPAND_IMPLICIT
# note that these use flags may be or may not be prefixed depending if the containing variable is in USE_EXPAND OR USE_EXPAND_UNPREFIXED
manage_use_expand_implicit_inner_list() {
	local LIST_NAME="USE_EXPAND_VALUES_${1}"
	local PREFIX="$2"
	local FUNCTION="$3"
	shift 3
	eval LIST="\$${LIST_NAME}"
	#echo "${LIST_NAME}=${LIST}"
	printf -v LIST " ${PREFIX}%s" ${LIST}
	"${FUNCTION}" "${LIST}" $@

}

manage_use_expand_implicit_el() {
	local LIST_NAME="$1"
	shift 1

	if contains "${USE_EXPAND}" "${LIST_NAME}"; then
		manage_use_expand_implicit_inner_list "${LIST_NAME}" "${LIST_NAME,,}_" $@
	fi
	if contains "${USE_EXPAND_UNPREFIXED}" "${LIST_NAME}"; then
		manage_use_expand_implicit_inner_list "${LIST_NAME}" "" $@
	fi
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
	"${FUNCTION}" "${LIST}"
}


manage_use_expand_unprefixed_inner() {
	local SIGNED_LIST_NAME="$1"
	local FUNCTION="$2"
	extract_sign "${SIGNED_LIST_NAME}" "LOCAL_SIGN" "LOCAL_LIST_NAME"
	eval local LIST="\$${LOCAL_LIST_NAME}"
	[ -n "${LIST}" ] && printf -v LIST "${LOCAL_SIGN}%s " ${LIST}
	#echo "${SIGNED_LIST_NAME}=${LIST}"
	"${FUNCTION}" "${LIST}"
}


######################################################################
# 3.2. USE FLAG HIDING

manage_profile_only_variables_el() { # does not expand USE_EXPAND_IMPLICIT correctly
	#echo "LIST_NAME=$1"
	KEEP_SIGN=false
	if [ "$1" == "USE_EXPAND_IMPLICIT" ]; then
		expand_list "$1" manage_use_expand_implicit_el set_as_profile_only
	elif [ "$1" == "USE_EXPAND" ]; then
		expand_list "$1" manage_use_expand_inner set_as_profile_only
	elif [ "$1" == "USE_EXPAND_UNPREFIXED" ]; then
		expand_list "$1" manage_use_expand_unprefixed_inner set_as_profile_only
	else
		expand_list "$1" set_as_profile_only
	fi
	KEEP_SIGN=true
}



######################################################################
# 4. MAIN
######################################################################



######################################################################
# 4.1. USE flag declaration


# FOR EAPI <= 4

IUSE_EAPI_4="${IUSE}"

# flags derived from ARCH
IUSE_EAPI_4="${IUSE_EAPI_4} ${ARCH} ${PORTAGE_ARCHLIST}"

# flags from variable expansion
for LIST_NAME in ${USE_EXPAND_HIDDEN}; do
	extract_sign "${LIST_NAME}" "SIGN" "LIST_NAME"
	expand_list "${LIST_NAME}" extends "IUSE_EAPI_5" # works
done



# FOR EAPI >= 5

IUSE_EAPI_5="${IUSE}"

# the IUSE_IMPLICIT variable is a simple list of USE flags to declare
extends "${IUSE_IMPLICIT}" "IUSE_EAPI_5" # works

# the USE_EXPAND_IMPLICIT expands USE_EXPAND_VALUES_* variables that are listed in the USE_EXPAND and USE_EXPAND_UNPREFIXED variables
iter manage_use_expand_implicit_el "${USE_EXPAND_IMPLICIT}" extends "IUSE_EAPI_5" # works

# the PROFILE_ONLY_VARIABLES lists the variables that expand into lists of USE flags that cannot be configured by the user
iter manage_profile_only_variables_el "${PROFILE_ONLY_VARIABLES}"


######################################################################
# 4.2. USE flag selection

iter manage_use_expand_inner "${USE_EXPAND}"  select_use_flag
iter manage_use_expand_unprefixed_inner "${USE_EXPAND_UNPREFIXED}"  select_use_flag


# display

#echo "IUSE=${IUSE}"
#echo "USE=${USE}"

set -o posix ; set




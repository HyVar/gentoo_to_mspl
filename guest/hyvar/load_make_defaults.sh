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
	FUNCTION=$1
	LIST=$2
	if [ -n "${LIST}" ]; then
		for i in ${LIST}; do
			${FUNCTION} ${i}
		done
	fi
}


# extract the "-" sign if present from a variable
extract_sign() {
	VAR=$1
	if [ ${i:0:1} == "-" ]; then
		SIGN="-"
		VARIABLE=${i:1}
	else
		SIGN=""
		VARIABLE=${i}
	fi
}


# check if a string is in a list
contains() {
	LIST=$1
	EL=$2
	[[ $LIST =~ (^|[[:space:]])"$EL"($|[[:space:]]) ]] && return 0 || return 1
}


# function that declares the parameter as a use flag
declare_use_flag() {
	#echo "declaring $1" >> log.txt
	if [ -n "${IUSE}" ]; then
		IUSE="${IUSE} $1"
	else
		IUSE="$1"
	fi
}

# function to add the parameter in the use flag selection
select_use_flag() {
	#echo "selecting $1" >> log.txt
	if [ -n "${USE}" ]; then
		USE="${USE} $1"
	else
		USE="$1"
	fi
}

# function that adds a variable to the set of profile-only variables
set_as_profile_only() {
	#echo "hiding $1" >> log.txt
	if [ -n "${FLAT_PROFILE_ONLY_VARIABLES}" ]; then
		FLAT_PROFILE_ONLY_VARIABLES="${FLAT_PROFILE_ONLY_VARIABLES} $1"
	else
		FLAT_PROFILE_ONLY_VARIABLES="$1"
	fi
}

######################################################################
# 3. FUNCTIONS TO MANAGE THE VARIABLE EXPANSION
######################################################################


######################################################################
# 3.1. USE FLAG DECLARATION

# declares the use flags in any IUSE list variable
manage_iuse_list() {
	for i in "$1"; do
		declare_use_flag "$i"
	done
}

# declare the use flags in the USE_EXPAND_IMPLICIT
# note that these use flags may be or may not be prefixed depending if the containing variable is in USE_EXPAND OR USE_EXPAND_UNPREFIXED
manage_use_expand_implicit_get_prefix_from_variable() {
	if contains "${USE_EXPAND}" "$1"; then
		PREFIX="${1,,}_"
	else
		PREFIX=""
	fi
}
manage_use_expand_implicit_inner() {
	VARIABLE="$1"
	manage_use_expand_implicit_get_prefix_from_variable "${VARIABLE}"
	eval LIST="\$${VARIABLE}"
	for i in ${LIST}; do
		declare_use_flag "${PREFIX}$i"
	done
}


######################################################################
# 3.2. USE FLAG SELECTION

manage_use_expand_inner() {
	SIGNED_VARIABLE="$1"
	extract_sign "${SIGNED_VARIABLE}"
	PREFIX="${VARIABLE,,}_"
	eval LIST="\$${VARIABLE}"
	for i in ${LIST}; do
		select_use_flag "${SIGN}${PREFIX}$i"
	done
}


manage_use_expand_unprefixed_inner() {
	SIGNED_VARIABLE="$1"
	extract_sign "${SIGNED_VARIABLE}"
	eval LIST="\$${VARIABLE}"
	for i in ${LIST}; do
		select_use_flag "${SIGN}$i"
	done
}


######################################################################
# 3.2. USE FLAG HIDING

manage_profile_only_variables() {
	for i in ${1}; do
	    #echo "VARIABLE=$i"
		eval LIST="\$${i}"
		if [ -n "${LIST}" ]; then
			manage_profile_only_variables "${LIST}"
		else
			set_as_profile_only "$i"
		fi
	done
}



######################################################################
# 4. MAIN
######################################################################


# use flag declaration
#echo "IUSE_IMPLICIT=${IUSE_IMPLICIT}"
manage_iuse_list "${IUSE_IMPLICIT}"
manage_iuse_list "${USE_EXPAND_VALUES_ARCH}"
manage_iuse_list "${USE_EXPAND_VALUES_ELIBC}"
manage_iuse_list "${USE_EXPAND_VALUES_KERNEL}"
manage_iuse_list "${USE_EXPAND_VALUES_USERLAND}"

#echo "USE_EXPAND_IMPLICIT=${USE_EXPAND_IMPLICIT}"
iter manage_use_expand_implicit_inner "${USE_EXPAND_IMPLICIT}"

# use flag selection
#echo "USE_EXPAND=${USE_EXPAND}"
iter manage_use_expand_inner "${USE_EXPAND}"

#echo "USE_EXPAND_UNPREFIXED=${USE_EXPAND_UNPREFIXED}"
iter manage_use_expand_unprefixed_inner "${USE_EXPAND_UNPREFIXED}"

#echo "PROFILE_ONLY_VARIABLES=${PROFILE_ONLY_VARIABLES}"
manage_profile_only_variables "${PROFILE_ONLY_VARIABLES}"

# display
set -o posix ; set




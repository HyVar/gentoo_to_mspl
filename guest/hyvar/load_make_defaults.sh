#!/bin/bash

######################################################################
### LOADS THE MAKE.CONF / MAKE.DEFAULTS FILE
######################################################################

source ${1}

# seems to me that the make.defaults must be loaded in sequence, together...

######################################################################
### FUNCTIONS TO MANAGE THE VARIABLE EXPANSION
######################################################################


manage_variable_list() {
	FUNCTION=$1
	LIST=$2
	if [ -n "${LIST}" ]; then
 		for i in ${LIST}; do
	 		if [ ${i:0:1} == "-" ]; then
	 			${FUNCTION} "-" ${i:1}
	 		else
	 			${FUNCTION} "" ${i}
	 		fi
	 	done
	fi
}


EXPANDED_USE=""
EXPANDED_IUSE=""

function_use_expand() { # does not implicitly add use flag to IUSE
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}${VARIABLE,,}_${i}"
	done
}

function_use_expand_implicit() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}${VARIABLE,,}_${i}"
		EXPANDED_IUSE="${EXPANDED_IUSE} ${VARIABLE,,}_${i}"
	done
}

function_use_expand_unprefixed() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}${i}"
	done
}

function_use_expand_values_arch() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}arch_${i}"
		EXPANDED_IUSE="${EXPANDED_IUSE} arch_${i}"
	done
}

function_use_expand_values_elibc() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}elibc_${i}"
		EXPANDED_IUSE="${EXPANDED_IUSE} elibc_${i}"
	done
}

function_use_expand_values_kernel() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}kernel_${i}"
		EXPANDED_IUSE="${EXPANDED_IUSE} kernel_${i}"
	done
}

function_use_expand_values_userland() {
	PREFIX=$1
	VARIABLE=$2
	eval TMP=\$${VARIABLE}
	for i in ${TMP}; do
		EXPANDED_USE="${EXPANDED_USE} ${PREFIX}userland_${i}"
		EXPANDED_IUSE="${EXPANDED_IUSE} userland_${i}"
	done
}


######################################################################
### PERFORM THE VARIABLE EXPANSION
######################################################################

my_test() {
	eval TMP=\$${2}
	echo "$2 = ${TMP}"
}

#TEST0="titi"
#TEST1="toto"
#TEST2="TEST0 TEST1"
#manage_variable_list my_test "${TEST2}"
#manage_variable_list my_test "${USE_EXPAND}"


EXPANDED_IUSE="${IUSE_IMPLICIT}"

manage_variable_list function_use_expand "${USE_EXPAND}"
manage_variable_list function_use_expand_implicit "${USE_EXPAND_IMPLICIT}"
manage_variable_list function_use_expand_unprefixed "${USE_EXPAND_UNPREFIXED}"
manage_variable_list function_use_expand_values_arch "${USE_EXPAND_VALUES_ARCH}"
manage_variable_list function_use_expand_values_elibc "${USE_EXPAND_VALUES_ELIBC}"
manage_variable_list function_use_expand_values_kernel "${USE_EXPAND_VALUES_KERNEL}"
manage_variable_list function_use_expand_values_userland "${USE_EXPAND_VALUES_USERLAND}"

[ -n "${EXPANDED_USE}" ] && USE="${USE} ${EXPANDED_USE}"
[ -n "${EXPANDED_IUSE}" ] && IUSE="${IUSE} ${EXPANDED_IUSE}"

# export the environment, for loading the next make.defaults/make.conf
set -o posix ; set
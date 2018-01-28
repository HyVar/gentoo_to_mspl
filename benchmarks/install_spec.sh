#/bin/bash

# tools depending on the operating systems
# note that only few functionalities are avaiable on non-gentoo systems
if [ -n "${WINDIR}" ]; then
	#"WINDOWS"
	MY_UNZIP="/c/Program Files/7-Zip/7z.exe"
	MY_UNZIP_OPTION="x"
	PATH_SEPARATOR=";"
else
	#"LINUX"
	MY_UNZIP="tar"
	MY_UNZIP_OPTION="xfvJ"
	PATH_SEPARATOR=":"
fi

# set the output of time
if [ -n "${TIMEFORMAT+x}" ]; then
	MY_TIMEFORMAT="${TIMEFORMAT}"
	MY_TIMEFORMAT_SET="true"
else
	MY_TIMEFORMAT_SET="false"
fi
export TIMEFORMAT='@TIME@real=%lR user=%lU system=%lS'


USER="osboxes"
HYVAR_FOLDER="/home/osboxes/hyvar"
HYVAR_GEN_CONFIG_EXE="${HYVAR_FOLDER}/guest/extract_portage.py"
HYVAR_MAIN_EXE="${HYVAR_FOLDER}/host/scripts/hyportage.py"
HYVARREC_FOLDER="/home/osboxes/hyvarrec"
#HYVARREC_EXE="python ${HYVARREC_FOLDER}/hyvar-rec.py"
HYVARREC_EXE="${HYVARREC_FOLDER}/hyvar-rec"
GIT_PORTAGE_TREE_FOLDER='/home/osboxes/portage-tree'


# main configuration
if [ -z "$2" ]; then
	echo "usage"
	echo "\"$0\" [archive to manipulate] operation"
	echo "	archive must be \"*-installation_spec.zip\""
	echo "	valid operation (in order): setup metadata"
	exit
fi

ARCHIVE="$(pwd)/$1"
FOLDER="${ARCHIVE%-installation_spec*}"
OPERATION="$2"



# configuration of folder and file structure
ARCHIVE_FOLDER="${FOLDER}/archive"				# the folder containing the archive
PORTAGE_REPO="${FOLDER}/portage-tree"			# the folder containing the portage tree
CONFIG_CONTAINING_FOLDER="${FOLDER}/config"		# where all the portage configuration data is stored
GENERATED_DATA_FOLDER="${FOLDER}/gen"			# the folder containing the hyportage generated data

MISSING_EBUILD_FOLDER="${FOLDER}/missing_ebuild" # where the user must put the missing .ebuild
MISSING_EBUILD_FILE="${MISSING_EBUILD_FOLDER}.txt"
STATISTICS_FILE="${FOLDER}/statistics.txt"
TESTS_PERFORMED_FILE="${FOLDER}/performed_tests.txt"

TEST_MODE_TEST_FILE="/var/lib/portage/world"

BASE_LOG_FILE="${FOLDER}/log.txt"
TEST_LOG_FILE="${FOLDER}/log_test.txt"
LOG_FILE="${BASE_LOG_FILE}"

if [ -n "${PYTHONPATH}" ]; then
	export PYTHONPATH="${HYVAR_FOLDER}/guest${PATH_SEPARATOR}${PYTHONPATH}"
else
	export PYTHONPATH="${HYVAR_FOLDER}/guest"
fi

# helper functions
function error {
	echo "Error: $@"
}
function die {
	error "$@"
	exit
}
function give_rights {
	chown -R "${USER}" "${FOLDER}"
}
function create_empty_file {
	touch "${1}" || die "could not create empty file \"${1}\""
	truncate -s 0 "${1}"
}
function register_in_log {
	echo "========================================" >> "${LOG_FILE}"
	echo "$*" >> "${LOG_FILE}"
	echo "=======" >> "${LOG_FILE}"
	{
		time {
			$@
			register_in_log_RETURN_VALUE="$?"
		}
	} &>> "${LOG_FILE}"
	return ${register_in_log_RETURN_VALUE}
}
function run_hyportage {
	[ -n "${HYOUT_DATA_FOLDER}" ] || die "output folder for hyportage is not set"
	mkdir -p "${HYOUT_DATA_FOLDER}"
	register_in_log python "${HYVAR_MAIN_EXE}" "${GENERATED_DATA_FOLDER}" "${GENERATED_DATA_FOLDER}" "${HYOUT_DATA_FOLDER}" --local-solver "${HYVARREC_EXE}" $@
	[ $? -ne "0" ] && [ $1 = "--mode=emerge" ] && register_in_log python "${HYVAR_MAIN_EXE}" "${GENERATED_DATA_FOLDER}" "${GENERATED_DATA_FOLDER}" "${GENERATED_DATA_FOLDER}" --local-solver "${HYVARREC_EXE}" --explain-modality --simplify-mode "individual" $@
}
function test_hyportage_output {
	[ -n "${HYOUT_DATA_FOLDER}" ] || die "output folder for hyportage is not set"
	[ -L "${TEST_MODE_TEST_FILE}" ] || die "we are not in safe mode"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${CONFIG_CONTAINING_FOLDER})" ] || die "the current test mode does not belong to this test"
	echo "========================================" > "${HYOUT_DATA_FOLDER}/log.txt"
	echo "$*" >> "${HYOUT_DATA_FOLDER}/log.txt"
	echo "=======" >> "${HYOUT_DATA_FOLDER}/log.txt"
	# 1. setting up the configuration files
	[ -e /etc/portage/package.use ] && mv /etc/portage/package.use /etc/portage/original-package.use
	[ -e /etc/portage/package.unmask ] && mv /etc/portage/package.unmask /etc/portage/original-package.unmask
	[ -e /etc/portage/package.accept_keywords ] && mv /etc/portage/package.accept_keywords /etc/portage/original-package.accept_keywords
	for i in use unmask accept_keywords; do
		if [ -e "${HYOUT_DATA_FOLDER}/package.$i" ]; then
			echo "using custom package.$i" >> "${HYOUT_DATA_FOLDER}/log.txt"
			cp "${HYOUT_DATA_FOLDER}/package.$i" /etc/portage/
		fi
	done
	echo "=======" >> "${HYOUT_DATA_FOLDER}/log.txt"
	# 2. executing emerge
	bash "${HYOUT_DATA_FOLDER}/emerge.sh" &>> "${HYOUT_DATA_FOLDER}/log.txt"
	# 3. cleaning
	for i in use unmask accept_keywords; do
		[ -e "/etc/portage/package.$i" ] && rm "/etc/portage/package.$i"
	done
	[ -e /etc/portage/original-package.use ] && mv -i /etc/portage/original-package.use /etc/portage/package.use
	[ -e /etc/portage/original-package.unmask ] && mv -i /etc/portage/original-package.unmask /etc/portage/package.unmask
	[ -e /etc/portage/original-package.accept_keywords ] && mv -i /etc/portage/original-package.accept_keywords /etc/portage/package.accept_keywords
}


#######################################
# DATA INSTALLATION
METADATA_FILE="${ARCHIVE_FOLDER}/tmp/installation_spec"

# create folder and extract archive
function unpack_archive {
	echo "=============================="
	echo "unpacking archive"
	cp "${ARCHIVE}" "${ARCHIVE_FOLDER}/archive.zip"
	cd "${ARCHIVE_FOLDER}"
	"${MY_UNZIP}" ${MY_UNZIP_OPTION} "archive.zip" || die "could not unzip the archive"
	cd ..
}

# install the portage tree
function install_portage_repo {
	echo "=============================="
	echo "installing portage repo"
	REPOSITORY_INFO=$(head --lines=1 "${METADATA_FILE}")
	REPOSITORY_DAY=$(echo ${REPOSITORY_INFO} | cut -d' ' -f6)
	REPOSITORY_HOUR=$(echo ${REPOSITORY_INFO} | cut -d' ' -f7)

	if [ ! -e "${PORTAGE_REPO}" ]; then
		if [ ! -e "${GIT_PORTAGE_TREE_FOLDER}" ]; then
			git clone https://anongit.gentoo.org/git/repo/gentoo.git "${GIT_PORTAGE_TREE_FOLDER}" || die "could not clone the portage tree"
		fi
		cp -R "${GIT_PORTAGE_TREE_FOLDER}" "${PORTAGE_REPO}"
	fi

	cd "${PORTAGE_REPO}"
	git checkout `git rev-list -n 1 --before="${REPOSITORY_DAY} ${REPOSITORY_HOUR}" master` || die "could not switch git repository to date \"${REPOSITORY_DAY} ${REPOSITORY_HOUR}\""
	cd ..
}

# check missing ebuild
function get_installed_packages_ebuild {
	echo "=============================="
	echo "computing missing ebuild"
	INSTALLED_PACKAGES=$(sed '1,/==================/d' "${METADATA_FILE}" | sed '/^\s*$/d')
	INSTALLED_PACKAGES_EBUILD=""
	for i in ${INSTALLED_PACKAGES}; do
		EBUILD_NAME=${i##*/}
		CATEGORY=${i%/*}
		local TMP=${EBUILD_NAME##*-}
		PACKAGE_NAME=${EBUILD_NAME%-*}
		[ ${TMP:0:1} == "r" ] && PACKAGE_NAME=${PACKAGE_NAME%-*}
		EBUILD_PATH="${CATEGORY}/${PACKAGE_NAME}/${EBUILD_NAME}.ebuild"
		INSTALLED_PACKAGES_EBUILD="${INSTALLED_PACKAGES_EBUILD} ${EBUILD_PATH}"
	done
}

function get_missing_packages_ebuild {
	echo "=============================="
	echo "saving missing ebuild"
	[ -n "${INSTALLED_PACKAGES}" ] || get_installed_packages_ebuild
	create_empty_file "${MISSING_EBUILD_FILE}"
	cd "${PORTAGE_REPO}"
	for i in ${INSTALLED_PACKAGES_EBUILD}; do
		if [ ! -f "$i" ]; then
			echo "adding missing ebuild \"$i\""
			MISSING_PACKAGE_EBUILD_COMMIT=$(git rev-list -n 1 HEAD -- "$i")
			if [ -n "${MISSING_PACKAGE_EBUILD_COMMIT}" ]; then
				git checkout ${MISSING_PACKAGE_EBUILD_COMMIT}^ -- "$i"
				echo "# ${i}" >> "${MISSING_EBUILD_FILE}" # keep track of deprecated ebuilds
			else
				echo "	ERROR: ebuild missing from repository"
				echo "${i}" >> "${MISSING_EBUILD_FILE}" # for these ones, manual work is required...
			fi
		fi
	done
	cd ..
}


function statistics {
	echo "=============================="
	echo "extracting simple statistics"
	[ -e "${MISSING_EBUILD_FILE}" ] || get_missing_packages_ebuild

	NB_INSTALLED_PACKAGES=$(echo "${INSTALLED_PACKAGES}" | wc -w)
	NB_WORLD=$(wc -l "${ARCHIVE_FOLDER}/var/lib/portage/world" | cut --delimiter=" " -f1)
	NB_DEPRECATED_PACKAGES=$(wc -l "${MISSING_EBUILD_FILE}" | cut --delimiter=" " -f1)
	NB_MISSING_PACKAGES=$(sed '/#.*/d' "${MISSING_EBUILD_FILE}" | wc -l)

	create_empty_file "${STATISTICS_FILE}"
	echo "number of requested packages : ${NB_WORLD}" >> "${STATISTICS_FILE}"
	echo "number of installed packages : ${NB_INSTALLED_PACKAGES}" >> "${STATISTICS_FILE}"
	echo "number of deprecated packages: ${NB_DEPRECATED_PACKAGES}" >> "${STATISTICS_FILE}"
	echo "number of missing packages   : ${NB_MISSING_PACKAGES}" >> "${STATISTICS_FILE}"
	echo "" >> "${STATISTICS_FILE}"
}


# create the archive related data
function rebuild_archive_data {
	echo "=============================="
	echo "building testing config"
	# profile
	PROFILE_INFO="$(head -2 "${METADATA_FILE}" | tail -1)"
	PROFILE_LINK="${PROFILE_INFO##* }"
	PROFILE_LINK=${PROFILE_LINK:5}
	[ -e  "${CONFIG_CONTAINING_FOLDER}/local/make.profile" ] && rm "${CONFIG_CONTAINING_FOLDER}/local/make.profile"
	[ -e  "${ARCHIVE_FOLDER}/etc/portage/make.profile" ] && rm "${ARCHIVE_FOLDER}/etc/portage/make.profile"	
	ln -s "${PROFILE_LINK}" "${CONFIG_CONTAINING_FOLDER}/local/make.profile"
	ln -s "${PROFILE_LINK}" "${ARCHIVE_FOLDER}/etc/portage/make.profile"
	# make.conf
	sed '/USE=".*"$/d' "/etc/portage/make.conf" | sed '/USE=".*/,/*"$/d' > "${CONFIG_CONTAINING_FOLDER}/local/make.conf"
	sed -n '/==================/q;p' "${METADATA_FILE}" | tail -n +3 >> "${CONFIG_CONTAINING_FOLDER}/local/make.conf"
	[ -e  "${ARCHIVE_FOLDER}/etc/portage/make.conf" ] && rm "${ARCHIVE_FOLDER}/etc/portage/make.conf"	
	ln -s "${CONFIG_CONTAINING_FOLDER}/local/make.conf" "${ARCHIVE_FOLDER}/etc/portage/make.conf"
	# installed packages
	[ -n "${INSTALLED_PACKAGES}" ] || get_installed_packages_ebuild
	for i in ${INSTALLED_PACKAGES}; do
		mkdir -p "${CONFIG_CONTAINING_FOLDER}/local/pkg/${i}"
	done
	
}




#######################################
# METADATA GENERATION

function install_missing_packages_ebuild {
	echo "=============================="
	echo "installing missing ebuild"
	[ -L "/etc/portage" ] && die "\"install_missing_packages_ebuild\" must be called in the normal environment"
	[ -e "${MISSING_EBUILD_FILE}" ] || get_missing_packages_ebuild
	STILL_MISSING=""
	for i in $(sed '/#.*/d' "${MISSING_EBUILD_FILE}"); do
		local EBUILD_FOLDER="${PORTAGE_REPO}/${i%/*}"
		local EBUILD_FILE="${i##*/}"
		if [ ! -e "${EBUILD_FOLDER}/${EBUILD_FILE}" ]; then
			if [ -e "${MISSING_EBUILD_FOLDER}/${EBUILD_FILE}" ]; then
				mkdir -p "${EBUILD_FOLDER}"
				cp "${MISSING_EBUILD_FOLDER}/${EBUILD_FILE}" "${EBUILD_FOLDER}"
				#ebuild "${EBUILD_FOLDER}/${EBUILD_FILE}" manifest
			else
				error "ebuild file \"${EBUILD_FILE}\" still missing"
				STILL_MISSING=":("
			fi
		fi
	done
	[ -z "${STILL_MISSING}" ] || die "Missing ebuild files"

	# installing the missing packages that are installed in the default configuration
	for i in $(find /var/db/pkg -name "*.ebuild"); do
		EBUILD_NAME=${i##*/}
		local TMP=${EBUILD_NAME##*-}
		PACKAGE_NAME=${EBUILD_NAME%-*}
		[ ${TMP:0:1} == "r" ] && PACKAGE_NAME=${PACKAGE_NAME%-*}
		CATEGORY=${i%/*}
		CATEGORY=${CATEGORY%/*}
		CATEGORY=${CATEGORY##*/}
		TEST_EBUID_PATH="${PORTAGE_REPO}/${CATEGORY}/${PACKAGE_NAME}/${EBUILD_NAME}"
		if [ ! -e "${TEST_EBUID_PATH}" ]; then
			echo "missing installed ebuild \"$i\""
			mkdir -p "${PORTAGE_REPO}/${CATEGORY}/${PACKAGE_NAME}"
			cp "$i" "${TEST_EBUID_PATH}"
			#ebuild "${TEST_EBUID_PATH}" manifest
		fi
	done

	# installing the .ebuild file in the installed package folder (in case it helps portage)
	[ -n "${INSTALLED_PACKAGES}" ] || get_installed_packages_ebuild
	for i in ${INSTALLED_PACKAGES}; do
		EBUILD_NAME=${i##*/}
		local TMP=${EBUILD_NAME##*-}
		PACKAGE_NAME=${EBUILD_NAME%-*}
		[ ${TMP:0:1} == "r" ] && PACKAGE_NAME=${PACKAGE_NAME%-*}
		CATEGORY=${i%/*}
		cp "${PORTAGE_REPO}/${CATEGORY}/${PACKAGE_NAME}/${EBUILD_NAME}.ebuild" "${CONFIG_CONTAINING_FOLDER}/local/pkg/${i}"
	done
}




function generate_metadata {
	echo "=============================="
	echo "generating the metadata"
	# metadata
	egencache --jobs=9 --update --repo gentoo

}


#######################################
# SWITCHING REPOSITORY

# install the folders and files
function setup_local_config {
	echo "=============================="
	echo "setting up the safe_mode | test_mode"
	[ ! -L "${TEST_MODE_TEST_FILE}" ] || die "the config is already in safe mode"
	mv -i /usr/portage "${CONFIG_CONTAINING_FOLDER}/real/usr-portage"
	mv -i /etc/portage "${CONFIG_CONTAINING_FOLDER}/real/etc-portage"
	mv -i /var/db/pkg  "${CONFIG_CONTAINING_FOLDER}/real/pkg"
	mv -i /var/lib/portage/world "${CONFIG_CONTAINING_FOLDER}/real/world"

	ln -s "${PORTAGE_REPO}" /usr/portage
	ln -s "${ARCHIVE_FOLDER}/etc/portage" /etc/portage
	ln -s "${ARCHIVE_FOLDER}/var/lib/portage/world" "/var/lib/portage/world"
	ln -s "${CONFIG_CONTAINING_FOLDER}/local/pkg" /var/db/pkg
}

function restore_original_config {
	echo "=============================="
	echo "disabling the safe_mode"
	[ -L "${TEST_MODE_TEST_FILE}" ] || die "cannot restore original config: we are not in safe mode"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${FOLDER})" ] || die "the current test mode does not belong to this test"
	rm "/usr/portage"
	rm "/etc/portage"
	rm "/var/lib/portage/world"
	rm "/var/db/pkg"

	mv -i "${CONFIG_CONTAINING_FOLDER}/real/usr-portage" /usr/portage
	mv -i "${CONFIG_CONTAINING_FOLDER}/real/etc-portage" /etc/portage
	mv -i "${CONFIG_CONTAINING_FOLDER}/real/pkg" /var/db/pkg
	mv -i "${CONFIG_CONTAINING_FOLDER}/real/world" /var/lib/portage/world
}


function switch_repo {
	echo "=============================="
	echo "switching portage repo"
	[ -L "${TEST_MODE_TEST_FILE}" ] || die "cannot switch repo: we are not in safe mode"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${FOLDER})" ] || die "the current test mode does not belong to this test"
	if [ -n "$(ls -ld /usr/portage | grep ${PORTAGE_REPO})" ]; then
		rm /usr/portage
		ln -s "${CONFIG_CONTAINING_FOLDER}/real/usr-portage" /usr/portage
	else
		rm /usr/portage
		ln -s "${PORTAGE_REPO}" /usr/portage
	fi
}

function switch_install {
	echo "=============================="
	echo "switching the installation"
	[ -L "${TEST_MODE_TEST_FILE}" ] || die "bad statement sequence: we are not in safe mode"
	if [ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ]; then
		rm "/var/lib/portage/world"
		rm "/var/db/pkg"

		ln -s "${CONFIG_CONTAINING_FOLDER}/real/pkg" /var/db/pkg
		ln -s "${CONFIG_CONTAINING_FOLDER}/real/world" /var/lib/portage/world
	else
		rm "/var/lib/portage/world"
		rm "/var/db/pkg"

		ln -s "${CONFIG_CONTAINING_FOLDER}/local/pkg" /var/db/pkg
		ln -s "${ARCHIVE_FOLDER}/var/lib/portage/world" "/var/lib/portage/world"
	fi
}


#######################################
# EXECUTING PORTAGE AND HYPORTAGE

function generate_pickle {
	echo "=============================="
	echo "generating the .pickle files"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ] || die "executing \"generate_pickle\" outside the testing environment"
	if [ ! -e "${GENERATED_DATA_FOLDER}/packages/portage-tree" ]; then
		mkdir -p "${GENERATED_DATA_FOLDER}/packages/deprecated"
		ln -s "${PORTAGE_REPO}/metadata/md5-cache" "${GENERATED_DATA_FOLDER}/packages/portage-tree"
	fi
	# we should be in the testing configuration
	register_in_log python "${HYVAR_GEN_CONFIG_EXE}" "${GENERATED_DATA_FOLDER}"
	mv "${GENERATED_DATA_FOLDER}/config.pickle" "${GENERATED_DATA_FOLDER}/config_test.pickle"
	switch_install
	register_in_log python "${HYVAR_GEN_CONFIG_EXE}" "${GENERATED_DATA_FOLDER}"
	mv "${GENERATED_DATA_FOLDER}/config.pickle" "${GENERATED_DATA_FOLDER}/config_base.pickle"
	switch_install
	HYOUT_DATA_FOLDER="/non-existing-folder/" # just to be on the safe side
	run_hyportage --mode=update --portage_files "config_test.pickle" "packages" -vvv -p 2
}

function test_hyportage_check_conf {
	echo "=============================="
	echo "test: check"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ] || die "executing \"test_hyportage_check_conf\" outside the testing environment"
	LOG_FILE="${TEST_LOG_FILE}"
	HYOUT_DATA_FOLDER="${GENERATED_DATA_FOLDER}/check"
	run_hyportage --mode=emerge --portage_files "config_test.pickle" "packages" -vvv -p 2
	[ -e "${GENERATED_DATA_FOLDER}/new_configuration.pickle" ] && mv "${GENERATED_DATA_FOLDER}/new_configuration.pickle" "${GENERATED_DATA_FOLDER}/check_new_configuration.pickle"
	LOG_FILE="${BASE_LOG_FILE}"
	echo "check" >> "${TESTS_PERFORMED_FILE}"
}

function test_get_install_set {
	#PACKAGE_SET_INSTALL=$(cat "${ARCHIVE_FOLDER}/var/lib/portage/world")
	PACKAGE_SET_INSTALL=""
	LOG_FILE="${TEST_LOG_FILE}"
	for i in $(cat "${ARCHIVE_FOLDER}/var/lib/portage/world"); do
		ATOM="${i%%::*}"
		[ "${ATOM}" != "${i}" ] && echo "Warning: atom \"${i}\" is annotated with a repo id. Removed" >> "${LOG_FILE}"
		PACKAGE_SET_INSTALL="${PACKAGE_SET_INSTALL} ${ATOM}"
	done
	LOG_FILE="${BASE_LOG_FILE}"
}

function test_hyportage_direct {
	echo "=============================="
	echo "test: direct"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ] && die "executing \"test_hyportage_direct\" inside the testing environment"
	[ -n "${PACKAGE_SET_INSTALL}" ] || test_get_install_set
	LOG_FILE="${TEST_LOG_FILE}"
	HYOUT_DATA_FOLDER="${GENERATED_DATA_FOLDER}/direct"
	run_hyportage --mode=emerge --portage_files "config_base.pickle" "packages" -vvv -p 2 ${PACKAGE_SET_INSTALL}
	[ -e "${GENERATED_DATA_FOLDER}/new_configuration.pickle" ] && mv "${GENERATED_DATA_FOLDER}/new_configuration.pickle" "${GENERATED_DATA_FOLDER}/direct_new_configuration.pickle"
	LOG_FILE="${BASE_LOG_FILE}"
	[ -e "${HYOUT_DATA_FOLDER}/emerge.sh" ] && test_hyportage_output
	echo "direct" >> "${TESTS_PERFORMED_FILE}"
}


function test_hyportage_flexible {
	echo "=============================="
	echo "test: flexible"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ] && die "executing \"test_hyportage_flexible\" inside the testing environment"
	[ -n "${PACKAGE_SET_INSTALL}" ] || test_get_install_set
	LOG_FILE="${TEST_LOG_FILE}"
	HYOUT_DATA_FOLDER="${GENERATED_DATA_FOLDER}/flexible"
	run_hyportage --mode=emerge --portage_files "config_base.pickle" "packages" --exploration "use,keywords" -vvv -p 2 ${PACKAGE_SET_INSTALL}
	[ -e "${GENERATED_DATA_FOLDER}/new_configuration.pickle" ] && mv "${GENERATED_DATA_FOLDER}/new_configuration.pickle" "${GENERATED_DATA_FOLDER}/flexible_new_configuration.pickle"
	LOG_FILE="${BASE_LOG_FILE}"
	[ -e "${HYOUT_DATA_FOLDER}/emerge.sh" ] && test_hyportage_output
	echo "flexible" >> "${TESTS_PERFORMED_FILE}"
}


function test_portage_direct {
	echo "=============================="
	echo "test: portage"
	[ -n "$(ls -l "${TEST_MODE_TEST_FILE}" | grep ${ARCHIVE_FOLDER})" ] && die "executing \"test_portage_direct\" inside the testing environment"
	[ -n "${PACKAGE_SET_INSTALL}" ] || test_get_install_set
	LOG_FILE="${TEST_LOG_FILE}"
	register_in_log emerge -vNp ${PACKAGE_SET_INSTALL}
	[ "$?" -eq "0" ] && touch "${GENERATED_DATA_FOLDER}/emerge_performed.txt"
	LOG_FILE="${BASE_LOG_FILE}"
	echo "portage" >> "${TESTS_PERFORMED_FILE}"
}

#######################################
# MAIN

# this function is to setup the right gentoo environment, with all the required packages
function setup_system {
	if ! which git &> /dev/null; then
		USE="-blksha1 -gpg -iconv -nls -pcre -perl -python -threads -webdav" emerge -av dev-vcs/git
	fi

	if ! which pip &> /dev/null; then
		eselect python set python2.7
		touch /etc/portage/package.accept_keywords
		echo "" >> /etc/portage/package.accept_keywords
		echo "=dev-python/pip-9.0.1-r1" >> /etc/portage/package.accept_keywords
		USE="-python_targets_python3_4 -python_targets_python3_5" emerge -av =dev-python/pip-9.0.1-r1
	fi

	pip install --user click
	pip install --user lrparsing
	pip install --user z3-solver
	pip install --user pysmt
	pip install --user requests
	pip install --user antlr4-python2-runtime

	mkdir -p /home/osboxes/hyvar/guest
	chown -R "${USER}" /home/osboxes/hyvar
}




function setup {
	mkdir -p "${ARCHIVE_FOLDER}" || die "could not create the \"${ARCHIVE_FOLDER}\" folder"
	mkdir -p "${CONFIG_CONTAINING_FOLDER}/real" || die "could not create the \"${CONFIG_CONTAINING_FOLDER}\" folder"
	mkdir -p "${CONFIG_CONTAINING_FOLDER}/local/pkg"
	mkdir -p "${MISSING_EBUILD_FOLDER}" || die "could not create \"${MISSING_EBUILD_FOLDER}\" folder"
	mkdir -p "${GENERATED_DATA_FOLDER}" || die "could not create \"${GENERATED_DATA_FOLDER}\" folder"


	[ -e "${HYVARREC_FOLDER}" ] || git clone https://github.com/HyVar/hyvar-rec.git "${HYVARREC_FOLDER}"

	touch "${LOG_FILE}"

	[ -e "${ARCHIVE_FOLDER}/etc" ] || unpack_archive
	[ -e "${PORTAGE_REPO}" ] || install_portage_repo
	[ -n "${INSTALLED_PACKAGES}" ] || get_installed_packages_ebuild
	[ -e "${MISSING_EBUILD_FILE}" ] || get_missing_packages_ebuild
	[ -e "${ARCHIVE_FOLDER}/etc/portage/make.conf" ] || rebuild_archive_data
	[ -e "${STATISTICS_FILE}" ] || statistics
}

function metadata {
	install_missing_packages_ebuild
	[ -e "${CONFIG_CONTAINING_FOLDER}/real/usr-portage" ] || setup_local_config # we now are in the safe_mode | testing_mode
	[ -e "${PORTAGE_REPO}/metadata/md5-cache" ] || generate_metadata
}

function tests {
	[ -e "${GENERATED_DATA_FOLDER}/hyportage.pickle" ] || generate_pickle
	touch "${TESTS_PERFORMED_FILE}"
	[ -n "$(grep check ${TESTS_PERFORMED_FILE})" ] || test_hyportage_check_conf
	switch_install # switching back to the safe_mode | base_mode
	[ -n "$(grep direct ${TESTS_PERFORMED_FILE})" ] || test_hyportage_direct
	[ -n "$(grep flexible ${TESTS_PERFORMED_FILE})" ] || test_hyportage_flexible
	[ -n "$(grep portage ${TESTS_PERFORMED_FILE})" ] || test_portage_direct
    switch_install # switch back
}

function clean {
	restore_original_config
}

function all {
	setup
	metadata
	tests
}





case "${2}" in
	*)
		shift 1
		$@
		;;
esac


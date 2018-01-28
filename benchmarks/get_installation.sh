#/bin/bash

ARCHIVE_NAME="installation_spec"

[ -e "${ARCHIVE_NAME}" ] && rm "${ARCHIVE_NAME}"

# 1. creating the spec file
TMP_FILE_NAME="/tmp/${ARCHIVE_NAME}"
echo $(ls -ld --time-style=long-iso /usr/portage) > ${TMP_FILE_NAME}
echo $(ls -l /etc/portage/make.profile) >> ${TMP_FILE_NAME}
source /etc/portage/make.conf
echo "USE=\"${USE}\"" >> ${TMP_FILE_NAME}
echo "" >> ${TMP_FILE_NAME}
echo "==================" >> ${TMP_FILE_NAME}
echo "" >> ${TMP_FILE_NAME}

for i in $(find /var/db/pkg -name "*.ebuild"); do
	TMP=${i%%.ebuild}
	PACKAGE=${TMP##*/}
	CATEGORY=${TMP##/var/db/pkg/}
	CATEGORY=${CATEGORY%%/*}
	echo "${CATEGORY}/${PACKAGE}" >> ${TMP_FILE_NAME}
done
echo "" >> "${TMP_FILE_NAME}"

# 2. listing all the files to archive
PACKAGE_USE="/etc/portage/package.use"
PACKAGE_UNMASK="/etc/portage/package.unmask"
PACKAGE_KEYWORDS="/etc/portage/package.accept_keywords"
WORLD="/var/lib/portage/world"

ARCHIVE_LIST="${TMP_FILE_NAME}"
[ -e "${PACKAGE_USE}" ] && ARCHIVE_LIST="${ARCHIVE_LIST} ${PACKAGE_USE}"
[ -e "${PACKAGE_UNMASK}" ] && ARCHIVE_LIST="${ARCHIVE_LIST} ${PACKAGE_UNMASK}"
[ -e "${PACKAGE_KEYWORDS}" ] && ARCHIVE_LIST="${ARCHIVE_LIST} ${PACKAGE_KEYWORDS}"
[ -e "${WORLD}" ] && ARCHIVE_LIST="${ARCHIVE_LIST} ${WORLD}"

# 3. creating the archive
echo "creating the archive"
echo "${ARCHIVE_LIST}" | xargs tar cvfJ "${ARCHIVE_NAME}" 


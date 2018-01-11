#/bin/bash

ARCHIVE_NAME="installation_spec"

[ -a "${ARCHIVE_NAME}" ] && rm "${ARCHIVE_NAME}"


PACKAGE_USE="/etc/portage/package.use"
PACKAGE_UNMASK="/etc/portage/package.unmask"
PACKAGE_KEYWORDS="/etc/portage/package.accept_keywords"
WORLD="/var/lib/portage/world"

[ -a "${PACKAGE_USE}" ] && zip -r ${ARCHIVE_NAME} ${PACKAGE_USE}
[ -a "${PACKAGE_UNMASK}" ] && zip -r ${ARCHIVE_NAME} ${PACKAGE_UNMASK}
[ -a "${PACKAGE_KEYWORDS}" ] && zip -r ${ARCHIVE_NAME} ${PACKAGE_KEYWORDS}
[ -a "${WORLD}" ] && zip ${ARCHIVE_NAME} ${WORLD}


TMP_FILE_NAME="/tmp/${ARCHIVE_NAME}"
echo $(ls -ld /usr/portage) > ${TMP_FILE_NAME}
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
echo "" >> ${TMP_FILE_NAME}

zip ${ARCHIVE_NAME} ${TMP_FILE_NAME}


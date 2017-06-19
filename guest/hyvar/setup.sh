#!/bin/bash

# create the necessary folders and links
GUEST_PACKAGE_DIR="${1}/packages"

# the folder containing all extracted data
mkdir -p "${GUEST_PACKAGE_DIR}"

# the link to the portage tree (we only consider egencache generated files)
ln -s /usr/portage/metadata/md5-cache "${GUEST_PACKAGE_DIR}/portage-tree"

# the folder containing the deprecated packages, necessary as some of them are installed
mkdir -p "${GUEST_PACKAGE_DIR}/deprecated"

# need python2.7 (for now)
eselect python set python2.7

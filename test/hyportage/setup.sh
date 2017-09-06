#!/bin/bash

LOCAL_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"


# put the right files in the right place

cp -i categories /etc/portage/
cp -i repos.conf /etc/portage/

mv -i /etc/portage/make.profile /etc/portage/make.profile.old
ln -s "${LOCAL_DIR}/profiles/root" /etc/portage/make.profile

# create the portage annex data from our test ebuild files

#bash "${LOCAL_DIR}/generate_ebuild_annex_data.sh"


# Copyright 2017 Michael Lienhardt

EAPI=5

# this test shows that in any case, we have that *use.force override *use, which is itself overwritten by *use.mask
#  indeed:
#    - the feature test-force8-123 is selected in ~/profiles/package.use, unselected in ~/profiles/root/package.mask and /etc/portage/profile/package.use.force does not succeed to select it bask
#    - the feature test-force8-132 is selected in ~/profiles/package.use, unselected in /etc/portage/profils/package.use.mask and ~/profiles/roo/package.use.force does not succeed to select it bask
# ...

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE="test-force8-123 test-force8-132 test-force8-213 test-force8-231 test-force8-312 test-force8-321"

DEPEND=""
REQUIRED_USE=""



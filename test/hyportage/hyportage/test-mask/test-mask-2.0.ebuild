# Copyright 2017 Michael Lienhardt

EAPI=5

# this is our last test on package*mask
# this test completes our study on the interaction between mask/unmask, and shows that globally the package*.unmask override the package*.mask
# Indeed, this package is masked in /etc/portage/profile/package.mask, and unmasked in ~/profiles/root/package.unmask

DESCRIPTION="testing the semantics of package.mask / package*.unmask files in the profile"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

DEPEND=""
REQUIRED_USE=""



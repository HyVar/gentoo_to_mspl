# Copyright 2017 Michael Lienhardt

EAPI=5

# this test shows that the package*.unmask override the package*.mask
# Indeed, this package is masked in ~/profiles/root/package.mask, and unmasked in /etc/portage/profile/package.unmask

DESCRIPTION="testing the semantics of package.mask / package*.unmask files in the profile"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

DEPEND=""
REQUIRED_USE=""



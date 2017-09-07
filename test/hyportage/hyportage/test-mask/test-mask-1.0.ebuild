# Copyright 2017 Michael Lienhardt

EAPI=5

# Seing that this is our last test, and we accumulated quite a bit of information now,
#  I don't think it is necessary to throughfully analyse the mask/unmask list construction

# as espected, the package*.mask /package*.unmask do not accept the atom */*
# but accept the - sign: this package is masked in ~/profiles/root/package.mask, and unmasked in /etc/portage/profile/package.mask

DESCRIPTION="testing the semantics of package.mask / package*.unmask files in the profile"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

DEPEND=""
REQUIRED_USE=""



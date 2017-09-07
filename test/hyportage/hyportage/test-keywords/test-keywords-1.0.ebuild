# Copyright 2017 Michael Lienhardt

# this test shows how the keywords and accept_keywords interact.
# In this test, this package is not installable, because even if its keywords contains the arch of this VM, its accept_keywords is emptied in ~/profiles/root/package.accept_keywords

EAPI=5

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

REQUIRED_USE=""



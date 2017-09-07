# Copyright 2017 Michael Lienhardt

EAPI=5
# this test shows that it is not possible, in a package.use* list manipulation file, to totally empty the previously constructed list with a -* symbol
# it seems that it is only possible with keywords...


DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64 ~amd64"

SLOT="0"
IUSE="test-use-selection"

DEPEND=""
REQUIRED_USE=""



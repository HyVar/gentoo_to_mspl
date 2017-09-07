# Copyright 2017 Michael Lienhardt

EAPI=5

# this test shows that package.use.force works are a list manipulation file, as the use flag selected in ~/profiles/root/sub-declaration1/package.use.force is removed by ~/profiles/root/package.use.force

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="~amd64"

SLOT="0"
IUSE="test-use-selection"

DEPEND=""
REQUIRED_USE=""



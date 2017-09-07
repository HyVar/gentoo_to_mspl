# Copyright 2017 Michael Lienhardt

EAPI=5

# this test shows that the USE flag declaration is recursive: the new declarations extend the previous ones
# indeed, this package required sub_implicit_feature to be declared, and it is in ~/profiles/root/sub-declaration1/make.defaults
# it seems thus impossible to undeclare USE flags

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

REQUIRED_USE="implicit_feature sub_implicit_feature"



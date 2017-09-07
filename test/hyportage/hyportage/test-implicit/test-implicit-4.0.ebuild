# Copyright 2017 Michael Lienhardt

EAPI=5

# this test shows that the USE flag declarations are combined between brother sub-profiles
# indeed, this package required sub_implicit_feature (resp. sub_implicit_feature2) to be declared, and it is in ~/profiles/root/sub-declaration1/make.defaults (resp. ~/profiles/root/sub-declarations2/make.defaults)
# it seems thus totally impossible to undeclare USE flags

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

REQUIRED_USE="sub_implicit_feature sub_implicit_feature2"



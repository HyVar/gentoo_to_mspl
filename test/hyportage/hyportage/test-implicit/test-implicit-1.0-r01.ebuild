# Copyright 2017 Michael Lienhardt

EAPI=5

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

#DEPEND=" implicit_feature? ( hyportage/test-deps )"
REQUIRED_USE="implicit_feature feature2 kernel_feature2 local-implicit local-implicit2"



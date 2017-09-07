# Copyright 2017 Michael Lienhardt


# this test shows how the USE flags are implicitly declared in a make.defaults file
# see ~/profiles/root/make.defaults to see how the first three USE flags are declared
# see /etc/portage/profiles/make.defaults to see how the last USE flag is declared. This shows that the user can declare USE flags...

EAPI=5

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

REQUIRED_USE="implicit_feature feature2 kernel_feature2 local-implicit"



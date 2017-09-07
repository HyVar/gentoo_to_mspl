# Copyright 2017 Michael Lienhardt

# this exmaple shows that the user profile in /etc/portage/profile is not recursive
# indeed, the file /etc/portage/profile/make.defaults declare the USE flag local-implicit,
#  while its  ``sub-profile'' /etc/portage/profile/sub-profile declares in its make.defaults the USE flag local-implicit2, which is not included

# in particular, ebuilding or emerging this package fails.

EAPI=5

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

#DEPEND=" implicit_feature? ( hyportage/test-deps )"
REQUIRED_USE="implicit_feature feature2 kernel_feature2 local-implicit"
#REQUIRED_USE="implicit_feature feature2 kernel_feature2 local-implicit local-implicit2"
# the local-implicit2 USE flag is not delclared, which proves that /etc/portage/profile is not recursive



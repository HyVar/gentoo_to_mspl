# Copyright 2017 Michael Lienhardt

EAPI=5
# this test shows that the package.use.* list construction combines the base profile, the default profile and the user profile
# indeed, the USE flag is deselected in ~/profiles/root/package.use.force, and selected back in /etc/portage/profile/package.use.force


DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64 ~amd64"

SLOT="0"
IUSE="test-use-selection"

DEPEND=""
REQUIRED_USE=""



# Copyright 2017 Michael Lienhardt

EAPI=5
# this test shows that the package.use.stable.* list construction is not applied on packages with unstable arches in their accept_keywords
# indeed, the arch ~amd64 is added to this package's accept_keywords in ~/profiles/root/package.accept_keywords, which forbids the removal of test-use-selection done in ~/profiles/root/package.use.stable.force
# Note that this package contains nonetheless a non unstable keywords amd64, but is still considered non stable, due to its accepted_keywords.
# I guess the tool does not expect someone to write a keyword list with the stable and unstable version of the same arch...


DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64 ~amd64"

SLOT="0"
IUSE="test-use-selection"

DEPEND=""
REQUIRED_USE=""



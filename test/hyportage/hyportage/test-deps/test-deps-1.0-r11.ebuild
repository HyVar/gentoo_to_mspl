# Copyright 2017 Michael Lienhardt

EAPI=6

DESCRIPTION="test how dependencies and USE dependencies in the DEPEND variable work"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE="test-feature"

DEPEND="=hyportage/test-dummy-1.0[!test-feature(+)?]"


REQUIRED_USE=""



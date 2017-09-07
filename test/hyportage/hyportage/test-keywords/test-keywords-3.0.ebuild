# Copyright 2017 Michael Lienhardt

# this test shows how the keywords and accept_keywords interact.
# In this test, this package is unstable and installable, even if stated for ppc architecture: we empty its keywords and add ~ppc to it in ~/profiles/root/package.keywords, and does the same with its accept_keywords in ~/profiles/root/package.accept_keywords

EAPI=5

DESCRIPTION="testing USE flags implicit declarations"
HOMEPAGE="http://gzoumix.wikidot.com"

KEYWORDS="amd64"

SLOT="0"
IUSE=""

REQUIRED_USE=""



#1/bin/bash


for EBUILD in $(find . -name "*.ebuild"); do
	ebuild ${EBUILD} manifest
done

egencache --update --repo hyportage



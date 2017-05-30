#!/bin/bash


cd /home/osboxes/hyvar

[ -d gen ] || mkdir gen

tar cvfj gen/portage.tar.bz2 /usr/portage/metadata/md5-cache

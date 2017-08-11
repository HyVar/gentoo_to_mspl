#!/usr/bin/python

import os.path
import json
import multiprocessing
import time
import re
import timeit

import hyportage_from_egencache

import utils
import hyportage_data
import hyportage_pattern


# base configuration

path_to_data = os.path.realpath("../data/")
path_to_data_portage_packages = os.path.join(path_to_data, os.path.join("portage", os.path.join("packages", "portage-tree")))
path_to_data_hyportage=os.path.join(path_to_data, os.path.join("hyportage", "hyportage.enc"))

save_modality="pickle"


# data to check


filenames = ["sys-fs/udev-232-r2", "kde-plasma/powerdevil-5.8.5", "sys-devel/automake-1.15"]
groupnames = [ "dev-lang/python-exec" ]

#constraint_list = [
#	"media-libs/freetype:2 virtual/opengl",
#	">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils",
#	"media-libs/freetype:2= virtual/opengl",
#	"virtual/pkgconfig java? ( >=virtual/jdk-1.4 ) python? ( >=dev-python/cython-0.16[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) bluetooth? ( net-wireless/bluez ) gpm? ( >=sys-libs/gpm-1.20 ) iconv? ( virtual/libiconv ) icu? ( dev-libs/icu:= ) python? ( python_targets_python2_7? ( >=dev-lang/python-2.7.5-r2:2.7 ) python_targets_python3_4? ( dev-lang/python:3.4 ) python_targets_python3_5? ( dev-lang/python:3.5 ) >=dev-lang/python-exec-2:=[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) ncurses? ( sys-libs/ncurses:0= ) nls? ( virtual/libintl ) tcl? ( >=dev-lang/tcl-8.4.15:0= ) usb? ( virtual/libusb:0 ) X? ( x11-libs/libXaw ) ocaml? ( >=dev-ml/findlib-1.0.4-r1 ) java? ( >=dev-java/java-config-2.2.0-r3 ) !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig virtual/pkgconfig"
#	]
#constraint_list = [ ">=sys-apps/util-linux-2.27.1[abi_x86_32(-)?,abi_x86_64(-)?,abi_x86_x32(-)?,abi_mips_n32(-)?,abi_mips_n64(-)?,abi_mips_o32(-)?,abi_ppc_32(-)?,abi_ppc_64(-)?,abi_s390_32(-)?,abi_s390_64(-)?] sys-libs/libcap[abi_x86_32(-)?,abi_x86_64(-)?,abi_x86_x32(-)?,abi_mips_n32(-)?,abi_mips_n64(-)?,abi_mips_o32(-)?,abi_ppc_32(-)?,abi_ppc_64(-)?,abi_s390_32(-)?,abi_s390_64(-)?] acl? ( sys-apps/acl ) kmod? ( >=sys-apps/kmod-16 ) selinux? ( >=sys-libs/libselinux-2.1.9 ) !<sys-libs/glibc-2.11 !sys-apps/gentoo-systemd-integration !sys-apps/systemd abi_x86_32? ( !<=app-emulation/emul-linux-x86-baselibs-20130224-r7 !app-emulation/emul-linux-x86-baselibs[-abi_x86_32(-)] ) dev-util/gperf >=dev-util/intltool-0.50 >=sys-apps/coreutils-8.16 virtual/os-headers virtual/pkgconfig >=sys-devel/make-3.82-r4 >=sys-kernel/linux-headers-3.9 app-text/docbook-xml-dtd:4.2 app-text/docbook-xml-dtd:4.5 app-text/docbook-xsl-stylesheets dev-libs/libxslt !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig" ]
constraint_list = [ "!compute-only? ( || ( mysql postgres sqlite ) ) compute-only? ( compute !rabbitmq !memcached !mysql !postgres !sqlite ) || ( python_targets_python2_7 )" ]


# check data loading

def test_parse_require(constraint_list):
	identifier = 1
	for constraint in constraint_list:
		print("==========")
		print(str(hyportage_from_egencache.require.parse(constraint)))
		ast = hyportage_from_egencache.translate_require(constraint)
		print("==========")
		print(str(ast))


def test_parse_depend(constraint_list):
	identifier = 1
	for constraint in constraint_list:
		ast = hyportage_from_egencache.translate_depend(constraint)
		print("==========")
		print(str(ast))


def test_load_packages(concurrent_map, paths):
	print("Translated MSPL:")
	raw_mspl = concurrent_map(hyportage_from_egencache.load_spl_from_egencache_file, paths)
	print("===============")
	print(str(raw_mspl))
	print("===============")

def spl_groups_to_spls(spl_groups):
	filenames = []
	for spl_group in spl_groups:
		array = spl_group.split("/")
		path = os.path.join(path_to_data_portage_packages, array[0])
		filenames.extend( [os.path.join(path, filename) for filename in os.listdir(path) if filename.startswith(array[1])] )
	return filenames
 

# check constructed data

def test_pattern_group_name():
	path_hyportage = path_to_data_hyportage
	if save_modality.endswith("json"):
		pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = hyportage_data.hyportage_data_from_save_format(utils.load_data_file(path_hyportage, save_modality))
	else:
		pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = utils.load_data_file(path_hyportage, save_modality)
	for spl in mspl.values():
		for pattern in hyportage_data.spl_get_dependencies(spl).keys():
			if hyportage_pattern.pattern_get_package_group(pattern)[0] in "=<>~":
				print(hyportage_data.spl_get_name(spl) + " => " + (str(pattern)))




# main

if __name__ == "__main__":
	# test partsing constraints
	test_parse_require(constraint_list)
	#test_parse_depend(constraint_list)
	# test loading files
	#test_load_packages(map, filenames)
	# test loading group
	#test_load_packages(map, spl_groups_to_spls(groupnames))
	# test the groups of the spls
	#test_load_packages(map, spl_groups_to_spls([ hyportage_from_egencache.structure_package_name(name)[0] for name in filenames ]))
	# test patterns of loaded spls
	#test_pattern_group_name()




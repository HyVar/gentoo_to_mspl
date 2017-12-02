#!/usr/bin/python

import os.path

import utils
import hyportage
import hyportage_ids
import hyportage_data
import hyportage_pattern
import utils_egencache


# base configuration

path_to_data = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)),"../data/"))
path_to_data_portage_packages = os.path.join(path_to_data, os.path.join("portage", os.path.join("packages", "portage-tree")))
path_to_data_hyportage=os.path.join(path_to_data, os.path.join("hyportage", "hyportage.enc"))


######################################################################
# 1. CORE TESTS
######################################################################


# data to check


filenames = ["sys-fs/udev-232-r2", "kde-plasma/powerdevil-5.8.5", "sys-devel/automake-1.15"]
groupnames = ["dev-lang/python-exec"]

constraint_list_depend = [
	"media-libs/freetype:2 virtual/opengl",
	">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils",
	"media-libs/freetype:2= virtual/opengl",
	"virtual/pkgconfig java? ( >=virtual/jdk-1.4 ) python? ( >=dev-python/cython-0.16[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) bluetooth? ( net-wireless/bluez ) gpm? ( >=sys-libs/gpm-1.20 ) iconv? ( virtual/libiconv ) icu? ( dev-libs/icu:= ) python? ( python_targets_python2_7? ( >=dev-lang/python-2.7.5-r2:2.7 ) python_targets_python3_4? ( dev-lang/python:3.4 ) python_targets_python3_5? ( dev-lang/python:3.5 ) >=dev-lang/python-exec-2:=[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) ncurses? ( sys-libs/ncurses:0= ) nls? ( virtual/libintl ) tcl? ( >=dev-lang/tcl-8.4.15:0= ) usb? ( virtual/libusb:0 ) X? ( x11-libs/libXaw ) ocaml? ( >=dev-ml/findlib-1.0.4-r1 ) java? ( >=dev-java/java-config-2.2.0-r3 ) !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig virtual/pkgconfig"
	]
constraint_list_depend2 = [ ">=sys-apps/util-linux-2.27.1[abi_x86_32(-)?,abi_x86_64(-)?,abi_x86_x32(-)?,abi_mips_n32(-)?,abi_mips_n64(-)?,abi_mips_o32(-)?,abi_ppc_32(-)?,abi_ppc_64(-)?,abi_s390_32(-)?,abi_s390_64(-)?] sys-libs/libcap[abi_x86_32(-)?,abi_x86_64(-)?,abi_x86_x32(-)?,abi_mips_n32(-)?,abi_mips_n64(-)?,abi_mips_o32(-)?,abi_ppc_32(-)?,abi_ppc_64(-)?,abi_s390_32(-)?,abi_s390_64(-)?] acl? ( sys-apps/acl ) kmod? ( >=sys-apps/kmod-16 ) selinux? ( >=sys-libs/libselinux-2.1.9 ) !<sys-libs/glibc-2.11 !sys-apps/gentoo-systemd-integration !sys-apps/systemd abi_x86_32? ( !<=app-emulation/emul-linux-x86-baselibs-20130224-r7 !app-emulation/emul-linux-x86-baselibs[-abi_x86_32(-)] ) dev-util/gperf >=dev-util/intltool-0.50 >=sys-apps/coreutils-8.16 virtual/os-headers virtual/pkgconfig >=sys-devel/make-3.82-r4 >=sys-kernel/linux-headers-3.9 app-text/docbook-xml-dtd:4.2 app-text/docbook-xml-dtd:4.5 app-text/docbook-xsl-stylesheets dev-libs/libxslt !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig" ]
constraint_list_require = [ "!compute-only? ( || ( mysql postgres sqlite ) ) compute-only? ( compute !rabbitmq !memcached !mysql !postgres !sqlite ) || ( python_targets_python2_7 )" ]


# check data loading

def test_parse_require(constraint_list):
	identifier = 1
	for constraint in constraint_list:
		print("==========")
		print(str(utils_egencache.require.parse(constraint)))
		ast = utils_egencache.translate_require(constraint)
		print("==========")
		print(str(ast))


def test_parse_depend(constraint_list):
	identifier = 1
	for constraint in constraint_list:
		ast = utils_egencache.translate_depend(constraint)
		print("==========")
		print(str(ast))


def test_load_packages(concurrent_map, paths):
	print("Translated MSPL:")
	raw_mspl = concurrent_map(utils_egencache.create_spl_from_egencache_file, paths)
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


######################################################################
# 2. STATISTICS
######################################################################

def load_hyportage_db():
	save_modality = "pickle"
	path_db_hyportage = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)),"../data/hyportage/hyportage.enc"))
	print(path_db_hyportage)
	global pattern_repository, flat_pattern_repository, id_repository, keywords, mspl, spl_groups, core_configuration, installed_spls
	pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = hyportage.load_hyportage(path_db_hyportage, save_modality)
	flat_pattern_repository = pattern_repository[1]
	for local_map in pattern_repository[0].values():
		flat_pattern_repository.update_set(local_map)
	keywords = set(hyportage_ids.id_repository_get_keywords(id_repository)[0])


use_flag_statistics_path = os.path.abspath(
	os.path.join(os.path.dirname(os.path.realpath(__file__)), "../../use_flag_statistics.md"))

def use_flags_statistics_init(path):
	with open(path, 'w') as f:
		f.write("# USE Flag Statistics\n")
		f.write("\n")
		f.write("\n")

def write_use_flags_statistics_core(path):
	with open(path, "a") as f:
		f.write("## Core Statistics\n")
		f.write("\n")
		f.write("In this section, we give general statistics of USE flags:\n")
		use_flags_max = 0
		use_flags_sum = 0
		use_flags_min = 100
		spl_min = []
		spl_max = []
		nb_spl = len(mspl)
		for spl in mspl.values():
			use_flag_size = len(hyportage_data.spl_get_iuses_default(spl))
			if use_flag_size < use_flags_min:
				use_flags_min = use_flag_size
				spl_min = [spl.name]
			elif use_flag_size == use_flags_min: spl_min.append(spl.name)
			if use_flag_size > use_flags_max:
				use_flags_max = use_flag_size
				spl_max = [spl.name]
			elif use_flag_size == use_flags_max: spl_max.append(spl.name)
			use_flags_sum = use_flags_sum + use_flag_size
		f.write(" * minimum number of use flag per package: " + str(use_flags_min) + "\n")
		f.write("   * package with this number of use flags: " + str(sorted(spl_min)) + "\n")
		f.write(" * maximum number of use flag per package: " + str(use_flags_max) + "\n")
		f.write("   * package with this number of use flags: " + str(sorted(spl_max)) + "\n")
		f.write(" * average number of use flags: " + str(use_flags_sum) + " / " + str(nb_spl) + " = " + str(use_flags_sum / nb_spl) + "\n")
		f.write(" * number of additional use flags from arch:" + str(len(keywords)) + "\n")


def write_use_flags_statistics_missing_locally(path):
	with open(path, 'a') as f:
		f.write("# USE Flag Statistics\n")
		f.write("\n")
		f.write("\n")
		# locally missing use flags
		print("computing locally missing use flags")
		f.write("## Locally Missing USE Flags\n")
		f.write("\n")
		f.write("Here we list the USE Flags that are not declared in a package, but used in its own constraints.\n")
		f.write("\n")
		f.write("Such USE flags must then be declared in the portage profile,\n")
		f.write(" otherwise this inconsistency means that the package cannot be installed\n")
		f.write("\n")
		data = {}
		for spl in mspl.values():
			print("processing " + spl.name)
			diff = spl.required_iuses_local.difference(spl.iuses_default)
			diff.difference_update(hyportage_data.keywords_get_core_set(spl.keywords_list))
			if diff:
				data[spl.name] = diff
		f.write("### Missing USE Flags Full List\n")
		missing_use_flags = {use_flag for use_flags in data.values() for use_flag in use_flags}
		f.write("\n")
		f.write("Number of missing USE flags: " + str(len(missing_use_flags)) + "\n")
		if missing_use_flags:
			f.write("\n")
			f.write("```\n")
			f.write("[\n")
			f.write(",\n".join(sorted({("    " + use_flag) for use_flag in missing_use_flags})))
			f.write("\n]\n")
			f.write("```\n")
		f.write("\n")
		f.write("### Per package\n")
		f.write("\n")
		f.write("```\n")
		for key, v in data.iteritems():
			f.write(key + ": " + str(v) + "\n")
		f.write("```\n")
		f.write("\n")

def write_use_flag_statistics_missing_externally(path):
	with open(path, 'a') as f:
		# externally missing use flags
		print("computing externally missing use flags")
		f.write("## Externally Missing USE Flags\n")
		f.write("\n")
		f.write("USE Flags that are not declared in a package, but used in another constraint constraints\n")
		f.write("\n")
		f.write("### Per package\n")
		f.write("\n")
		f.write("```\n")
		data = set()
		for spl in mspl.values():
			print("processing " + spl.name)
			diff = hyportage_pattern.pattern_repository_get_spl_required_use(pattern_repository, spl).difference(spl.iuses_default)
			if diff:
				data.update(diff)
				f.write(spl.name + ": " + str(list(diff)) + "\n")
		f.write("```\n")
		f.write("\n")
		f.write("### Missing USE Flags Full List\n")
		f.write("\n")
		f.write("```\n")
		f.write(str(list(data)) + "\n")
		f.write("```\n")
		f.write("\n")


def get_spl(spl_name):
	return mspl[spl_name]


def get_pattern_element(atom):
	return hyportage_pattern.pattern_repository_get(pattern_repository, hyportage_pattern.pattern_create_from_atom(atom))

def quick_get(atom):
	load_hyportage_db()
	el = get_pattern_element(atom)
	return [spl.name for spl in el.containing_spl]

def local_mapping_to_mapping(local_mapping):
	return {
		hyportage_pattern.pattern_to_atom(pattern): [ spl.name for spl in el.containing_spl ]
		for pattern, el in local_mapping.iteritems()
	}

def get_core_pattern_repository():
	m = local_mapping_to_mapping(pattern_repository[1])
	for mapping in pattern_repository[0].values():
		m.update(local_mapping_to_mapping(mapping))
	return m

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




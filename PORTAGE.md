# Portage: an Overview

[Portage](https://wiki.gentoo.org/wiki/Portage) ([wikipedia](https://en.wikipedia.org/wiki/Portage_(software))) is the package manager of the [Gentoo](https://gentoo.org/) Linux distribution.


## Core Principles

The main characteristics of portage, compared to other package managers, is that its packages are distributed as source code (when possible),
 which can be configured by the machine's administrator, prior to compilation and installation of the package.
Portage contains a unified interface for configuring the package, called [USE flags](https://wiki.gentoo.org/wiki/Handbook:AMD64/Working/USE).
In principle, USE flags are *features* giving a [Software Product Line (SPL)](https://en.wikipedia.org/wiki/Software_product_line) structure to all of the portage's packages.

#### Portage's Repository Structure

Portage declares its package in [*.ebuild*](https://devmanual.gentoo.org/ebuild-writing/index.html) files.
These files are structured in a folder structure of the following form:
```
/usr/portage/ +
              |
              +-> <category> / +
                               |
                               +-> <group> / +
                                             |
                                             +-> <group>-<version>.ebuild
```

The folder `/usr/portage` is the root directory of the portage tree.
This root directory contains many categories (e.g., `kde-apps`, `www-client`),
 plus several folders containing configuration data (we may discuss them later).
These categories contains several groups corresponding to one library or one software (e.g., `konsole`, `firefox`).
Finally, these groups contains several `.ebuild` files, one per version of the group.

#### Portage's Packages as Software Product Lines

A package's *.ebuild* file follows a syntax close to a bash script file,
 and declares a set of information defining its (hybrid-dependent) SPL structure:
 * `IUSE`: this variable declares the list of USE flags (i.e., SPL's features) for this package
 * `REQUIRED_USE`: this variable declares a constraint on the package's USE flag, thus defining the local [Feature Model](https://en.wikipedia.org/wiki/Feature_model) of this SPL
 * [`DEPEND`, `RDEPEND` and `PDEPEND`](https://devmanual.gentoo.org/general-concepts/dependencies/index.html):
    these variables declare constraints stating the dependencies to other packages,
    thus giving a structure of **Dependent SPL** to the package.
   Note that the dependency of a package is structure in three variables to follow the package's installation life cycle:
    `DEPEND` is the dependency activated for the installation of the package,
    `RDEPEND` is the dependency activated for the correct usage of the content of the package,
    and `PDEPEND` has a similar semantics to `RDEPEND` but is used to avoid circular dependency within the same life-cycle stage.
 * `KEYWORDS`: this variable lists the architecture on which this package can be installed,
    thus giving a structure of **Hybrid SPL** to the package.
   Note that these package can be prefixed by `~` to state that this package is not thoroughly tested on that architecture.

#### Feature Model Syntax

As discussed previously, the Feture Model of a Portage package is declared with six variables:
 * `IUSE` lists the features of the Feature Model
 * `REQUIRED_USE` defines the *local* part of the Feature Model
 * `DEPEND`, `RDEPEND` and `PDEPEND` define the *dependency* part of the Feature Model

The syntax of the `REQUIRED_USE` constraint is as follows:
```
REQUIRED_USE ::= EL*
EL ::= '!'? feature | '!'? feature '?' '(' EL* ')' | OPERATOR '(' EL* ')' | '(' EL* ')'
OPERATOR ::= '||' | '^^' | '??'
```
In this syntax, `feature` requires for `feature` to be selected,
 `!` is the standard not operator,
 `?` is the implication operator (`!feature? (EL*)` means that if the feature `feature` is not selected, then `EL*` must hold),
 `||` is the or operator (at least one constraint in the following group must be satisfied),
 `^^` is the xor operator (exactly one constraint in the following group must be satisfied),
 `??` is the one-max operator (at most one constraint in the following group can be satisfied).

The syntax of the `*DEPEND` constraint is as follows:
```
DEPEND ::= EL*
EL ::= '!'? atom SELECTION? | '!'? feature '?' '(' EL* ')' | OPERATOR '(' EL* ')' | '(' EL* ')'
SELECTION ::= '[' feature_selection (',' feature_selection)* ']'
OPERATOR ::= '||' | '^^' | '??'
```
This syntax is similar to the one for `REQUIRED_USE`, with two core difference:
 * instead of selecting features, this syntax selects *atoms*, with an optional `SELECTION`.
   Portage is a package manager with a little less than 40000 packages,
    and so package selection is not done on a per-package basis, but through atoms (or [*package dependency specification*](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)) that corresponds to a set of packages.
   We won't go in details into the syntax of atoms in this section,
    we just want to point out that atoms are a very low level and implicit notion of SPL Interface:
     it is a name on which an SPL can depend on, and that can be implemented by several SPLs.
   No notion of Feature Model or code interface is associated to this low level notion of [SPL interface](http://fsen.ir/2017/files/Preproceedings.pdf) (page 29).
 * `SELECTION` is the portage's way to specify a *partial product* for a package's dependency.
   Like for atoms, we won't go in details into the syntax of partial product,
    we just want to point our that it can select or require unselected some features,
    with such feature selection possibly guarded by some local feature being selected or unselected.

For more information about the `*DEPEND` variables, you can look at the [documentation](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
 and the [full semantics of partial product specification](#semantics-of-use-flags-selection-in-constraints).


## Configuration

As introduced previously, portage's packages are configured
 via the selection and non-selection (i.e., a product) of USE flags (i.e., features).
The most direct way to configure packages is via the file [`/etc/portage/package.use`](https://wiki.gentoo.org/wiki//etc/portage/package.use),
 in which the administrator can specify a list of USE flags to select or unselect (when guarded with `-`) for an *atom*, one per line.
Note that the list of USE flags specifies a *partial product* (i.e., the administrator can miss to specify the selection status of some USE flags, which are then implicitly set to unselected by portage).

**Example**
```
# Configure one package of the group git, selecting curl and unselecting emacs
=dev-vcs/git-2.12.1 curl -emacs

# Globally disable the unwanted USE Flags which were enabled by the profile
*/* -bluetooth -consolekit -dbus -ldap -libnotify -nls -qt3support -udisks

# enable the offensive USE flag for app-admin/sudo
app-admin/sudo offensive

# disable mysql support for dev-lang/php
dev-lang/php -mysql

# enable java and set the python interpreter version for libreoffice-5.1
app-office/libreoffice java python_single_target_python3_4
```



# Portage: in Depth Documentation

In this section, we discuss more in details most of the aspects of portage, and in particular
 the ones related to package structure, package configuration, and the semantics of the dependency solver
  (which are necessary information to design a solver that computes a configuration from a user request).


## Portage Directory Structure

We already presented in the [Repository Structure Section](#portages-repository-structure)
 the part of the folder structure of portage where packages are declared.
Additionally, portage contains other folders containing configuration or annex data that can be very important.
The folders [md5-cache](#usrportagemetadatamd5-cache) and [profiles](#usrportageprofiles) are indeed central in portage.

### /usr/portage/distfiles

This folder is where portage stores all the source code of the installed packages:
 when a package is pulled to be installed, portage downloads its source code (storing the archive in `/usr/portage/distfiles`),
 compiles and install it.
Note that portage never cleans this folder (to avoid downloading the same archive several time),
 and so the administrator should remove by hand some of the archives stored there
 to avoid filling the disk space with useless data.

### /usr/portage/eclass

This folder contains the [eclasses](https://devmanual.gentoo.org/eclass-reference/) of portage.
An [eclass](https://devmanual.gentoo.org/eclass-writing/) is a bash file defining several functions and data
 that can be used by packages in their definition.
Indeed, an `.ebuild` file (which is a bash script) can use the `inherit` function to import several of these files,
 and thus import all the data and functions they contain and use them in its definition.
For instance, [eutils.class](https://devmanual.gentoo.org/eclass-reference/eutils.eclass/index.html)
 declares many utility functions for package installation,
 while [python-single-r1.class](https://devmanual.gentoo.org/eclass-reference/python-single-r1.eclass/index.html)
 declares python related functions and variable for feature model construction specifically for python related packages.

### /usr/portage/header.txt

This file contains the header of all the `.ebuild` files in the portage package repository.
In particular, if someone wants to write a portage package a software,
 he must put the content of this file as header of his `.ebuild` file.

### /usr/portage/licenses

This folder contains all the licences of all the packages in the portage repository.
That way, if an administrator needs to install a package bound by a licence he does not know,
 he can read it before accepting it and installing the package, or not.
We will discuss Licenses more in details in the Section about the [package's data](#definition-of-a-package).

### /usr/portage/metadata

This folder contains several data about the repository management,
 like the [`layout.conf`](https://wiki.gentoo.org/wiki/Repository_format/metadata/layout.conf) file,
 or the `news` folder that contains all the messages from the portage package developpers to the system administrators.
Moreover, this folder contains the `md5-cache` folder that needs to be discussed in detail.

#### /usr/portage/metadata/md5-cache

We previously discussed the fact that the `.ebuild` files that define a package are bash scripts
 that may include definitions from many other files (with the `inherit` function).
Consequently, knowing the feature model and the dependencies of a package can require some long computation
 which must be performed every time the portage `emerge` tool is called.
To avoid computing this information many time,
 the [`egencache`](https://wiki.gentoo.org/wiki/Egencache) tool extract them from a `.ebuild` file and store them in a file
 in the `/usr/portage/metadata/md5-cache` folder:
 that folder thus contains all packages' raw information related to feature model, dependencies and visibility
 (we will discuss this information more in detail in the Section about the [package's data](#definition-of-a-package)).
The structure of the `md5-cache` folder is as follows:

```
/usr/portage/metadata/md5-cache +
                                |
                                +-> <category> / +
                                                 |
                                                 +-> <group>-<version>
```
each `<category>/<group>/<group>-<version>.ebuild` file is abstracted in a `<category>/<group>-<version>` egencache file.
By default, the `emerge` tool uses these files in its computation,
 as discussed in [here](https://wiki.gentoo.org/wiki//usr/portage/metadata/md5-cache).

### /usr/portage/profiles

This folder contains all data used by portage to compute a default configuration for its package.
This data is structure w.r.t. the architecture considered,
 so a package installed on MacOS will not be configured in the same way as a package installed on Linux
 (e.g., a package on MacOS will use `aqua` for its GUI toolkit, while on Linux `aqua` is not available).
The content of this folder is central in how packages are configured, and will be discussed more in details in the Section
 about [package configuration](#package-configuration).

### /usr/portage/scripts

This folder contains one sh script,
 [`bootstrap.sh`](https://wiki.gentoo.org/wiki/FAQ#How_do_I_install_Gentoo_using_a_stage1_or_stage2_tarball.3F)
 that can be called to recompile all the base portage package from scratch during the initial installation of the gentoo system.

## Definition of a Package

In portage, packages are characterised by several information that we structure in four categories.
To illustrate our presentation, we will use the content of the package `app-admin/sudo-1.8.19_p2`,
 called `sudo` in this section for simplicity.


### Feature Model

The feature model of a package contains all the information related to its variability
 and its relationship with other packages.
It is described in portage with 6 information:

 - [**IUSE**](https://dev.gentoo.org/~zmedico/portage/doc/portage.html#package-ebuild-eapi-1-iuse-defaults)
    This variable declares the list of default features (or *USE flags* in portage terminology) of the package.
    Additionally, the USE flags in this list can be prefixed with `+` or `-` to specify a *USE flag manipulation*
    that is used to define the default product (or *USE flag selection*) of the package.
    This will be discussed more in detail in the section about [USE flag configuration](#use-flags-configuration).
    The IUSE of the `sudo` package is
    ```
    ldap nls pam offensive selinux skey +sendmail
    ```
    As we just discussed, this is the list of the default features of this package.
    Note that `sendmail` is prefixed with `+`, that states that the default product of this package (most probably) contains that feature.
    Note also that this variable lists the *default* features of the package:
    *implicit* features can be added to it by the portage or user profile, as discussed in the [USE flag configuration](#iuse).
 - **SELECTED_USE**
   To the best of our knowledge, this information is not explicitly named in the portage documentation,
   and corresponds to the product (i.e. the set of USE flags) that is installed when installing the package.
   This product is not directly stated by the user (it is not possible to write something like `SELECTED_USE=<list of USE flags`),
   but is constructed in several steps, as discussed in the [package configuration section](#selected-use).
 - [**REQUIRED_USE**](https://dev.gentoo.org/~zmedico/portage/doc/portage.html#package-ebuild-eapi-4-metadata-required-use)
   This variable contains a constraint that states what are the valid products of the package,
   i.e. how the USE flags can be selected for this package.
   The REQUIRED_USE of the `sudo` package is
   ```
   pam? ( !skey ) skey? ( !pam )
   ```
   This constraint states that the features `pam` and `skey` are in conflict and cannot be selected together.
   For instance, the product `sendmail skey` is valid, while `sendmail pam skey` is not.
 - [**DEPEND**](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
   This variable contains a constraint stating for every product of the package,
   which other packages are required during (or in conflict with) the installation of the current package.
   A core aspect in the definition of a package's dependency is the notion of [*atom*](https://dev.gentoo.org/~zmedico/portage/doc/man/ebuild.5.html).
   An atom is a kind of [*pattern*](https://en.wikipedia.org/wiki/Pattern_matching) used to represent a set of packages,
   and is essential in portage, as explicitly listing all packages related to a dependency is unmaintainable.
   We invite the interested reader to look at the [documentation](https://devmanual.gentoo.org/general-concepts/dependencies/index.html).
   It is moreover important to note that *atoms* also are a core element in the way portage implements package configuration, as discussed in the [portage configuration's implementation section](#portage-layered-configuration).
   \
   The DEPEND variable of the `sudo` package is
   ```
   pam? ( virtual/pam ) skey? ( >=sys-auth/skey-1.1.5-r1 ) ldap? ( >=net-nds/openldap-2.1.30-r1 dev-libs/cyrus-sasl ) sys-libs/zlib sys-devel/bison
   ```
   This constraint states for instance that if the feature `pam` is selected, then one of the packages implementing `virtual/pam` must be present during its installation.
   Note also that this package depends on `sys-devel/bison` which is used to generate a grammar in the sudo source code.
 - [**RDEPEND**](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
   This variable contains a constraint following the same syntax as DEPEND, that describes the dependencies *at runtime* of the package.
   For instance, the RDEPEND of `sudo` is
   ```
   pam? ( virtual/pam ) skey? ( >=sys-auth/skey-1.1.5-r1 ) ldap? ( >=net-nds/openldap-2.1.30-r1 dev-libs/cyrus-sasl ) sys-libs/zlib selinux? ( sec-policy/selinux-sudo ) ldap? ( dev-lang/perl ) pam? ( sys-auth/pambase ) >=app-misc/editor-wrapper-3 virtual/editor sendmail? ( virtual/mta )
   ```
   In this constraint, it is possible to see that the dependency to `sys-devel/bison` is not present anymore (the package is indeed installed so it is not necessary to download its source code), but additional dependencies like `virtual/editor` appeared.
 - [**PDEPEND**](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
   This variable is similar to the two previous ones as it contains the *post-merge* dependencies, i.e.
   > dependencies that should be merged after the package, but which may be merged at any time, if the former is not possible.
   > [...] Generally `PDEPEND` should be avoided in favour of `RDEPEND` except where this will create circular dependency chains.
   The `sudo` package does not have a PDEPEND variable.
 - [**SLOT**](https://devmanual.gentoo.org/general-concepts/slotting/index.html)
   Slots is portage's mechanism to specify which packages of the same group can be installed at the same time.
   This is very useful for instance for `python` that has two parallel sets of versions: `2.7.*` and `3.*`.
   The slot of a package is simply a string (by default `0`), and two package of the same group can be installed at the same time only if their slot is different.
   The SLOT variable thus contains the slot of the package, plus an optional *subslot* separated from the slot with a `/` character.
   This subslot is not used to specify conflicts between packages, but to specify recompilation events:
    a package that has a [*`=` slot dependency*](https://devmanual.gentoo.org/general-concepts/dependencies/index.html#slot-dependencies) must be recompiled if that dependency changes sublot.
   The `sudo` package has a simple `SLOT=0` slot variable.


### Visibility

The visibility of a package states if a package can be considered in an installation process or not.
It is related to different factors: the computer hardware architecture (not all program can be installed on all architecture), if the package is stable or not, etc.
In the following, we list the different data related to a package visibility:

 - [**KEYWORDS**](https://wiki.gentoo.org/wiki/KEYWORDS)
   As previously discussed, KEYWORDS is a variable that lists the architecture on which this package can be installed.
   By default, this variable contains just a list of architecture names,
    possibly prefixed with `~` to state that this package might be installable on that architecture but is not fully tested: this package is *unstable* for that architecture.
   Additionally, this list can also contain *set operators* like `-*` that removes all previously specified architectures (see the [documentation](https://wiki.gentoo.org/wiki/KEYWORDS) for more information).
   The KEYWORDS variable of `sudo` is a simple list of architecture (like most packages) that however states that this package is not tested on any architecture:
   ```
   ~alpha ~amd64 ~arm ~arm64 ~hppa ~ia64 ~m68k ~mips ~ppc ~ppc64 ~s390 ~sh ~sparc ~x86 ~amd64-fbsd ~sparc-fbsd ~x86-fbsd ~sparc-solaris
   ```
 - [**ACCEPT_KEYWORDS**](https://wiki.gentoo.org/wiki/ACCEPT_KEYWORDS/en)
   By default, a package can only be installed if the hardware architecture of the computer (specified in the `ARCH` variable in portage) is listed in the KEYWORDS variable of the package.
   However, this behavior can be overwritten by the user, by specifying an ACCEPT_KEYWORDS for this packages.
   This variable override the `ARCH` variable, and lists the architecture against which the package's KEYWORDS must be confronted.
   For instance, specifying the ACCEPT_KEYWORDS `~alpha` for `sudo` would make this package installable.
   We will see in the TODO how to specify a package's ACCEPT_KEYWORDS
 - **INSTALLABLE** and **STABLE** These two information are a consequence to the matching between a package's KEYWORDS, its ACCEPT_KEYWORDS, and the ARCH variable.
   A package is *installable* if the intersection between the set stated by its KEYWORDS variable and ARCH (or its ACCEPT_KEYWORDS if defined) is non empty.
   A package is *stable* if that intersection contains no testing architecture (i.e., architecture prefixed with `~`).
 - [**(UN)**](https://wiki.gentoo.org/wiki/Knowledge_Base:Unmasking_a_package) [**MASK**](https://wiki.gentoo.org/wiki/Knowledge_Base:Masking_a_package)
   In portage, package can be masked so they will never be installed.
   Masked package can also be unmasked by the user so he can install it nonetheless (assuming the risk that it could break something in his system).
 - [**LICENSE**](https://www.gentoo.org/glep/glep-0023.html)
   This variable is a constraint (that uses a syntax identical to the one in REQUIRED_USE) that lists the licenses under which the package is distributed.
   This is essential, as installing a package means accepting one of its distribution licenses, which is legally binding.
   By default, portage allows to install package with a free license (see [here](https://wiki.gentoo.org/wiki/License_Groups) or [wikipedia](https://en.wikipedia.org/wiki/Free_license) for some discussion on that topic),
   and package with a more restricting license, like `dev-java/oracle-jdk-bin` can be installed only if its license is explicitly accepted by the user.
   The LICENSE of `sudo` contains two elements: `ISC` and `BSD` (which are [GPL-Compatible](https://wiki.gentoo.org/wiki/License_Groups/GPL-COMPATIBLE)).
 - [**ACCEPT_LICENSE**](https://www.gentoo.org/glep/glep-0023.html)
   As we just discussed, it is possible to define the ACCEPT_LICENSE of a package to list the license terms the user accepts for that package.
   In portage, it is not necessary to accept any license to install `sudo`, but it is necessary to accept the `Oracle-BCLA-JavaSE` license to install `dev-java/oracle-jdk-bin`

**Remark**: at one point in the evolution of portage, ACCEPT_KEYWORDS did not exist and the only way to install a package was to directly change its KEYWORDS list (using the [/etc/portage/package.keywords](https://wiki.gentoo.org/wiki//etc/portage/package.accept_keywords) file).
Due to backward compatibility, this is still possible, which means that a user can both modify the KEYWORDS of a package, and its ACCEPT_KEYWORDS:
 consequently, it is possible in portage to make any package installable and stable.


### Installation

The installation of a package is characterized in portage by two main elements:
 - **SRC_URI**
   This variable lists the links from which the package implementation can be downloaded.
   For instance, the SRC_URI of `sudo` is
   ```
   SRC_URI=http://www.sudo.ws/sudo/dist/sudo-1.8.19p2.tar.gz ftp://ftp.sudo.ws/pub/sudo/sudo-1.8.19p2.tar.gz
   ```
 - [**installation functions**](https://devmanual.gentoo.org/ebuild-writing/functions/index.html)
   The developer of the package also defines a set of functions that implement the build process.
   In this documentation, we focus on the configuration of a package, not on its installation, and we invite the interested reader to look at the [documentation](https://devmanual.gentoo.org/ebuild-writing/functions/index.html).

### EAPI

The last important information in a package is its [`EAPI`](https://devmanual.gentoo.org/ebuild-writing/eapi/index.html)
 variable, that informs portage about syntax used in the package declaration and its content.
In particular, this variable is used for deciding which USE flags must be implicitly added to the package's `IUSE` variable.


## Configuration of a Package

Portage has a complex, layered system for configuring its packages.
Among all the information described in the previous section, only the
 `REQUIRED_USE`, `*DEPEND`, `SLOT` and `LICENSE` variables are not configurable.

For the sake of clarity, and because the way portage configures package is quite complex,
we structure our presentation in two main parts:
 [we first give an overview](#overview-per-variable) of the mechanisms used by portage to configure each information individually,
 and in a second step [we discuss how these mechanisms are implemented](#portage-layered-configuration) in the layered structure of portage's configuration system.

### Overview per Variable

#### IUSE

According to the [documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/ebuild.5.html),
 the declaration of a package's USE flags is done in each package declaration individually.
Here is an excerpt of the documentation:
> **IUSE**
>
> This should be a list of any and all USE flags that are leveraged within your build script.
> The only USE flags that should not be listed here are arch related flags (see KEYWORDS).
> Beginning with EAPI 1, it is possible to prefix flags with + or - in order to create default settings that respectively enable or disable the corresponding USE flags.
> For details about USE flag stacking order, refer to the USE_ORDER variable in make.conf(5).
> Given the default USE_ORDER setting, negative IUSE default settings are effective only for negation of repo-level USE settings, since profile and user configuration settings override them.

However, in reality, many USE flags, not only the ones that are arch related, are implicitly declared in two places:
 * a package's [eclasses](https://devmanual.gentoo.org/eclass-writing/index.html)
    implicitly declares USE flags for that package, like the different `python_target_*`, `ruby_target_*`, and other similar USE Flags.
   These implicit definitions are expanded into the `IUSE` variable by the [egencache tool](https://wiki.gentoo.org/wiki/Egencache).
   Hence, these implicitly added USE flags can be found in the files in [metadata/md5-cache](https://wiki.gentoo.org/wiki//usr/portage/metadata/md5-cache).
 * The `make.defaults` files in the [portage's profile](https://wiki.gentoo.org/wiki/Profile_(Portage)),
    are *bash<sup>1</sup>* script files (see [portage's manpage](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html))
    that implicitly declares system-wide USE flags (i.e., for all packages),
    like the different `kernel_*`, `elibc_*`, and other USE flags, including the arch-related ones.
   The [documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html)
    vaguely describes how several variables are involved in the implicit declaration of USE flags,
    but this description is not very precise and seems obsolete.
   We looked up the [actual implementation](https://github.com/gentoo/portage/blob/232a45d02e526ac4bdb4c5806432ff4b58d8cdc7/pym/portage/package/ebuild/config.py#L1852)
    of the IUSE variable construction to know how USE flags are implicitly declared in a `make.defaults` file,
    which depends on the package's EAPI variable.

<sup>1</sup>: More precisely, the `make.defaults` file supports a small subset of the bash scripting language,
 as described in the [`make.conf` documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/make.conf.5.html).
The actual parser of the `make.defaults` and similar files uses [shlex](https://docs.python.org/3/library/shlex.html)
 and is defined in [portage/util](https://github.com/gentoo/portage/blob/master/pym/portage/util/__init__.py)
 and in [portage/package/ebuild/config.py](https://github.com/gentoo/portage/blob/master/pym/portage/package/ebuild/config.py).

##### USE Flag Declaration for EAPI <= 4

We did not find any information on this subject in the portage documentation,
 so we describe how the [implementation](https://github.com/gentoo/portage/blob/232a45d02e526ac4bdb4c5806432ff4b58d8cdc7/pym/portage/package/ebuild/config.py#L1882) generates the list.

The USE flags are declared with the following variables:
 * `ARCH`: this variable contains the name of the architecture of the host machine (e.g., amd64), which is included in the list of declared USE flags
 * `PORTAGE_ARCHLIST`: this variables declares a list of architecture names, which are included in the list of declared USE flags
 * `USE_EXPAND_HIDDEN`: this variable contains a list of other variables names, themselves containing a list of USE flags to declare.
    This variable is thus expanded into a list of USE flags to declare, of the form`(lowercase(variable name))_(use flag)`
     where `variable_name` is an element of the list contained in  `USE_EXPAND_HIDDEN` and `use flag` is an element of the variable name's contained list.
 * `BOOTSTRAP_USE`: this variables contains a list of USE flag to declare for creating a bootstrap image of portage.
    These USE flags are also declared for the packages with an EAPI <= 4.

   **Example**
   ```
   ARCH="amd64"
   PORTAGE_ARCHLIST="amd64 x86"
   USE_EXPAND_HIDDEN="KERNEL ELIBC"
   KERNEL="linux"
   ELIBC="glibc"
   BOOTSTRAP_USE="cxx unicode"
   ```
   This declares the USE flags `amd64`, `x86`, `kernel_linux`, `elibc_glibc`, `cxx` and `unicode`.


##### USE Flag Declaration for EAPI >= 5

Such declaration is done by the mean of two variables:
 * the variable `IUSE_IMPLICIT` simply list USE flags to be declared.

   **Example**
   ```
   IUSE_IMPLICIT="prefix prefix-guest"
   ```
   This declares the USE flags `prefix` and `prefix-guest`.
 * the variable `USE_EXPAND_IMPLICIT` is more complex:
   it lists variables names that are expanded into USE flags lists to declare.
  The way a variable name is expanded is as follows:
   * if that variable name is listed in the variable `USE_EXPAND_UNPREFIXED`,
      the variable name, prefixed with `USE_EXPAND_VALUES_`, is directly expanded into its contained list
   * if instead that variable name is listed in the variable `USE_EXPAND`,
      the variable name, prefixed with `USE_EXPAND_VALUES_`, is expanded into a list of `(lowercase(variable name))_(use flag)`
      where `use flag` is an element of the variable name's contained list

     **Example**
     ```
     USE_EXPAND_IMPLICIT="KERNEL"
     USE_EXPAND="KERNEL"
     USE_EXPAND_UNPREFIXED="KERNEL"
     USE_EXPAND_VALUES_KERNEL="linux"
     ```
     This declares the USE flags `kernel_linux` and `linux`.


#### SELECTED_USE


As discussed before, the `SELECTED_USE` is not an explicit variable in portage and corresponds to
 the selected *product* of the package, i.e., the a set of its selected USE flags.
This product cannot be directly stated in portage, which instead uses five sets of USE flags to define the `SELECTED_USE`:
 - `use` is the base USE flag set
 - `use.force` is the set of USE flags that are always added to the package's `SELECTED_USE`
 - `use.stable.force` is the set of USE flags that are added to the package's `SELECTED_USE` only if it is stable
 - `use.mask` is the set of USE flags that are always removed from the package's `SELECTED_USE`
 - `use.stable.mask` is the set of USE flags that are removed from the package's `SELECTED_USE` only if it is stable

Note that the sets `use.*` are applied on `SELECTED_USE` in the order we described them.
In particular, the `*.mask` sets override all the USE flags added by the `*.force` sets.

**Example**
Consider the following USE flag sets for a stable package:
```
use = ssl berkdb gtk multilib
use.force = amd64 kernel-linux elibc-glibc
use.stable.force =
use.mask = multilib
use.stable.mask = python_targets_pypy
```
This results in the product `ssl berkdb gtk amd64 kernel-linux elibc-glibc`.


\
Portage constructs these five sets using what we call *USE flag set manipulation*.
Conceptually, every package starts with these sets empty, and then operations can be applied to them in order to modify them.
These operations are:
 - `U`: this operation adds the USE flag `U` in the set
 - `-U`: this operation removes the USE flag `U` from the set
 - `-*`: this operation empties the set

For instance, consider the following USE flag set manipulation, that removes `mysql`, adds `berkdb`, removes `kde` and adds `gtk`:
```
-mysql berkdb -kde gtk
```
Applying this set manipulation on the product `mysql ssl`, we get the product `ssl berkdb gtk`.
Note that the removal of a feature that is not present in the set (here `kde`) is silently skipped.


\
Finally, an important variable of an `make.defaults` bash scripts is `PROFILE_ONLY_VARIABLES`
 which expands into a list of USE flags that cannot be changed by the user,
 i.e., all attempts to select or unselect these USE flags by the user are simply discarded.
This variable is expanded in a similar fashion to `USE_EXPAND_IMPLICIT` (as discussed in the [IUSE section](#iuse)),
 but at one level higher than this variable (i.e., it can reference `IUSE_IMPLICIT`,
 `USE_EXPAND_IMPLICIT` or other variables that expand in a way or another into a list of USE flags).


#### KEYWORDS

As previously discussed, the `KEYWORDS` of a package can be modified, even if this functionality should be considered deprecated.
The modification is done via what we call *keyword set manipulation* that is a sequence of simple operation:
 - `K`: this operation adds the keyword `K` in the set
 - `*`: this operation adds all stable keywords to the set
 - `~*`: this operation adds all testing keywords to the set
 - `-K`: this operation removes the keyword `K` from the set (or does nothing if `K` is not present in the set)
 - `-*`: this operation empties the set

Note that the semantics of these operations is different from elements that can be used in the definition of the `KEYWORDS` variable itself.
For instance, the term `-*` can be used in the defintion of  `KEYWORDS`,
 but in this case this symbol does not empties the `KEYWORDS` set.
At the moment, we don't know the semantics of this symbol, as the [documentation](https://wiki.gentoo.org/wiki/KEYWORDS) is vague and our tests on the behavior of portage were not conclusive.

#### ACCEPT_KEYWORDS

The `ACCEPT_KEYWORDS` variable is manipulated in the same way as the `KEYWORDS`, with the same operations.

#### MASK

Similarly to the `SELECTED_USE`, the masked status of a package is defined from two sets of *atoms*:
 - [`mask`](https://wiki.gentoo.org/wiki/Knowledge_Base:Masking_a_package) lists the atoms (i.e., sets of packages) that are masked
 - [`unmask`](https://wiki.gentoo.org/wiki/Knowledge_Base:Unmasking_a_package) lists the atoms that are unmasked.

Hence, a package is masked if and only if there is an atom in the `mask` list that matches it, while no atom in the `unmask` list matches it.

**Example**
Consider the following sets:
```
mask: sys-fs/eudev sys-fs/udev sys-kernel/genkernel
umask: >=sys-kernel/genkernel-3.5.0.5
```
Here, all packages of the groups `sys-fs/eudev` and `sys-fs/udev` are masked,
 and so are the packages of the group `sys-kernel/genkernel` whose version is less than `3.5.0.5`.

\
As previously, portage constructs these sets by assuming them initially empty, and then applying user-defined *masking set manipulations* on them.
These operations are direct:
 - `A`: this operation adds the atom `A` in the set
 - `-A`: this operation removes the atom `A` from the set (or does nothing if `A` is not present in the set)


#### ACCEPT_LICENSE

As this variable is the responsibility of only the user (who accepts or not the license of a package in order to install it),
 this variable can only be stated (not modified) by the user, and contains the list of accepted licenses for this package.




### Portage Layered Configuration



We previously stated that the Portage configuration system is layered.
The different layers are described in the documentation of the [`USE_ORDER`](https://wiki.gentoo.org/wiki/USE_ORDER) variable that describes in which order these layers are applied.
Additionally, here is an excerpt of the [make.conf documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/make.conf.5.html) about `USE_ORDER`:

> **USE_ORDER** = "env:pkg:conf:defaults:pkginternal:repo:env.d"
>
> Determines the precedence of layers in the incremental stacking of the USE variable. Precedence decreases from left to right such that env overrides pkg, pkg overrides conf, and so forth.
>
> **warning**: Do not modify this value unless you're a developer and you know what you're doing. If you change this and something breaks, we will not help you fix it.
>
> * **env**: USE from the current environment variables (USE and those listed in USE_EXPAND)
> * **pkg**: Per-package USE from /etc/portage/package.use (see portage(5))
> * **conf**: USE from make.conf
> * **defaults**: USE from make.defaults and package.use in the profile (e.g. /etc/portage/make.profile/package.use) (see portage(5))
> * **pkginternal**: USE from ebuild(5) IUSE defaults
> * **repo**: USE from make.defaults and package.use in the repo's profiles/ top dir (e.g. /usr/portage/profiles/package.use) (see portage(5))
> * **env.d**: USE from the environment variables, such as LINGUAS, defined by files in /etc/env.d/

Hence, there are six layers, which we briefly describe, in their default loading order:
 * [**env.d**](https://wiki.gentoo.org/wiki/Handbook:X86/Working/EnvVar):
    this layer corresponds to the `/etc/env.d/` folder that contains files with many environment variables,
    some of them being possibly used to configure the packages in portage.
    But most of the variables stored in these files are related to system and software configuration,
    like the [default paths](https://wiki.gentoo.org/wiki/Handbook:X86/Working/EnvVar), the [system locale](https://wiki.gentoo.org/wiki/Localization/Guide), etc.
    Consequently, these variables may configure the installation process of the packages, bur rarely the packages themselves.
    \
    **Note 1**: gentoo assumes that these variables indeed do not configure the packages,
     and thus directly distributes in its main package repository the `egencache` files corresponding to these packages.
    If the `.ebuild` or `.eclass` files were to use the variables declared in `/etc/env.d/`, the `egencache` files would be erroneous.
    \
    **Note 2**: for a similar reason, gentoo assumes that the variable `USE_ORDER` always has its default value.
    Otherwise, as the files in the other layers (repo, defaults and pkg) may declare variables that can be used by the `.ebuild` and `.eclass` files,
    the `egencache` files distributed with the portage tree would be erroneous.
 * [**repo**](https://wiki.gentoo.org/wiki/Profile_(Portage)):
    this layer corresponds to the folder `/usr/portage/profiles/` that may contain several files for package configuration (use selection, mask, etc).
    We will discuss in detail these files in the [default profile section](default-profile).
 * [**pkginternal**](https://devmanual.gentoo.org/ebuild-writing/eapi/index.html):
    this layer corresponds to the default configuration stated in the package itself, declared in the `.ebuild` files and reported in the corresponding `egencache` files.
 * [**defaults**](https://wiki.gentoo.org/wiki/Profile_(Portage)):
    this layer corresponds to the user selected profile, usually specified by a simlink from `/etc/portage/make.profile` to a folder in the portage's profile tree.
    This profile is structured in a tree where each node is a folder containing several configuration files.
    We discuss this tree structure and the configuration files in the [user profile section](user-profile).
 * [**conf**](https://wiki.gentoo.org/wiki//etc/portage/make.conf):
    this layer corresponds to the [`/etc/portage/make.conf` file](https://wiki.gentoo.org/wiki//etc/portage/make.conf).
    The file documentation is quite complete, but it could be still be helpful to discuss which information it contains are relevant for package configuration and how they are integrated with the rest.
    This is briefly discussed in the [make.conf section](make-conf).
 * [**pkg**](https://wiki.gentoo.org/wiki//etc/portage):
    this layer corresponds to the user configuration of the packages, stored in the folder `/etc/portage`.
    The user configuration is structured in several files and folders that are discussed in the [user configuration section](user-configuration).
    We discuss the path is
    a user-defined file or folder containing several files declaring a USE flag selection for several *atoms* (i.e., sets of [packages]).
   As this/these file/s have the same structure as some in the profile, we will present its/their structure in a dedicated Section.
 * **env**: this layer corresponds to the `USE` variable available in the current environment, like in the following command line:
   ```
   USE="unicode -pcre" emerge -av sys-apps/less
   ```


#### Default Profile

The `/usr/portage/profiles/` folder contains many files and folders.
Some of these files (like [`use.desc`](https://wiki.gentoo.org/wiki/USE_flag)) discuss important information about portage.
Some folders (like `arcb` or `default`) store the data for the possible user-selected profiles.
We won't discuss these files and folder in detail here.

The default profile contains one configuration file for the package: [`package.mask`](https://wiki.gentoo.org/wiki//usr/portage/profiles/package.mask).
This file has the same structure as the `package.mask` files in the user profile and user configuration.
We thus discuss it more in detail [here](#package-masking).

#### User Profile

The user profile is set with a simlink [`/etc/portage/make.profile`](https://wiki.gentoo.org/wiki//etc/portage/make.profile)
 toward a user *profile* folder within the `/usr/portage/profiles/` folder.
The list of the user profiles and its selection can be accessed with the following commands:
```bash
eselect profile list # lists the user profiles
eselect profile set default/linux/amd64/13.0 # set the user profile
```

The [data of the user profile](https://wiki.gentoo.org/wiki/Profile_(Portage)) itself is thus contained in the portage tree and is structured in several files:
 * **parent**:
  This file lists the *parent* user profiles (or *subprofiles*) to this one.
  This means that to compute the package configuration defined by this profile,
   one must first iterate over all the folders listed in this file (one per line),
   compute the package configurations they define, combine them in order and add to the result the configuration stated in the current profile.
  \
  The way portage combines the package configurations is relatively simple:
   all the data in the profiles are described with *USE flag set manipulation*, *keyword set manipulation*, etc, which are combined as described previously.
 * **eapi**:
  This file contains one number corresponding to the EAPI validated by all the configuration files in this profile (see [portage manpage](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html)).
 * [**packages** / **packages.build**](#portage-core-packages):
  These two files describe (using *atoms*) the packages that are necessary for portage to work.
  We describe these files in detail in [their own section](#portage-core-packages).
 * [**make.defaults**](#makedefaults):
  This file declares several core information for portage.
  We describe this file in detail in [its own section](#makedefaults).
 * [**use.\***](#global-use-flags-selection):
  These files, together with some variables declared in [`make.defaults`](#makedefaults) construct the default USE flag selection globally for all packages.
  We describe these files in detail in [their own section](#global-use-flags-selection).
 * [**package.use\***](#per-package-use-flags-selection):
  These files enrich the global USE flag selection constructed by the previous files with per package configuration.
  We describe these files in detail in [their own section](#per-package-use-flags-selection).
 * [**package.mask** / **package.unmask**](#package-masking):
  These files declare which packages are masked and which are unmasked.
  These files are rather simple, but we still dedicate [a small section to them](#package-masking).
 * other files that are not directly related to package configuration (one is however related to *package installation* configuration).
  These files, together with the ones described in this document are described in the [portage manpage](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html).

All of these files but `parent` and `eapi` can have comments starting with a `#` character (like any `*sh` script files).


###### Portage Core Packages

The file `packages.build` is what we call an *package set manipulation* that lists all the packages that needs to be present in a gentoo stage 1 image.
An package set manipulation is similar to a USE flag set manipulation, but uses *atoms* to declare the required packages, with the semantics that an atom corresponds to *any* (not all) package that matches the atom.
We thus have the following operations:
 * `A`: this operation adds **any package** matching the atom `A` to the set
 * `-A`: this operation removes **all packages** matching the atom `A` from the set
 * `-*`: this operation empties the set

The file `packages` lists all the packages (i.e., *atoms*) that **must** be present in the system (like `sys-devel/gcc` or `sys-devel/make`).
Like the `packages.build` file, this file is a package set manipulation, with an additional syntactic construction to distinguish two sets of packages:
 * the `@system` set is manipulated by operations prefixed with `*`
 * the `@profile` set is manipulated by the other operations

Note that the `-*` operation empties the `@system` set as well as the `@profile` set.

**Note**: as these files are lists of *operations* (like the other configuration files in portage),
 the actual required package list can be computed in a hierarchical profile by concatenating all the `packages.build` (resp. all the `packages`) files together,
 and applying the operations iteratively on the empty set.

###### make.defaults

This file declares many core variables for configuring portage and its packages, like `ARCH` that states the architecture of the system.
Moreover, it is in this file that the implicit USE flags are declared, and the default USE flag selection for all packages is set.
We already discussed the definition of the implicit USE flags,
 so we now describe how the default USE flag selection is constructed.
Three variables are responsible for the construction of the USE flag selection in this file:
 * `USE`: this variable declares the USE flag set manipulation of this profile to construct the `use` USE flag selection that is common to all packages.
 * `USE_EXPAND`: this variable expands into a USE flag selection,
   in a similar manner to the `USE_EXPAND_IMPLICIT` variable for USE flag declaration,
   except that all the USE flags in the expanded list are prefixed.
   Note that additionally, the variables in the `USE_EXPAND` list can be prefixed by `-` sign to
    state that the USE flag in that variable must be unselected.
   \
   **Example**
   ```bash
   USE_EXPAND="KERNEL APACHE2_MODULES -INPUT_DEVICES"
   KERNEL="linux"
   APACHE2_MODULES="authn_core authz_core"
   INPUT_DEVICES="keyboard mouse"
   ```
   This defines the USE flag selection `kernel_linux apache2_modules_authn_core apache2_modules_authz_core -input_devices_keyboard -input_devices_mouse`.
 * `USE_EXPAND_UNPREFIXED`: this variable also expands in a USE flag selection,
    except that the expanded USE flags are not prefixed.
   \
   **Example**
   ```bash
   USE_EXPAND_UNPREFIXED="ARCH"
   ARCH=amd64
   ```
   This defined the USE flag selection `amd64`.


###### Global USE flags Selection

We just saw that the file [`make.defaults`](#makedefaults) is responsible to declare the `use` set of the USE flag selection that is common for all package.
The four other sets are declared in the following dedicated files:
 * `use.force`
 * `use.mask`
 * `use.stable.force`
 * `use.stable.mask`

These files declare USE flag set manipulations and follow the same syntax, with one operation per line.


###### Per Package USE flags Selection

In addition to the USE flag selection shared by all the packages,
 there are five files dedicated to declare the different sets for the USE flag selection specific for each package:
 * [`package.use`](https://wiki.gentoo.org/wiki//etc/portage/package.use):
   this file constructs the `use` set of the USE flag selection specific to each package.
   It lists a set of atoms, one per line,
    with its corresponding USE flag set manipulation on the same line.
   Note that atoms corresponds to sets of packages,
    and thus each line of this file defines a USE selection for a set of packages.
   Note also that two different atoms in this file could include a common package, which is thus configured twice.
   \
   **Example**
   ```
   # Globally disable the unwanted USE Flags which were enabled by the profile
   */* -bluetooth -consolekit -dbus -ldap -libnotify -nls -qt3support -udisks

   # enable the offensive USE flag for app-admin/sudo
   app-admin/sudo offensive

   # disable mysql support for dev-lang/php
   dev-lang/php -mysql

   # enable java and set the python interpreter version for libreoffice-5.1
   app-office/libreoffice java python_single_target_python3_4
   ```
 * `package.use.force`:
   this file constructs the `use.force` set of the USE flag selection specific to each package.
   Its syntax is identical to the one of `package.use`.
 * `package.use.mask`:
   this file constructs the `use.mask` set of the USE flag selection specific to each package.
   Its syntax is identical to the one of `package.use`.
 * `package.use.stable.force`:
   this file constructs the `use.stable.force` set of the USE flag selection specific to each package.
   Its syntax is identical to the one of `package.use`.
 * `package.use.stable.mask`:
   this file constructs the `use.stable.mask` set of the USE flag selection specific to each package.
   Its syntax is identical to the one of `package.use`.


###### Package Masking

As discussed [previously](#mask), the masking status of a package is defined by two sets of atoms:
 [`mask`](https://wiki.gentoo.org/wiki/Knowledge_Base:Masking_a_package) and
 [`unmask`](https://wiki.gentoo.org/wiki/Knowledge_Base:Unmasking_a_package).
The `mask` set is constructed by concatenating the content of the `package.mask` files in the profile hierarchy,
 each of them having listing the atoms to mask, one per line.
The construction of the `unmask` set is similar, with the `package.unmask` files.


#### make.conf

The [make.conf](https://wiki.gentoo.org/wiki//etc/portage/make.conf) file is one of the most common file to configure portage, and is thus very well documented.
In particular, it declares two imporant variables:
 * [`USE`](https://wiki.gentoo.org/wiki//etc/portage/make.conf#USE): a USE flag set manipulation that updates the `use` set of the USE flag selection.
 * [`ACCEPT_LICENSE`](https://wiki.gentoo.org/wiki//etc/portage/make.conf#ACCEPT_LICENSE): a list of accepted licenses accepted for every package.




#### User Configuration

The [user configuration](https://wiki.gentoo.org/wiki//etc/portage) can contain many information related to many aspects of portage.
Here, we will just focus on the package configuration, which is structured in two parts.

The first part is the `/etc/portage/profile` folder,
 which can contain the same files as the [user profile](#user-profile), except the `parent` file
 (if this file is present, it is not followed).
In particular, this gives the possibility to the user to declare implicit USE flags shared by all packages
 by defining a [`make.defaults`](#makedefaults) file
 (it is however useless as the packages will not use these flags in their configuration).

The second part is again very similar to an user profile,
 configuring the packages USE flag selection and its visibility
 with different configuration files and folders:
 * [**package.use**](https://wiki.gentoo.org/wiki//etc/portage/package.use):
  this element can either be a file (that follows the same syntax as the `package.use` file in the [user profile](#user-profile))
  or a folder containing an arbitrary number of file with arbitrary names, all of the them following the `package.use` file syntax.
  These files define the `use` set of the USE flag selection, and are combined in alphabetic order if there are several of them.
 * [**package.mask** / **package.unmask**](#package-masking):
  These elements, like for `package.use`, can be either files with the user profile `package.mask` syntax,
  or folders containing files with such syntax.
  They are used to construct the `mask` and `unmask` package set.
 * [**package.keywords** / **package.accept_keywords**](#package-keywording):
  These elements, like for `package.use`, can be either files with the user profile `package.keywords` syntax,
  or folders containing files with such syntax.
  That syntax follows the same principle as the other configuration files:
   they declare a [keyword set manipulation](#keywords), with one operation per line
   and are used to construct the `keywords` and `accept_keywords` variables for each package.
 * [**package.license**](https://wiki.gentoo.org/wiki//etc/portage/package.license):
  This file gives the accepted licenses per package:
   like for the `package.use` file, it lists a set of atoms, one per line,
   with its corresponding list of accepted licenses on the same line.
  \
  **Example** (from the documentation)
   ```
   # Accepting google-chrome license for www-client/google-chrome for version equal or greater than 42.0.2311.90_p1
   >=www-client/google-chrome-42.0.2311.90_p1 google-chrome

   # Accepting google-chrome license for any version of www-client/google-chrome
   www-client/google-chrome google-chrome

   # Accepting google-chrome license for every www-client package at any version
   www-client/* google-chrome

   # Accepting google-chrome license for every package at any version
   */* google-chrome

   # Accepting every license for every package at any version (not a good idea)
   */*  *
   ```











# Portage: Semantics

The semantics of the constraints in the `REQUIRED_USE` and the `*DEPEND` variables are in most part direct and well [documented](https://devmanual.gentoo.org/general-concepts/dependencies/index.html).
Three points are however not entirely covered in that documentation:
  few operators are not described, atom matching has some subtleties, and the corner cases of [USE dependencies](https://devmanual.gentoo.org/general-concepts/dependencies/index.html#built-with-use-dependencies) are not discussed.

### Constraint Operators

Two operators are missing from the main documentation, but are actually described in the [documentation about EAPI](https://devmanual.gentoo.org/ebuild-writing/eapi/index.html)

* `^^` is the xor operator (exactly one constraint in the following group must be satisfied),
* `??` is the one-max operator (at most one constraint in the following group can be satisfied).

### Atom Matching

The [documentation](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
 presents how to specify dependencies to other packages using atoms and informally discusses their semantics
 but does not go into details into the matching of version.
Indeed, package name must follow a naming convention described in the [ebuild file format documentation](https://devmanual.gentoo.org/ebuild-writing/file-format/index.html)
 where the syntax of version is explicitly stated to be *complicated*.
Consequently, comparing versions is difficult.

The syntax of versions is as follows:
```
VERSION ::= NUMBER ('.' NUMBER)* ( '_' SUFFIX)* ('-r' REVISION)?
NUMBER ::= digit+
SUFFIX ::= RELEASE_KIND NUMBER?
RELEASE_KIND ::= alpha | beta | pre | rc | p
REVISION ::= NUMBER
```

The following description of the Portage matching function is the result of our tests, and might be slightly erroneous.
Given two versions `v1` and `v2`, the matching function
 first splits these strings w.r.t. the separators '.', '_' and '-r'.
It then iterates over the two lists in parallel, and returns at the first point the two compared elements are different
  (we describes how the elements of the lists are pair-wise compared using python pseudo-code):
* `NUMBER_1` vs `NUMBER_2`: note that if the number start with `0`, they are considered fractional
  ```python
  if (NUMBER_1[0] == '0') or (NUMBER_2[0] == '0'):
    float_1 = float("0." + NUMBER_1)
    float_2 = float("0." + NUMBER_2)
    if float_1 < float_2: return "v1 is lesser than v2"
    elif float_1 > float_2: return "v1 is greater than v2"
  else:
    int_1 = int(NUMBER_1)
    int_2 = int(NUMBER_2)
    if int_1 < int_2: return "v1 is lesser than v2"
    elif int_1 > int_2: return "v1 is greater than v2"
  ```
* (`SUFFIX_1` or `REVISION_1`) vs `NUMBER_2`:
  ```python
  return "v1 is lesser than v2"
  ```
* `NUMBER_1` vs (`SUFFIX_2` or `REVISION_2`):
  ```python
  return "v1 is greater than v2"
  ```
* `RELEASE_KIND_1 NUMBER_1` vs `RELEASE_KIND_2 NUMBER_2`:
  ```python
  if RELEASE_KIND_1 != RELEASE_KIND_2:
    return "we have alpha < beta < pre < rc < p"
  else:
    if (NUMBER_1 != None) and (NUMBER_2 != None):
      int_1 = int(NUMBER_1)
      int_2 = int(NUMBER_2)
      if int_1 < int_2: return "v1 is lesser than v2"
      elif int_1 > int_2: return "v1 is greater than v2"
    elif NUMBER_1 != None:
      return "v1 is greater than v2"
    elif NUMBER_2 != None:
      return "v1 is lesser than v2"

  ```
* `RELEASE_KIND_1 NUMBER_1` vs  `REVISION_2`
  ```python
  return "v1 is lesser than v2"
  ```
* `REVISION_1` vs `RELEASE_KIND_2 NUMBER_2`:
  ```python
  return "v1 is greater than v2"
  ```
* `REVISION_1` vs `REVISION_2`:
  ```python
  int_1 = int(REVISION_1)
  int_2 = int(REVISION_2)
  if int_1 < int_2: return "v1 is lesser than v2"
  elif int_1 > int_2: return "v1 is greater than v2"
  ```

Our implementation of this comparison function (function `compare_version` in [core_data.py](https://github.com/HyVar/gentoo_to_mspl/blob/master/guest/hyvar/core_data.py))
 follows this description but compares each character of the versions individually for efficiency.

### Semantics of USE dependencies

Consider the constraint syntax in the DEPEND variable of a package, as described in [portage documentation](https://devmanual.gentoo.org/general-concepts/dependencies/).
This syntax, starting from EAPI=2, allows for USE dependencies,
 i.e., when specifying a dependency, one can specify which USE flags must be selected or unselected for that dependency.
The documentation is clear for simple examples:
 for instance `app-misc/foo[bar,-baz]` means that `app-misc/foo` must be installed with the use flag `bar` selected, and `baz` unselected.

However, when the constraints  mixes *compact forms* and *use dependency defaults*, the documentation fails to describes what they mean.
Hence, we list here how use dependencies in portage can be translated in unambiguous constraints.
We consider the following:
 - the USE flag in the selection is called `my-feature`
 - the predicate corresponding to this USE flag being selected in the local package, if it exists, is `feature-local`
 - the predicate corresponding to this USE flag being selected in the external package, if it exists,  is `feature-external`


**1. If the USE flag `my-feature` is present in the external package**

| Selection | Constraint |
|-----------|------------|
| `my-feature` , `my-feature(+)` , `my-feature(-)` | `feature-external`|
| `-my-feature` , `-my-feature(+)` , `-my-feature(-)` | `not feature-external` |
| `my-feature?` , `my-feature(+)?` , `my-feature(-)?` | `feature-local => feature-external` |
| `!my-feature?` , `!my-feature(+)?` , `!my-feature)(-)?` | `(not feature-local) => (not feature-external)` |
| `my-feature=` , `my-feature(+)=` , `my-feature(-)=` | `feature-local <=> feature-external` |
| `!my-feature=` , `!my-feature(+)=` , `!my-feature(-)=` | `feature-local <=> (not feature-external)` |


**2. If the USE flag `my-feature` is *NOT* present in the external package**

| Selection | Constraint |
|-----------|------------|
| `my-feature` , `-my-feature` , `my-feature(-)` , `-my-feature(+)` | `FALSE`|
| `my-feature(+)` , `-my-feature(-)` | `TRUE` |
| `my-feature?` , `!my-feature?` , `my-feature=` , `!my-feature=` | `FALSE` |
| `my-feature(+)?` | `TRUE` |
| `my-feature(-)?` | `not feature-local` |
| `!my-feature(+)?` | `feature-local` |
| `!my-feature(-)?` | `TRUE` |
| `my-feature(+)=` , `!my-feature)(-)=`| `feature-local` |
| `my-feature)(-)=` , `!my-feature(+)=` | `not feature-local` |



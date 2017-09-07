# Portage: an Overview

[Portage](https://wiki.gentoo.org/wiki/Portage) ([wikipedia](https://en.wikipedia.org/wiki/Portage_(software))) is the package manager of the [Gentoo](https://gentoo.org/) Linux distribution.


## Core Principles

The main characteristics of portage, compared to other package manager, is that its packages are distributed as source code (when possible),
 which can be configured by the machine's administrator, prior to compilation and installation of the package.
Portage contains a unified interface for configuring the package, called [USE flags](https://wiki.gentoo.org/wiki/Handbook:AMD64/Working/USE).
The documentation is a bit unclear: USE flags are *features* giving an [SPL](https://en.wikipedia.org/wiki/Software_product_line) structure to all of the portage's packages.

#### Portage's Repository Structure

Portage declares its package in [*.ebuild*](https://devmanual.gentoo.org/ebuild-writing/index.html) files.
These files are structured in a folder structure of the following form:
```
/usr/portage/ +
              |
              +-> category / +
                             |
                             +-> group / +
                                         |
                                         +-> group-version.ebuild
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
 * `REQUIRED_USE`: this variable declares a constraint on the package's USE flag, thus defining the local feature model of this SPL
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

###### Feature Model Syntax

As discussed previously, the Feture Model of a Portage package is declared with six variables:
 * `IUSE` lists the features of the feature model
 * `REQUIRED_USE` defines the *local* part of the feature model
 * `DEPEND`, `RDEPEND` and `PDEPEND` define the *dependency* part of the feature model

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
   No notion of feature model or code interface is associated to this low level notion of SPL interface.
 * `SELECTION` is the portage's way to specify a *partial product* for a package's dependency.
   Like for atoms, we won't go in details into the syntax of partial product,
    we just want to point our that it can select or require unselected some features,
    with such feature selection possibly guarded by some local feature being selected or unselected.

For more information about the `*DEPEND` variables, you can look at the [documentation](https://devmanual.gentoo.org/general-concepts/dependencies/index.html)
 and the full semantics of [full semantics of partial product specification](#semantics-of-use-flags-selection-in-constraints).


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



# Portage: Some Technical Information

In this section, we give a brief and precise summary of many information scattered in the portage's documentation,
 and that is essential to correctly compute a valid portage configuration.
In some cases, the information presented here are the result of exhaustive testing,
 as the available documentation did not describe the behavior of portage in certain cases.

## USE Flags Declaration and Selection

USE Flag declaration and selection is a core part of portage, as presented in its [documentation](https://wiki.gentoo.org/wiki/USE_flag).
They are the core of a package configuration during its installation.
However, the documentation of the use flag is ambiguous and quite unclear on some aspects of the use flags.
Hence, we present here a detailed documentation on two aspects of the portage use flags:
 * how the use flags are declared
 * how packages are configured using these use flags

### USE Flag Declaration


According to the [documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/ebuild.5.html),
 the USE flag declaration (called IUSE), is mostly done in each package declaration individually.
Here is an excerpt of the documentation:
> **IUSE**
>
> This should be a list of any and all USE flags that are leveraged within your build script.
> The only USE flags that should not be listed here are arch related flags (see KEYWORDS).
> Beginning with EAPI 1, it is possible to prefix flags with + or - in order to create default settings that respectively enable or disable the corresponding USE flags.
> For details about USE flag stacking order, refer to the USE_ORDER variable in make.conf(5).
> Given the default USE_ORDER setting, negative IUSE default settings are effective only for negation of repo-level USE settings, since profile and user configuration settings override them.

However, in reality, many USE flags, not only the ones that are arch related, are implicitly declared in two places:
 * a package's [eclasses](https://devmanual.gentoo.org/eclass-writing/index.html),
    implicitly declares USE flags for that package, like the different `python_target_*`, `ruby_target_*`, and other similar USE Flags.
   These implicit definitions are expanded into the `IUSE` variable by the egencache tool,
    and so we can simply use the files in [metadata/md5-cache](https://wiki.gentoo.org/wiki//usr/portage/metadata/md5-cache)  (like `emerge` does)
    to get all these USE flags, in addition to the ones explicitly declared by the package.
 * The `make.defaults` files in the [portage's profile](https://wiki.gentoo.org/wiki/Profile_(Portage)),
    are *bash<sup>1</sup>* script files (see [portage's manpage](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html))
    that implicitly declares system-wide USE flags (i.e., for all packages),
    like the different `kernel_*`, `elibc_*`, and other USE flags, including the arch-related ones.
   The [documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html)
    vaguely describe how several variables are involved in the implicit declaration of USE flags,
    however it does not corresponds to the reality.
   I actually had to look up the [actual implementation](https://github.com/gentoo/portage/blob/232a45d02e526ac4bdb4c5806432ff4b58d8cdc7/pym/portage/package/ebuild/config.py#L1852)
    of the IUSE variable construction to know how USE flags are implicitly declared.

#### USE Flag Declaration in a `make.defaults` file

This file declares two sets of USE flags,
 one for the packages with EAPI equal or lower than 4
 and one for the packages with EAPI equal or greater than 5.

##### USE Flag Declaration for EAPI <= 4

We did not find any information on this subject in the portage documentation,
 so I describes how the [implementation](https://github.com/gentoo/portage/blob/232a45d02e526ac4bdb4c5806432ff4b58d8cdc7/pym/portage/package/ebuild/config.py#L1882) generates the list.

The USE flags are declared with the following variables:
 * `ARCH`: this variable contains the name of the architecture of the host machine (e.g., amd64), which is included in the list of declared USE flags
 * `PORTAGE_ARCHLIST`: this variables declares a list of architecture names, which are included in the list of declared USE flags
 * `USE_EXPAND_HIDDEN`: this variable contains a list of other variables names, themselves containing a list of USE flags to declare.
    This variable is thus expanded into a list of USE flag to declare, of the form`(lowercase(variable name))_(use flag)`
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

   Another important variable of an `make.defaults` bash scripts is `PROFILE_ONLY_VARIABLES`
    which expands into a list of USE flags that cannot be changed by the user,
    i.e., all attempts to select or unselect these USE flags by the user are simply discarded.
   This variable is expanded in a similar fashion to `USE_EXPAND_IMPLICIT`,
    but at one level higher than this variable (i.e., it can reference `IUSE_IMPLICIT`,
    `USE_EXPAND_IMPLICIT` or other variables that expand in a way or another into a list of USE flags).

   Finally, portage's profile contains several `make.defaults` files.
   The ones that are considered in the declaration of the USE flags depends on the profile configuration,
    as discussed in the [documentation](https://wiki.gentoo.org/wiki/Profile_(Portage)).


<sup>1</sup>: More precisely, the `make.defaults` file supports a small subset of bash-like terminal language,
 as described in the `make.conf` [documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/make.conf.5.html).
The actual parser of the `make.defaults` and similar files uses [shlex](https://docs.python.org/3/library/shlex.html)
 and is defined in [portage/util](https://github.com/gentoo/portage/blob/master/pym/portage/util/__init__.py)
 and in [portage/package/ebuild/config.py](https://github.com/gentoo/portage/blob/master/pym/portage/package/ebuild/config.py).


### Package Configuration with Use Flags

While the USE flags declaration in portage is quite intricate,
 the USE flag selection (i.e., stating for which package which USE flag is selected and which is not)
 is even more complex.
This complexity is caused by three interacting properties of USE flag Selection:
 * they can be combined: several USE selections for the same package can be declared in several places, and are combined somehow to define the actual USE flag selection of that package
 * they can affect several packages: depending on where and how they are specified, USE flag selections can be system-wide, only for one package, or for a specific set of packages
 * they can include USE flags that are not declared in the configured package:
    for instance, system-wide USE flag selection can select a large amount of USE flags, and only few of them are present in each individual package.
   In such case, the additional USE flags in the selection are simply not considered during the computation of the packages' configurations.

We consequently structure the presentation of Package Configuration in two parts:
 * where the USE flag selection can be defined
 * how they are combined to build the configuration of each package


#### USE Flag Selection Declaration

A global overview of where USE flag selections are declared can be found in
 the [make.conf documentation](https://dev.gentoo.org/~zmedico/portage/doc/man/make.conf.5.html)
 that describes the [`USE_ORDER`](https://wiki.gentoo.org/wiki/USE_ORDER) variable.
Here is an excerpt of the documentation:
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

Hence, there are six general locations in which USE flag selections can be specified.
Moreover, these locations are ordered (with the `USE_ORDER` variable),
 thus partially specifying the order in which the different USE flag selections are combined.

Let briefly overview these locations, in their loading order:
 * [**env.d**](https://wiki.gentoo.org/wiki/Handbook:X86/Working/EnvVar): this folder sets many environment variables,
    including some that are used to construct the USE flag selections.
   These variables are loaded system-wide, and we don't need to explicitly manage them.
 * [**repo**](https://wiki.gentoo.org/wiki/Profile_(Portage)):
    the folder `/usr/portage/profiles/` may contain several files that define some USE flag selections.
   These files follow the structure of the rest of the portage's profile,
    which is quite complex and will be discussed in detail in its own section.
 * [**pkginternal**](https://devmanual.gentoo.org/ebuild-writing/eapi/index.html): 
    the IUSE defaults is the USE flag selection extracted from the package's IUSE variables
    (from the `+` and `-` annotation on its USE flags).
   This is the default USE flag selection of the package, specified by the package's maintainer.
 * [**defaults**](https://wiki.gentoo.org/wiki/Profile_(Portage)): this corresponds to the user selected profile,
    usually specified by a simlink from `/etc/portage/make.profile` to a folder in the portage's profile tree.
   As for the **repo** location, many files are considered to construct the USE flag selection of this location,
    which will be discussed in detail later in its own section.
 * [**conf**](https://wiki.gentoo.org/wiki//etc/portage/make.conf):
 * [**pkg**](https://wiki.gentoo.org/wiki//etc/portage/package.use): the `/etc/portage/package.use` path is
    a user-defined file or folder containing several files declaring a USE flag selection for several *atoms* (i.e., sets of [packages]).
   As this/these file/s have the same structure as some in the profile, we will present its/their structure in a dedicated Section.
 * **env**: this corresponds to the `USE` variable available in the current environment, like in the following command line:
   ```
   USE="unicode -pcre" emerge -av sys-apps/less 
   ```

##### USE Flag Selection Declaration in Profile

The USE flag selection done in the two parts from the portage profile (**repo** and **defaults**)
 is based on a similar file structure.
The difference is that the **defaults** part is recursive, based on the `parent` file,
 as described in the [documentation](https://wiki.gentoo.org/wiki/Profile_(Portage).)

We structure he presentation of the files that take part in the USE flag selection in the profile
 in three parts: the Core files, the force and mask files, and the Stable files.

###### Core Files

 * `make.defaults`: we already discussed this file in the USE flag declaration section,
    and this file is also used to declare system-wide USE flag selection, based on other bash variables.
   Two variables are responsible for the construction of the USE flag selection in this file:
    * `USE_EXPAND`: this variable expands into a USE flag selection,
      in a similar manner to the `USE_EXPAND_IMPLICIT` variable for USE flag declaration,
      except that all the USE flags in the expanded list are prefixed.
     Note that additionally, the variables in the `USE_EXPAND` list can be prefixed by `-` sign to
      state that the USE flag in that variable must be unselected.

      **Example**
      ```
      USE_EXPAND="KERNEL APACHE2_MODULES -INPUT_DEVICES"
      KERNEL="linux"
      APACHE2_MODULES="authn_core authz_core"
      INPUT_DEVICES="keyboard mouse"
      ```
      This defines the USE flag selection `kernel_linux apache2_modules_authn_core apache2_modules_authz_core -input_devices_keyboard -input_devices_mouse`.
    * `USE_EXPAND_UNPREFIXED`: this variable also expands in a USE flag selection,
       except that the expanded USE flags are not prefixed.

      **Example**
      ```
      USE_EXPAND_UNPREFIXED="ARCH"
      ARCH=amd64
      ```
      This defined the USE flag selection `amd64`.
 * `use`: this file states a system-wide USE flag selection,
    by simply listing USE flags to be selected.
   The list is constructed with only one (possibly guarded) USE flag per line.
   Note that there is a way to remove an element from this list,
    by declaring a USE flag guarded by a `-` sign.
 * [`package.use`](https://wiki.gentoo.org/wiki//etc/portage/package.use):
    this file lists a set of atoms, one per line,
    with its corresponding USE flag selection (i.e., a list of possibly guarded USE flags) on the same line.
   Note that atoms corresponds to sets of packages,
    and thus each line of this file defines a USE selection for a set of packages.
   Note also that two different atoms in this file could include a common package, which is thus configured twice.

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

###### Force and Mask Files

In addition to the previously presented files, a profile folder can contain
 other files with a syntax identical to the ones of the `use` and `package.use` files,
 and a very similar semantics:
 * `use.force`: identical to `use`
 * `use.mask`: similar to `use`, but with an opposite semantics.
   The constructed list corresponds to the USE flags that must be unselected.
   This list override declarations made in `use` and `use.force`.
 * `package.use.force`: it has a similar semantics of `use.force`
    (i.e., the `-` sign just states that the guarded USE flag is removed from the selected list),
    but per atom.
   This file override declarations made in `package.use`
 * `package.use.mask`: opposite to `package.use.force`
   This file override declarations made in `package.use.force`

 TODO: write a complete example


###### Stable Files

The previously discussed `use*` and `package.use*` have yet another variation:
 `use.stable.force`, `use.stable.mask`, `package.use.stable.force` and `package.use.stable.mask`.
These files follows the same syntax of `use` and `package.use` respectively,
 and have the same semantics of the files without the `stable` annotation,
 except that they apply only on packages that are stable (i.e., with a stable keyword),
 as discussed in the [portage man page](https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html):

> Beginning with **EAPI 5**, new USE configuration files are supported:
> use.stable.mask, use.stable.force, package.use.stable.mask and package.use.stable.force.
> These files behave similarly to previously supported USE configuration files,
> except that they only influence packages that are merged due to a stable keyword.


###### USE Flag Selection Combination in Profile



So, the first tests I did shown that the files in a profile layer are managed separately.
Between layers, the files of the same category are combined.
Then, the resulting configuration are combined in the end.

So, we have a configuration is a sub profile that is -everything
in parallel, we have a use.force that sets two variables to true

so, we have on one layer package.use < use.force < package.use.force < use.mask

I need to test all interactions between these different files, and also the profile recursive structure.

Hence, I need to
 - add `my_feature1` and `my_feature2` in an `IUSE_IMPLICIT`
 - check, with `dev-vcs/my-svn` if these features are indeed declared.
   Hmm, to be able to see them, we need to have the variable `PROFILE_ONLY_VARIABLES` is set correctly.
   Maybe I could create a dummy profile that does exactly what I want
 -


 - test the semantics of .stable.


In portage, the use flags manipulation (declaration and selection) is not very clear.
The default use flags declaration and selection is done locally to every package,
  which declare its own use flags, and specify its own default use flag selection.
These default use flag selection can be updated by the user, by filling a [package.use](https://wiki.gentoo.org/wiki//etc/portage/package.use) file.
These two parts are clear.

The not so clear use flag manipulation in portage is
Additionally, portage itself manipulates the use flags of

In the portage profile tree, there are several files that manipulate use flags:
 - `use.force`: globally sets the use flags in this file to be positively selected
 - use.mask: globally sets the use flags in this file to be negatively selected
 - package.use: same as package.use in /etc/portage
 - package.use.force:
 - package.use.mask:
 - package.use.stable.force:
 - package.use.stable.mask:
 - make.defaults: this is actually where default use flags are declared

files `*.stable.*` are configuration files that only affect package with a stable (i.e., not `~`)keyword.

In the previous items,
 `positively selected` meant that the use flag is selected (or unseletected if guarded by -) for every packages that contain it;
 `negatively selected` meant that the use flag is unselected (or seletected if guarded by -) for every packages that contain it;


#### USE Flag Selection Combination
TODO: structure these data in an understandable way.

well, the structure of this document is not perfect, as the composition of the information is global to a profile, and thus include information about use selection, but also per package use selection and package masking.
Any way, as I discovered, there are three layers of profiles: the root profile (/usr/portage/profiles/, non hierarchical), the default profile (/etc/portage/make.profile, hierarchical) and the user profile (/etc/portage/profile/, non hierarchical).

All these profiles are combined before being applied to the packages:
 the set construction (e.g., removal of element from package.mask) does transfer from one profile to the other.

The manipulation of package.accept_keywords is quite strange, to say the least.
Well, ok, I think I understand:
 - `KEYWORDS` is the list of architecture that is supported by the package.
   In principle, it can be modified by package.keywords files (which, again, works as a list manipulation file),
    but in practice, it may be mistaken as an `package.accept_keywords` file
 - `ACCEPT_KEYWORDS` is the list of keywords that the local architecture accepts to allow the installation of a package.
   By default, this list is contained in the `ACCEPT_KEYWORDS` variable, and can be set per package in the files `package.accept_keywords`,
     which, again, works as a list manipulation file (that manipulate the `ACCEPT_KEYWORDS` variable for each package independently).
   A package is considered unstable if its `ACCEPT_KEYWORDS` list contains an unstable keyword.
 A package can be installed if its list of keywords, intersected with its accepted keywords, is non empty.


**Note that the list manipulation of accepted keywords accepts `-*` ** to remove all elements of the list.
Does other list manipulation work in the same way (e.g., package.use, use.force)?
Nope. package.\* does not accept `*/*` atoms either.

I still need to check with package.keywords and package.accept_keywords:
 - `-*` works in package.accept_keywords
 - `-*` works in package.keywords


package.use package.use.force package.use.mask

## Package Visibility

### Package Masking

package.unmask is applied after package.mask

### Package Keywords



## Semantics of Use Flags Selection in Constraints

Consider the constraint syntax in the DEPEND variable of a package, as described in [portage documentation](https://devmanual.gentoo.org/general-concepts/dependencies/).
This syntax, starting from EAPI=2, allows for Use dependencies, i.e., when specifying a dependency, one can specify which use flags must be selected or unselected for that dependency.
The documentation is clear for simple examples:
 for instance `app-misc/foo[bar,-baz]` means that `app-misc/foo` must be installed with the use flag `bar` selected, and `baz` unselected.

However, when the constraints  mixes *compact forms* and *use dependency defaults*, the documentation fails to describes what they mean.
Hence, we list here how use dependencies in portage can be translated in unambiguous constraints.
We consider the following:
 - the use flag in the selection is called `my-feature`
 - the predicate corresponding to this feature in the local package, if it exists, is `feature-local`
 - the predicate corresponding to this feature in the external package, if it exists,  is `feature-external`


**1. If use flag is present in the external package**

| Selection | Constraint |
|-----------|------------|
| `my-feature` , `my-feature(+)` , `my-feature(-)` | `feature-external`|
| `-my-feature` , `-my-feature(+)` , `-my-feature(-)` | `not feature-external` |
| `my-feature?` , `my-feature(+)?` , `my-feature(-)?` | `feature-local => feature-external` |
| `!my-feature?` , `!my-feature(+)?` , `!my-feature)(-)?` | `(not feature-local) => (not feature-external)` |
| `my-feature=` , `my-feature(+)=` , `my-feature(-)=` | `feature-local <=> feature-external` |
| `!my-feature=` , `!my-feature(+)=` , `!my-feature(-)=` | `feature-local <=> (not feature-external)` |


**2. If use flag is NOT present in the external package**

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



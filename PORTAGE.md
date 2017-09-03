# Portage: Some Technical Information

In this document, we give a brief and precise summary of many information scattered in the portage's documentation,
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
   Such declaration is done by the mean of different variables:
    * the variables `IUSE_IMPLICIT`, `USE_EXPAND_VALUES_ARCH`, `USE_EXPAND_VALUES_ELIBC`,
       `USE_EXPAND_VALUES_KERNEL` and `USE_EXPAND_VALUES_USERLAND` simply list USE flags to be declared.

       **Example**
       ```
       IUSE_IMPLICIT="prefix prefix-guest"
       USE_EXPAND_VALUES_USERLAND="BSD GNU"
       ```
       This declares the USE flags `prefix`, `prefix-guest`, `BSD` and `GNU`.
    * the variable `USE_EXPAND_IMPLICIT` is more complex:
       it lists variables names that are expanded into USE flags lists to declare.
      The way a variable name is expanded is as follows:
       * if that variable name is listed in the variable `USE_EXPAND_UNPREFIXED`,
          the variable name is directly expanded into its contained list
       * if instead that variable name is listed in the variable `USE_EXPAND`,
          the variable name is expanded into a list of `(lowercase(variable name))_(use flag)`
          where `use flag` is an element of the variable name's contained list

         **Example**
         ```
         USE_EXPAND_IMPLICIT="ARCH KERNEL"
         USE_EXPAND="KERNEL OTHER_UNRELATED_VARIABLES"
         USE_EXPAND_UNPREFIXED="ARCH YET_OTHER_VARIABLES"
         ARCH="amd64"
         KERNEL="linux"
         ```
       This declares the USE flags `amd64` and `kernel_linux`.

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
    by simply listing USE flags to be selected, or unselected if guarded with a `-` sign.
   The list is constructed with only one (possibly guarded) USE flag per line.
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
    app-office/libreoffice java PYTHON_SINGLE_TARGET: python3_4
    ```

###### Force and Mask Files


###### Stable Files


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



## Package Visibility

### Package Masking


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
| `my-feature?` , `my-feature(+)?` , `my-feature)(-)?` | `feature-local => feature-external` |
| `!my-feature?` , `!my-feature(+)?` , `!my-feature)(-)?` | `(not feature-local) => (not feature-external)` |
| `my-feature=` , `my-feature(+)=` , `my-feature)(-)=` | `feature-local <=> feature-external` |
| `!my-feature=` , `!my-feature(+)=` , `!my-feature)(-)=` | `feature-local <=> (not feature-external)` |


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



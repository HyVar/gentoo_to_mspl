# hyvar for reconfiguring gentoo


This tool allows for a correct and complete dependency resolution in portage,
 thus giving a correct list of packages to for emerge to install and uninstall,
 with a correct use flag configuration.

This tool works by abstracting the portage tree and user configuration
 (the files in /etc/portage) into some core data, that are then combined with the user request to solve the dependencies.
The list of packages to instal and uninstall are saved in a bash script, and the use flag configuration is saved in a package.use file.

This work is based on the theory of Software Product Line and Multi-Software Product Line,
 and the fact that portage is a Multi-Sofware Product Line


## Tool Usage

Our tool consider two computers or VM:
 - the guest VM hosts the managed gentoo OS. The core data is extracted from there, and the bash installation script is executed there
 - the host VM hosts the main computation of the core data and the dependency resolution. It can be any OS with
    1. ssh
    2. rsync
    3. python 2.7
    4. python 2.7 packages: click, lrparsing, z3-solver

All the functionalities of this tool can be accessed from the hyportage.sh bash script at the root of this repository.
The functions are:
 - `hyportage.sh setup_guest`: install extraction scripts in the guest VM.
 - `hyportage.sh sync_guest`: extracts the data from the guest VM.
 - `hyportage.sh clean_guest`: removed the installed scripts from the guest VM.
 - `hyportage.sh setup_host`: creates the correct folder structure in the host to store the data. This must be executed before `sync_guest`
 - `hyportage.sh translate`: translate the portage tree and the user data into our internal representation
 - `hyportage.sh emerge`: acts like gentoo's `emerge -p`, except that it generates a installation script and a package.use file
<!-- - `hyportage.sh install`: copy the generated installation script and package.use file to the guest VM, and executes the scripts, thus performing the installation. -->



## Structure of the repository:


Note that this structure is configurable in the main script hyportage.sh

* hyportage.sh: the main script of this implementation. documentation of the commands is included
* guest/hyvar: contains the script to save in the gentoo VM
    1. clean.sh: clean the guest VM off the installed scripts
    2. setup.sh: bash script to setup the right environment for the scripts
    3. load_make_defaults.sh: bash script to load a make.defaults or make.conf portage file
    4. core_data.py: core data structures used in our tool
    5. extract_portage.py: main script that extract variability information from the portage packages, and store them in a local folder

* host: contains the code needed for the translation and computation of the new configuration
   - data: this folder contains the data extracted and translated from the gentoo VM
      * portage: contains all the data extracted from the guest gentoo VM
         1. packages/portage-tree: a copy of the egencache folder of the portage repository
         2. packages/deprecated: generated egencache files from the installed packages that are not available in portage anymore
         3. config.pickle: pickle file containing all information concerning the VM portage configuration:
           1. the configuration done by the portage's profile and the user, including the use flag selection, the package masks and keywords.
              Licenses are not considered at the moment.
           2. the list of packages that are installed on the guest VM, with the selected use flags
           3. the world list and the package sets (declared in the profile and by the user)
      * hyportage: contains our translation of the gentoo packages with information related to their variability, and some annex useful data
        1. hyportage.pickle: pickle file that contains the translated packages and their visibility status
   - scripts: contains all the scripts for translating portage into hyportage, and for installing new packages.
      In particular:
      * hyportage.py: is the main python script, responsible for both translating the data extracted from portage into our hyportage encoding, and for computing a nnew connfiguration from a user request
      * hyportage_translation.py: contains the necessary functions for translating portage into hyportage
      * reconfigure.py: contains the necessary functions for computing a new configuration from the user request



## Usage Example

### Prepare the Gentoo VM

For this example we consider the Gentoo VMs available from https://www.osboxes.org/gentoo/

In particular the system was tested with Gentoo 201703 (CLI Minimal) - 64bit.

Our script will use ssh to connect to the VM. For this reason sshd demon needs to be started on the VM.
To do so please make sure that sshd is started and if not run the following command:
```
sudo service sshd start
```

Note that the credential to use the VM are the following:
``` 
Username: osboxes
Password: osboxes.org
Password for Root account: osboxes.org
```

To access the machine for the remaing of the running example we assume that it could be reached with the ssh protocol
at port 9022 (if VirtualBox is used this can be configured with a port forwarding).
Please verity to have access to the VM. As example this can be obtained as follows:
```
ssh -p 9022 -o PubkeyAuthentication=no osboxes@localhost
```

If the VM is reachable then run the following command that will install the necessary script in the VM:
```
./hyportage.sh setup_guest
```



### Getting data from the VM

To get the required information from the VM please run the following scripts:
```
bash hyportage.sh sync_guest
```

This script copies to the host VM the package data (in the [egencache](https://wiki.gentoo.org/wiki/Egencache) format),
 extracts to the host VM relevant information from the [VM's profile](https://wiki.gentoo.org/wiki/Profile_(Portage)) and from the [user configuration](https://wiki.gentoo.org/wiki//etc/portage),
 and extracts to the host VM the list and use flags configuration of the installed packages.

Note that if an installed package is deprecated (i.e., it is not in the portage tree anymore),
 this script regenerate a egencache file for it, so this package can still be considered in our tool.



### Translating the data into hyportage format

The next step is to translate the egencache files and the extracted data into our hyportage encoding.
This is done by executing
```
bash hyportage.sh translate
```

This script can take several minutes to complete.


This script have several options:
 * `-v`: verbose mode. The verbosity of the tool can be increased by having several instances of this option (`-vvv` is for debugging)
 * `-p`: parallel mode. This option takes in parameter how many process to use, and parallelizes the loading of the egencache files

Typically, for a verbose execution of the script on a 4 core processor, one runs:
```
bash hyportage.sh translate -vvv -p 3
```



### Computing a new Configuration

As discussed before, the function to compute a new configuration is `emerge` and can be called similarly to the portage `emerge` tool, without its options:
```
bash hyportage.sh emerge <list of atoms to install>
```

or
```
bash USE="use flag selection" hyportage.sh emerge <list of atoms to install>
```
Note that the atoms in parameter must be qualified with the package category.
For instance, `www-servers/apache` is accepted while `apache` is not.

However, our tool have additional very important options that we discuss below.

#### External Solver Configuration

The computation of a new configuration uses an external solver called [hyvar-rec](https://github.com/HyVar/hyvar-rec).
By default, our tool suppose that the executable `hyvar-rec` can be called, but two options can change this behavior:
 1. `--local-solver 'command'` specifies the command to call the solver on the local computer.
    It can be useful when it is not possible to create an `hyvar-rec` executable (on windows for instance).
    For instance, one can specify a command that directly execute the hyvar-rec.py file with python:
    ```
    bash hyportage.sh emerge -vvv  --local-solver 'python C:\Users\user\git\hyvar-rec\hyvar-rec.py' www-servers/apache
    ```
    Note that the paths in the command cannot contain spaces
 2. `--hyvarrec-url` specifies the url of an hyvar-rec server.

#### Exploration

By default, our tool installs only installable packages (that are stable and not masked) with the use flag configuration as specified by the user.
However, the `--exploration` option allow our tool to be more flexible.
This option takes in parameter a list of exploration mode to consider:
  - **use**: this mode allows the tool to change the use flag configuration of the packages
  - **keywords**: this mode allows the tool to consider also packages that are unstable or that cannot be installed in the specified architecture
  - **mask**: this mode allows the tool to consider also masked packages
For instance, to install gnome considering unstable packages and allowing the tool to change the use flag configuration:
```
bash hyportage.sh emerge --exploration=keywords,use gnome-base/gnome
```


#### Error Management

By default, if the atoms in parameter cannot be installed, the tool simply states that there are no solution and terminates without giving any explanation.
This is due to a limitation of the backend solver.
However, if an explanation of the problem is needed, it is possible to re-run the tool with the `--explain-modality` option
 to get a message listing the constraints that are in conflict.

Note that it is possible to directly call our tool with the `--explain-modality`, but it disturbs the solver that most probably will install many unnecessary packages.
For instance, to have an idea of why gnome cannot be installed, one can call
```
bash hyportage.sh emerge --explain-modality gnome-base/gnome
```
and will obtain the following message
```
user-required: (or gnome-base/gnome-3.20.0 gnome-base/gnome-3.22.0)
user-required: (not gnome-base/gvfs-1.28.3-r1#udisks)
user-required: (not gnome-base/gvfs-1.30.3)
gnome-base/gnome-3.20.0: (=> gnome-base/gnome-3.20.0 (and x11-themes/sound-theme-freedesktop-0.8 (or gnome-base/gdm-3.20.1 gnome-base/gdm-3.22.3) (or x11-themes/gnome-backgrounds-3.20 x11-themes/gnome-backgrounds-3.22.1 x11-themes/gnome-backgrounds-3.23.91) (or x11-wm/mutter-3.22.3 x11-wm/mutter-3.20.3) (or (and gnome-base/gnome-core-apps-3.22.2 (or (not gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.22.2#cups) (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.22.2#bluetooth) (or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.22.2#cdr)) (and gnome-base/gnome-core-apps-3.20.0 (or (not gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.20.0#cups) (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.20.0#bluetooth) (or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.20.0#cdr)) (and gnome-base/gnome-core-apps-3.22.0 (or (not gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.22.0#cups) (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.22.0#bluetooth) (or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.22.0#cdr))) (or (and gnome-base/gnome-core-libs-3.22.2 (or (not gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-libs-3.22.2#cups)) (and gnome-base/gnome-core-libs-3.20.0-r1 (or (not gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-libs-3.20.0-r1#cups))) (or (and gnome-base/gnome-shell-3.22.3 (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-shell-3.22.3#bluetooth)) (and gnome-base/gnome-shell-3.22.2 (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-shell-3.22.2#bluetooth)) (and gnome-base/gnome-shell-3.20.4 (or (not gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-shell-3.20.4#bluetooth))) (or (and gnome-base/gvfs-1.28.3-r1 gnome-base/gvfs-1.28.3-r1#udisks) (and gnome-base/gvfs-1.30.3 gnome-base/gvfs-1.30.3#udisks)) (or (not gnome-base/gnome-3.20.0#accessibility) (and (or app-accessibility/at-spi2-atk-2.22.0 app-accessibility/at-spi2-atk-2.20.1) (or app-accessibility/at-spi2-core-2.22.1 app-accessibility/at-spi2-core-2.20.2) app-accessibility/caribou-0.4.21 (or app-accessibility/orca-3.20.3-r1 app-accessibility/orca-3.22.2 app-accessibility/orca-3.22.1) gnome-extra/mousetweaks-3.12.0)) (or (not gnome-base/gnome-3.20.0#classic) gnome-extra/gnome-shell-extensions-3.20.1 gnome-extra/gnome-shell-extensions-3.22.2) (or (not gnome-base/gnome-3.20.0#extras) gnome-base/gnome-extra-apps-3.20.0 gnome-base/gnome-extra-apps-3.22.0)))
user-required: (not gnome-base/gnome-3.22.0)
```
This message is not very satisfactory (it does not contain proper sentence using portage syntax), but still give us some information:
 - to install gnome, we need to install either `gnome-base/gnome-3.20.0` or `gnome-base/gnome-3.22.0`
 - `gnome-base/gnome-3.22.0` is not installable, either because it is masked or unstable
 - `gnome-base/gnome-3.20.0` is not installable because of its dependencies requires the use flag `udisks` to be selected for the packages `gnome-base/gvfs`, which is not.



## Limitations

This tool, being a prototype in a research project, has many limitations and most probably bugs
 - As previously discussed, the installation and error messages could greatly be improved.
   However, this would require a lot of engineering work.
 - This tool does not consider the different stages of package installation, and merges together the dependencies, the runtime dependencies and the p-dependencies.
 - This tool does not manage the order of package installation/removal. For instance, to install gnome, our tool states that `=sys-fs/eudev-3.1.5` must be removed but does not say when.
   By default, the tool first states what must be installed and then what must be removed.
 - This tool does not ask for the recompilation of packages with the slot `:=` dependency (this is however managed by portage itself when our installation script calls emerge)

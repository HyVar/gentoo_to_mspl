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
 - `hyportage.sh install`: copy the generated installation script and package.use file to the guest VM, and executes the scripts, thus performing the installation.



## Structure of the repository:


Note that this structure is configurable in the main script hyportage.sh

* hyportage.sh: the main script of this implementation. documentation of the commands is included
* guest/hyvar: contains the script to save in the gentoo VM
    1. clean.sh: clean the guest VM off the installed scripts
    2. setup.sh: bash script to setup the right environment for the scripts
    3. load_make_defaults.sh: bash script to load a make.defaults or make.conf portage file
    4. core_data.py: core data structures used in our tool
    5. portage_data.py: portage-specific data structures used in our tool
    5. extract_portage.py: main script that extract variability information from the portage packages, and store them in a local folder

* host: contains the code needed for the translation and computation of the new configuration
   - data: this folder contains the data extracted and translated from the gentoo VM
      * portage: contains all the data extracted from the guest gentoo VM
         1. packages/portage-tree: a copy of the egencache folder of the portage repository
         2. packages/deprecated: generated egencache files from the installed packages that are not available in portage anymore
         3. installed_packages.json: lists the packages that are installed on the guest VM, with the selected use flags
         4. profile_configuration.json: stores the packages variability information stored in the guest VM profile
         5. user_configuration.json: stores the packages variability information defined by the user in the guest VM
      * hyportage: contains our translation of the gentoo packages with information related to their variability, and some annex useful data
        1. hyportage.enc: contains the main information
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
./hyportage.sh sync_guest
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
./hyportage.sh translate
```

This script can take several minutes to complete.


This script have several options:
 * `-v`: verbose mode. The verbosity of the tool can be increased by having several instances of this option
 * `-p`: parallel mode. This option takes in parameter how many process to use, and parallelizes the loading of the egencache files

Typically, for a verbose execution of the script on a 4 core processor, one runs:
```
./hyportage.sh translate -vvv -p 3
```



### Computing a new Configuration




To run the reconfiguration run the following script.
```
sh reconfigure <request file> <keyword>
```

For example, to install git execute the following script.
```
sh reconfigure world amd64
```
where the world file is the following JSON file.
```
{
	"app-admin/sudo":{},
	"app-admin/syslog-ng":{},
	"sys-apps/dbus":{},
	"sys-boot/grub":{},
	"sys-kernel/genkernel":{},
	"sys-kernel/gentoo-sources":{},
	"dev-vcs/git":{}
}
```

Updating the VM
----------------------
To update the VM run the following script.
```
sh update-guest.sh osboxes@localhost 9022
```
This script move to the VM in the user home folder the installation script update.sh and set the configuration file
for the packages. The update script needs to be run on the VM by the user as follows.
```
sudo update.sh
```



### Removing the installed scripts and data


Note that this script for safety does not override existing data.
Please run the following script to delete local data TODO



Assumptions
----------------------

Package that are always visible (**) are treated as packages visible if they are stable on any architecture (*)

When the keyword is not specified for a package we do not consider its installation

Slot Operators
 - := is treated as :*
 - :SLOT= is treated as :SLOT

TODO:
------------------------ 
 sys-apps/kbd-2.0.3 can not be disinstalled

 Both: change world structure file to allow user to disinstall packages + extend capabilities (version,slots)
 
 Michael: correct generation of world from gentoo also translating the profile in hyvarrec

 Michael: split the configuration files to have a more efficient update

 Both: find a way to deal with necessary packages (should be easy), and global use flags preference (more complex)

 Michael: handle the deprecated packages after an update
 
 Jacopo: remove slot o subslot variables in encoding
 
 Jacopo: install world of kde version into minimal gentoo version and check what happens
 
 Jacopo: incrementality of translation into hyvarrec
 
 Jacopo: try to unify both parsing of dependencies (talk with Michael)
 
 Michael: contact gentoo community
 

Known Bugs
----------

 - the list of use flags of a package is not well computed
 -


Task:
------------------------ 
Find configuration from which installing something can not be done in portage easily


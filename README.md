# HyPortage: reconfiguring Gentoo

When trying to install a package in Gentoo by using the pakage manger [Portage](https://wiki.gentoo.org/wiki/Portage),
the users often had to configure a lot of settings, often performing manually the installation and removal of
other packages. When the installation is not straighforward due to some dependencies,
Portage often suggest some actions to perform. Unfortunately, even when these action are taken,
there is no guarantee to reach the desired configuration.

HyPortage is a tool that allows a correct and complete dependency resolution in portage,
 thus giving a correct list of packages to for emerge to install and uninstall,
 with a correct use flag configuration.

HyPortage works by abstracting the portage tree and the user configuration
(i.e., the files in /etc/portage) into some data that is then combined with the user
request to solve the dependencies.
In particular, package dependencies are translated into [SMT constraints](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories),
  and a backend solver guarantees the correctness and completeness of the result.
The list of packages to install and uninstall are saved in a bash script,
and the use flag configuration is saved in a `package.use` file. The bash script can be executed to
install the desired packages.

Note that HyPortage when a package can not be installed will worn the user that can also use the tool in
the explain modality to understand why the desired configuration can not be reached.

This work is based on the theory of Software Product Line and Multi-Software Product Line,
and the fact that portage is a Multi-Sofware Product Line. HyPortage uses the
[HyVarRec](https://github.com/HyVar/hyvar-rec) reconfigurator 
as back-end solver.

## Tool installation

### Using Docker

HyPortage can be deployed by using the [Docker](https://www.docker.com/) container technology.
Docker supports a huge variety of OS. In the following we assume that it is correctly installed on
a Linux OS (a similar procedure can be used to install HyPortage on a Windows or MacOS).

To create the Docker image please run the following command.

```
sudo docker pull jacopomauro/hyportage
```

For more information related to Docker and how to use it we invite the reader to the documentation at 
[https://www.docker.com/](https://www.docker.com/).


### Cloning the repository

The HyPortage source code can also be directly installed on a computer, by cloning this repository.
HyPortage is implemented in [bash](https://www.gnu.org/software/bash/) and [Python2.7](https://www.python.org/) and has the following dependencies:
 1. ssh
 2. rsync
 3. python 2.7 packages (installable with `pip install`): click, lrparsing, z3-solver
 4. [HyVarRec](https://github.com/HyVar/hyvar-rec) reconfigurator
The executable of HyPortage is the `hyportage.sh` bash script.

## Tool Usage

Our tool consider two OS/systems:
- the guest VM/OS that runs Gentoo OS
- the host VM/OS where HyPortage is installed.

We assume that the guest VM can reach by using ssh.

All the functionalities of HyPortage can be accessed from the hyportage.sh bash script
at the root of this repository.

The functions are:
- `hyportage.sh clean_guest`: removes the installed scripts from the guest VM.
- `hyportage.sh setup_guest`: installs some scripts in the guest VM to extract relevant data for HyPortage.
- `hyportage.sh clean_host`: removes data generated from previous runs. 
- `hyportage.sh setup_host`: creates the correct folder structure in the host to store the data.
   This must be executed before `sync_guest`.
- `hyportage.sh sync_guest`: extracts the data from the guest VM and moves it into the host.
- `hyportage.sh translate`: translate the portage tree and the user data into HyPortage internal representation.
- `hyportage.sh emerge`: acts like gentoo's `emerge -p`, except that it generates a installation script
   and a package.use file. These files are stored in the host/data/hyportage directory.
- `hyportage.sh install`: copy the generated installation script and package.use file to the guest VM,
   and executes the scripts thus performing the installation.\
  **Warning**: before executing this function, please read the [limitation section](#limitations).

### Usage Example

In the following we provide an example of how HyPortage can be used.
For this example we consider the Gentoo VMs available at
[https://www.osboxes.org/gentoo/](https://www.osboxes.org/gentoo/)
(Gentoo 201703 CLI Minimal - 64bit).

We assume that the Gentoo machine, in the following called guest, is reachable by using ssh.
For this reason the sshd demon needs to be started on the VM.
To do so please make sure that sshd is started and if not run the following command in the guest:

```
sudo service sshd start
```

Note that the credential to use the VM are the following:


``` 
Username: osboxes
Password: osboxes.org
Password for Root account: osboxes.org
```

To access the machine for the remaing of the running example we assume that it could be reached
with the ssh protocol at port 9022 (if VirtualBox is used this can be configured with a port forwarding).
Please verity to have access to the VM. As example this can be obtained as follows:

```
ssh -p 9022 -o PubkeyAuthentication=no osboxes@localhost
```

Finally, if the docker installation was chosen then we can start the host VM to run HyPortage.
This can be done by creating a Docker container as follows.

```
sudo docker run -i --net="host" --name hyportage_container -t jacopomauro/hyportage /bin/bash
```

The Docker container called hyportage_container will start and the bash prompt will be given.

### Initial setup

If it is the first time the guest or the host are used, the necessary scripts needs to be installed.
This can be done by running

```
bash hyportage.sh setup_guest
bash hyportage.sh setup_host
```

The password and the location of the guest VM can be configured in the hyportage.sh script.
In our case for instance the variables in hyportage.sh are initialized as follows.

```
# Configures how to connect to the guest VM
GUEST="localhost"
GUEST_PORT="9022"

GUEST_USER="osboxes"
GUEST_PWD_ROOT="osboxes.org"
GUEST_PWD_USER="osboxes.org"
```

Please make sure that the guest VM may be reached by the host VM by running the ssh command before 
running the previous two commands.

Note that `clean_guest` and `clean_host` commands can also be
run to start fresh in case the system has been previously used for other reconfiguration attempts.
 
### Getting data from the guest VM

The next step requires to move the information from the guest to the host.
This can be done by running the following command.

```
bash hyportage.sh sync_guest
```

This operation may require some seconds.
Note that once the password to access the guest is configured, the user does not need to enter it.
The script uses the sshpass utility to do so.

This script copies to the host the package data
(in the [egencache](https://wiki.gentoo.org/wiki/Egencache) format),
extracts to the host relevant information from the
[VM's profile](https://wiki.gentoo.org/wiki/Profile_(Portage)) and from the
[user configuration](https://wiki.gentoo.org/wiki//etc/portage),
and extracts to the host the list and use flags configuration of the installed packages.

Note that if an installed package is deprecated (i.e., it is not in the portage tree anymore),
this script regenerate a egencache file for it, so this package can still be considered in our tool.

### Translating the data into HyPortage format

The next step is to translate the egencache files and the extracted data into the internal HyPortage encoding.
This is done by executing

```
bash hyportage.sh translate
```

This script can take several minutes to complete.

This script have several options:
* `-v`: verbose mode.
  The verbosity of the tool can be increased by having several instances of this option (recommended `-vv`)
* `-p`: parallel mode.
  This option takes in parameter how many process to use, and parallelizes the loading of the egencache files.

Typically, for a verbose execution of the script on a 4 core processor, one runs:
```
bash hyportage.sh translate -vvv -p 3
```

### Computing a new configuration

The command to compute a new configuration is `emerge` and can be called similarly to
the portage `emerge` tool, without its options:

```
bash hyportage.sh emerge <list of atoms to install>
```
or
```
bash USE="use flag selection" hyportage.sh emerge <list of atoms to install>
```
Note that the atoms in parameter must be qualified with the package category.
For instance, `www-servers/apache` is accepted while `apache` is not.

This command has different options that can be viewed running the command
```
bash hyportage.sh bash hyportage.sh emerge --help
```

Let us assume that we want to install the apache web server. The command to compute the operation
to reach the new configuration is the following one.

```
bash hyportage.sh emerge -vv www-servers/apache
```

Since we added the option to increase the verbosity to 2 (`-vv`), this will print something like the following.
```
INFO: Verbose Level: 2
INFO: number of available cores: 1
INFO: Loading the hyportage config.
INFO: Loading Completed in 0.0174939632416 seconds.
INFO: Loading the hyportage database.
INFO: Loading Completed in 34.0355110168 seconds.
INFO: computing a new system configuration... ()
INFO: Running: ['hyvar-rec', ... ]
INFO: Execution ended in 97.1177768707 seconds.
INFO: Execution succesfully terminated
```

The emerge script to run on the guest machine will be saved on the host VM in host/data/install/emerge.sh
In the same directory the file listing the selected use flags will be stored.

For the apache example on the osboxes VM the command will generate an emerge.sh script
requiring to execute the following command.
```
emerge -a --newuse =app-admin/apache-tools-2.2.31 \
  =dev-libs/apr-1.5.2 \
  =dev-libs/apr-util-1.5.2 \
  =www-servers/apache-2.2.31-r1
```

The real installation process can be triggered directly from the host by running the following command.
```
bash hyportage.sh install
```
Alternatively the user can inspect the command and replicate it on the guest machine manually.

### Checking the current configuration

HyPortage can be used to check if the current configuration is consistent.
This can be done by running the following command.
```
bash hyportage.sh emerge -vv
```

If the configuration is consistent then the final host/data/install/emerge.sh will not contain
any emerge invocation. If a dependency is not met then the emerge.sh script will list the command
to execute to bring the configuration into a consistent state.

### External Solver Configuration

The computation of a new configuration uses an external solver called [HyVarRec](https://github.com/HyVar/hyvar-rec).
By default, our tool suppose that the executable `hyvar-rec` can be called, but two options can change this behavior:
 1. `--local-solver 'command'` specifies the command to call the solver on the local computer.
    It can be useful when the HyPortage is installed without Docker and is not possible to create an `hyvar-rec` 
    executable (e.g., the user have a Windows OS).
    For instance, one can specify a command that directly execute the hyvar-rec.py file with python:
    ```
    bash hyportage.sh emerge -vvv  --local-solver 'python C:\Users\user\git\hyvar-rec\hyvar-rec.py' www-servers/apache
    ```
    Note that the paths in the command cannot contain spaces.
 2. `--hyvarrec-url` specifies the url of an HyVarRec server.

### Exploration Modality

By default, HyPortage installs only installable packages (that are stable and not masked) with the use flag
configuration as specified by the user.
However, the `--exploration` option allow HyPortage to be more flexible.
This option takes as parameter a list of exploration mode to consider:
- **use**: this mode allows the tool to change the use flag configuration of the packages
- **keywords**: this mode allows the tool to consider also packages that are unstable or that cannot be installed
  in the specified architecture
- **mask**: this mode allows the tool to consider also masked packages.

For instance, to install gnome considering unstable packages and allowing the tool to change the use flag configuration
it is possible to invoke the following command.
```
bash hyportage.sh emerge --exploration=keywords,use gnome-base/gnome
```

### Detecting conflicts

It is possible that a package could not be installed due to its dependencies.
This for instance happens for osboxes VM when trying to install the gnome-base/gnome package.

Indeed, running the following command  
```
bash hyportage.sh emerge -vv gnome-base/gnome
```
the tool outputs
```
ERROR: Non valid configuration found
ERROR: exiting
```

By default, if the atoms requried cannot be installed, the tool simply states that there are no solution and 
terminates without giving any explanation.
It is possible to try to understand what is the source of the problem by finding why there is a conflict.
This can be done by running the tool in explain modality as follows.
```
bash hyportage.sh emerge -vv --explain-modality gnome-base/gnome
```
In this case HyPortage will output the following lines.
```
ERROR: Conflict detected. Explanation:
user-required: (or gnome-base/gnome-3.20.0 gnome-base/gnome-3.22.0)
user-required: (not gnome-base/gvfs-1.28.3-r1#udisks)
user-required: (not gnome-base/gvfs-1.30.3)
gnome-base/gnome-3.20.0: (=>
gnome-base/gnome-3.20.0 (and x11-themes/sound-theme-freedesktop-0.8
	(or gnome-base/gdm-3.22.3 gnome-base/gdm-3.20.1) (or
	x11-themes/gnome-backgrounds-3.23.91 x11-themes/gnome-backgrounds-3.22.1
	x11-themes/gnome-backgrounds-3.20) (or x11-wm/mutter-3.22.3
	x11-wm/mutter-3.20.3) (or (and gnome-base/gnome-core-apps-3.22.0 (or (not
	gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.22.0#cups) (or (not
	gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.22.0#bluetooth)
	(or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.22.0#cdr))
	(and gnome-base/gnome-core-apps-3.22.2 (or (not
	gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.22.2#cups) (or (not
	gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.22.2#bluetooth)
	(or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.22.2#cdr))
	(and gnome-base/gnome-core-apps-3.20.0 (or (not
	gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-apps-3.20.0#cups) (or (not
	gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-core-apps-3.20.0#bluetooth)
	(or (not gnome-base/gnome-3.20.0#cdr) gnome-base/gnome-core-apps-3.20.0#cdr)))
	(or (and gnome-base/gnome-core-libs-3.22.2 (or (not
	gnome-base/gnome-3.20.0#cups) gnome-base/gnome-core-libs-3.22.2#cups)) (and
	gnome-base/gnome-core-libs-3.20.0-r1 (or (not gnome-base/gnome-3.20.0#cups)
	gnome-base/gnome-core-libs-3.20.0-r1#cups))) (or (and
	gnome-base/gnome-shell-3.22.3 (or (not gnome-base/gnome-3.20.0#bluetooth)
	gnome-base/gnome-shell-3.22.3#bluetooth))
	(and gnome-base/gnome-shell-3.22.2 (or (not
	gnome-base/gnome-3.20.0#bluetooth) gnome-base/gnome-shell-3.22.2#bluetooth))
	(and gnome-base/gnome-shell-3.20.4 (or (not gnome-base/gnome-3.20.0#bluetooth)
	gnome-base/gnome-shell-3.20.4#bluetooth))) (or (and gnome-base/gvfs-1.28.3-r1
	gnome-base/gvfs-1.28.3-r1#udisks) (and gnome-base/gvfs-1.30.3
	gnome-base/gvfs-1.30.3#udisks)) (or (not gnome-base/gnome-3.20.0#accessibility)
	(and (or app-accessibility/at-spi2-atk-2.22.0
	app-accessibility/at-spi2-atk-2.20.1) (or app-accessibility/at-spi2-core-2.22.1
	app-accessibility/at-spi2-core-2.20.2) app-accessibility/caribou-0.4.21
	(or app-accessibility/orca-3.20.3-r1 app-accessibility/orca-3.22.2
	app-accessibility/orca-3.22.1) gnome-extra/mousetweaks-3.12.0)) (or (not
	gnome-base/gnome-3.20.0#classic) gnome-extra/gnome-shell-extensions-3.20.1
	gnome-extra/gnome-shell-extensions-3.22.2) (or (not
	gnome-base/gnome-3.20.0#extras) gnome-base/gnome-extra-apps-3.20.0
	gnome-base/gnome-extra-apps-3.22.0)))
user-required: (not gnome-base/gnome-3.22.0)
```

This message is not very satisfactory (it does not contain proper sentence using portage syntax),
but still give us some information:
- to install gnome, we need to install either `gnome-base/gnome-3.20.0` or `gnome-base/gnome-3.22.0`
- `gnome-base/gnome-3.22.0` is not installable, either because it is masked or unstable
- `gnome-base/gnome-3.20.0` is not installable because of its dependencies requires the use flag `udisks` to be
    selected for the packages `gnome-base/gvfs`, which is not.

## Cleaning

To clean up the Docker installation of HyPortage the following commands can be used.

```
sudo docker stop hyportage_container
sudo docker rm hyportage_container
sudo docker rmi jacopomauro/hyportage
```

## Additional Notes

* The translation is a long procedure due to the amount of packages of the Gentoo distribution.
 There is no need to rerun the translation if the packages information has not changed.

* The generation of a new configuration requires the solving of an NP-hard problem. In the worst case it
  may require a long time to be performed but in our test it took only few minutes.

* In our [Tool Usage](#tool-usage) section, we considered two OS/Systems because HyPortage requires the installation of different packages and the Z3 SMT solver. It is
  however possible to install it also on the same Gentoo Machine provided that all the HyPortage dependencies
  are met. 

## Limitations

This tool, being a prototype in a research project, has many limitations and most probably bugs
- As previously discussed, the installation and error messages could greatly be improved.
  However, this would require a lot of engineering work.
- Currently, HyPortage always generates a `package.use` file, even if it is not necessary (.e.g, when the `use` exploration modality is not activated), and does not generate a `package.accept_keywords` nor a `package.unmask` file when it should.
  This limitation can be solved quickly.
- This tool does not consider the different stages of package installation, and merges together the dependencies,
   the runtime dependencies and the p-dependencies.
- This tool does not manage the order of package installation/removal. For instance, to install gnome, our tool 
  states that `=sys-fs/eudev-3.1.5` must be removed but does not say when.
  By default, the tool first states what must be installed and then what must be removed.
- This tool does not ask for the recompilation of packages with the slot `:=` dependency 
  (this is however managed by portage itself when our installation script calls emerge).
- Licenses are not considered.
- The incrementality of the translation process needs further testing.

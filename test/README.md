# Testing Portage's Semantics

Some parts of the otherwise very complete portage documentation is unclear or missing important information.
In addition to looking at portage's implementation, I also designed a testing environment to check that
 my understanding of USE flag implicit declaration,
 and of USE dependency semantics was correct.

## Setup the Testing Environment

The testing environment is stored in the hyportage folder.
The setup process is as follows:
 1. Copy the hyportage folder to the guest VM, in /opt
 2. log in the guest VM
 3. execute
    ```
    cd /opt/hyportage
    bash ./setup.sh
    ```

## Testing Environment Structure

 - the **hyportage** folder contains the packages used for testing.
   In particular, the group `test-implicit` is used to test the implicit USE flag declaration made in the profile.
   The package of this group indeed have a `REQUIRED_USE` variables using USE flags not locally defined.
   The other relevant packages here are in the group `test-deps` for testing the semantics of USE Dependencies.
 - the **metadata** folder is the standard portage metadata folder, nothing to see here.
 - the **profiles** folder is the profile I use for testing (you can indeed see that `setup.sh` replaces the standard profile with this one in `/etc/portage/make.profile`).
   There, one can define the file he wants and check what is the effect on portage.

One important thing to remember:
 every time a package is added or modified, its manifest must be regenerated, otherwise portage will complain.
To regenerate the manifest of a package, run the following command:
```
ebuild "your-package.ebuild" manifest
```
Otherwise, the script `generate_ebuild_annex_data.sh` regenerate all manifests for you.
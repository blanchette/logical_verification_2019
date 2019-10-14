# Logical Verification 2019 - Installation Instructions

We have installation instructions for Windows, Linux, and MacOS.
As a backup plan, we prepared a virtual machine on which
Lean is already installed.

<details><summary>Windows</summary>

## Windows

### Get Lean

* Install Git for Windows: https://gitforwindows.org/.
  Accept all default answers during the installation
  (or, if you would like to minimize the installation,
  you may deselect all components on the "Select components"
  question)

* Start the newly installed `Git Bash` by searching for it in the Windows
search bar.

* In Git Bash, run the command `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`

* Press `[Enter]` to proceed with the installation.

* Run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile`

* Run `source $HOME/.elan/env`

* Close Git Bash

### Get Python

* Download the [Python installer](https://www.python.org/ftp/python/3.7.4/python-3.7.4-amd64.exe) and run it.
* Check `Add Python 3.7 to PATH`.
* Click on `Install Now`.
* Navigate to the folder where Python was installed. A reliable way to do this is to search for `python` in the Start Menu -> right click `Python 3.x (xx-bit)` -> open file location -> right click `Python 3.x (xx-bit)` -> open file location. The default location is something like `C:\Users\<user>\AppData\Local\Programs\Python\Python37-32`.
* Copy the file `python.exe` to `python3.exe`.
* Open Git Bash (type `git bash` in the Start Menu)
* Test whether everything is working by typing `python3 --version` and `pip3 --version`. If both commands give a short output and no error, everything is set up correctly.
* If `pip3 --version` doesn't give any output, run the command `python3 -m pip install --upgrade pip`, which should fix it.

### Configure Git

* Run `git config --global core.autocrlf input` in Git Bash

### Install Lean Tools

* in Git Bash, run:

    * `curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash` 

    * `source ~/.profile`


### Installing and configuring the editor

1. Install [VS Code](https://code.visualstudio.com/) (You can accept all default options).
2. Launch VS Code.
3. Click on the extension icon ![(image of icon)](https://github.com/leanprover-community/mathlib/raw/master/docs/install/new-extensions-icon.png) 
   (or ![(image of icon)](https://github.com/leanprover-community/mathlib/raw/master/docs/install/extensions-icon.png) in older versions) in the side bar on the left edge of 
   the screen (or press `Shift-Ctrl-c`) and search for `leanprover`.
4. Click "install" and wait for the installation to complete.
5. Press `ctrl-shift-p` to open the command palette, and type
  `Select Default Shell`, press enter, then select `git bash` from   the menu.
6. Verify Lean is working:
Create a new file using `ctrl-N`,
save it using `ctrl-S`, and
name it `test.lean` 
in an arbitrary directory.
Write `#eval 1+1` into the new file.
A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
displayed.



### Install our logical verification repository

* Close VSCode

* Open Git Bash

* In Git Bash, use `cd` to go to the directory you want to place the project in  (a new folder will be created for it at that location). For instance, you can use `cd ~/Documents` to go to your personal Documents folder.

* Run these commands in Git Bash:

  * `git clone https://github.com/blanchette/logical_verification_2019`

  * `cd logical_verification_2019`

  * `leanpkg configure`

  * `update-mathlib`

  * `leanpkg build`

* launch VScode

* In the `File` menu, click `Open folder`, and choose the folder `logical_verification_2019` (not one of its subfolders). If you used `~/Documents` above, it will be located in your `Documents` folder.

* In the file explorer on the left-hand side, you will find all 
exercises and homework in the `lean` folder,
as we upload them.

* You can retrieve the newest exercises and homework that we upload by clicking the two arrows forming a circle in the bottom left corner.

</details>


<details><summary>Debian/Ubuntu and derivates</summary>


## Debian/Ubuntu and derivates

### Install Lean

* Open a terminal.

* `wget -q https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile`
(will take some time)

### Install our logical verification repository

* Use `cd` to go to the directory you want to place the project in  (a new folder will be created for it at that location).

* `git clone https://github.com/blanchette/logical_verification_2019`

* `cd logical_verification_2019`

* `leanpkg configure`

* `update-mathlib`

* `leanpkg build`

* launch VScode, either through your application menu or by typing `code`

* On the main screen, or in the `File` menu, click `Open folder`, and choose the folder `logical_verification_2019` (not one of its subfolders).

* In the file explorer on the left-hand side, you will find all 
exercises and homework in the `lean` folder,
as we upload them.

* You can retrieve the newest exercises and homework that we upload by clicking the two arrows forming a circle in the bottom left corner.

</details>


<details><summary>Other Linux distros</summary>

## Other Linux distros

Follow [these instructions](https://github.com/leanprover-community/mathlib/blob/master/docs/install/linux.md) and proceed by the instructions "Install our logical verification repository"
for Debian/Ubunutu above.

</details>


<details><summary>MacOS</summary>

## MacOS

* Open a terminal

* Install homebrew by running
`/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"`. Press enter to continue
and enter your password.

* Run `brew install gmp coreutils`

* Run `curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh`.
Hit enter to proceed with the installation.

* Run `source $HOME/.elan/env`

* Run `curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash`. Press `y` if you are asked whether you want to install python3 and pip3.

* Run `source ~/.profile`

### Set up VSCode

1. Download [VS Code](https://code.visualstudio.com/).
Open `Finder`, click on `Downloads`,
and drag the downloaded file `Visual Studio Code` into `Applications`.
2. Open `Launchpad` and launch `Visual Studio Code`.
Add `Visual Studio Code` to your Dock by right-clicking on the icon to bring up the context menu and choosing `Options`, `Keep in Dock`.
3. Click on the extension icon ![(image of icon)](https://github.com/leanprover-community/mathlib/raw/master/docs/install/new-extensions-icon.png) 
   (or ![(image of icon)](https://github.com/leanprover-community/mathlib/raw/master/docs/install/extensions-icon.png) in older versions) in the side bar on the left edge of 
   the screen (or press `Shift-Command-X`) and search for `leanprover`.
4. Click `install`.
5.  Verify Lean is working:
Create a new file using `Command-N`,
save it using `Command-S`, and
name it `test.lean` 
in an arbitrary directory.
Write `#eval 1+1` into the new file.
A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
displayed.

### Install our logical verification repository

* Open a terminal.

* Use `cd` to go to the directory you want to place the project in  (a new folder will be created for it at that location),
for example you can use `~/Documents`.

* `git clone https://github.com/blanchette/logical_verification_2019`

* `cd logical_verification_2019`

* `leanpkg configure`

* `update-mathlib`

* `leanpkg build`

* open VScode again

* Inn the `File` menu, click `Open`, and choose the folder `logical_verification_2019` (not one of its subfolders). If you used `~/Documents` above, it will be in the `Documents` folder.

* In the file explorer on the left-hand side, you will find all 
exercises and homework in the `lean` folder,
as we upload them.

* You can retrieve the newest exercises and homework that we upload by clicking the two arrows forming a circle in the bottom left corner.

</details>


<details><summary>Virtual Machine (for any operating system)</summary>

* Download and install VirtualBox: https://www.virtualbox.org/
(Other virtualization software should also work)

* Download the virtual machine:
https://drive.google.com/drive/folders/15R22c3iiYn4a2USkOFU6PvW6KbsS4-B0?usp=sharing

* Open VirtualBox

* Import the downloaded file via `File > Import Appliance`

* Select the `.ova` file you downloaded, click `continue` and then `import`.

* Start the virtual machine by 
selecting `logical_verification_2019` and clicking the `Start` button
and wait for the system to boot.

* Open VSCode by clicking on the blue ribbon icon on the left.

* In case you need the password for the virtual machine at some point,
it is `love`.

</details>

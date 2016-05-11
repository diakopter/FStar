## Online editor ##

The easiest way to try out F\* quickly is directly in your browser by using
the [online F\* editor] that's part of the [F\* tutorial].

[online F\* editor]: https://www.fstar-lang.org/run.php
[F\* tutorial]: https://www.fstar-lang.org/tutorial/

## Binary releases ##

Every now and then we release [F\* binaries on GitHub].
This is the easiest way to get F\* quickly running on your machine,
but if the release you use is old you might be missing out on new
features and bug fixes.

[F\* binaries on GitHub]: https://github.com/FStarLang/FStar/releases

### Testing a binary package ###

Test that the binary is good by expanding the archive and running the
following commands. (On Windows this requires Cygwin and `make`)

1. Add `fstar.exe` and `z3` to your `PATH`, either permanently
   or temporarily, for instance by running this:

        $ source setenv.sh
        $ fstar.exe --version
        F* 0.9.1.1
        platform=Linux_x86_64
        compiler=OCaml 4.02.3
        date=2015-12-04T15:45:49+0100
        commit=344c7d1
        $ z3 --version
        Z3 version 4.4.1

2. Run the unit tests:

        $ make -C examples/unit-tests

3. If you have OCaml installed run, the following command should print "Hello F*!"

        $ make -C examples/hello ocaml

4. If you have F# installed run, the following command should print "Hello F*!"

        $ make -C examples/hello fs

5. You can try out the full regression suite, but keep in mind that
   things might fail because of timeouts if your machine is not
   sufficiently powerful.

        $ make -C examples

### OPAM package ###

If the OCaml package manager is present on your platform, you can install F\*
and required dependencies (except for Z3) using the opam package:

        $ opam install fstar

### Homebrew formula for Mac OS X ###

On Macs you can also build and install the latest F\* release using Homebrew
This will install F\* and all required dependencies (including Z3):

        $ brew install fstar

For building and installing the latest F\* sources from GitHub (the master branch)
instead of the latest release you can do:

        $ brew install --HEAD fstar

## Building F* from sources ##

If you have a serious interest in F\* or want to report bugs then we
recommend that you build F\* from the sources on GitHub (the master branch).

F\* is written in a subset of F# that F\* itself can also parse with a
special flag. Therefore, the standard build process of F* involves the following
three steps:

  **Step 1.** build F* from sources using the F# compiler
     (obtaining a .NET binary for F\*);

  **Step 2.** extract the sources of F* itself to OCaml
     using the F* binary produced at step 1 (or even a previous step 3);

  **Step 3.** re-build F* using the OCaml compiler from the code
     generated at step 2 (obtaining a faster native binary for F\*).

**Note:** If you build F* from sources you will also need to get a Z3
binary. This is further explained towards the end of this document.

**Easier alternative:**  If you don't care about efficiency and about the .NET
dependency you can stop already after step 1.

**Easier alternative:**  If you don't want to use F#/.NET/Mono at all you can
also build F\* directly from the generated OCaml sources.  Therefore, for
convenience, we keep a (possibly outdated) snapshot of the F\* sources
extracted to OCaml (the result of step 2) in the repo.  This allows
you to skip directly to step 3 and build F* with just an OCaml compiler.

### Step 1. Building F* from sources using the F# compiler ###

#### On Windows 7/8/10 using Visual Studio 2015 ####

  - Prerequisite: .NET framework 4.5

  - Prerequisite: [Visual Studio 2015 and Visual F# Tools](http://fsharp.org/use/windows/)
    - for instance install the **free**
      [Visual Studio Community](https://www.visualstudio.com/en-us/products/visual-studio-community-vs.aspx)
    - The Visual F# Tools are installed automatically when you first
      create or open an F# project.

  - Run the `src/VS/nuget-restore.bat` script _from the top-level F* directory_
    before opening the solution for the first time.
    F* depends upon NuGet packages that are incompatible with
    Visual Studio's internal invocation of NuGet's restore feature.

        C:\Users\xxx\Desktop\FStar>src\VS\nuget-restore.bat
        Installing 'FsLexYacc.Runtime 6.1.0'.
        Installing 'FsLexYacc 6.1.0'.
        Successfully installed 'FsLexYacc.Runtime 6.1.0'.
        Successfully installed 'FsLexYacc 6.1.0'.
        All packages listed in packages.config are already installed.

  - Using Visual Studio, open `src/VS/FStar.sln` and build the solution
    (in the menus: Build > Build Solution). **Make sure to chose the 'Release' configuration**. 
    Note: the 'Debug' configuration may be the default, although it has no optimizations enabled
    and is not capable of bootstrapping.

**Note:** on Windows if you want to build F\* using F# you need use
  Visual Studio (building using `fsc.exe` in Cygwin is not supported
  currently; `make -C src` succeeds but produces a broken binary:
  https://github.com/FStarLang/FStar/issues/159)

**Note:** If Visual Studio fails to open one or more projects, the
  problem is likely that the NuGet package cache hasn't been
  restored. You must either exit Visual Studio to restore the cache
  (using the `src/VS/nuget-restore.bat` script), or restart Visual
  Studio after having restored the cache. Otherwise, F* may not
  successfully build (or correctly build).

#### On Linux or Mac OS X using Mono ####

  - Install mono from 3.10.x to 4.2.x and fsharp 4.0.1.0

    - On Debian/Ubuntu

            $ sudo apt-get install mono-complete fsharp

    - On Arch

            $ pacman -S mono
            $ aura -A fsharp

    - For other Linux distributions check out these links:
      - http://www.mono-project.com/download/#download-lin
      - http://fsharp.org/use/linux/

    - For Mac OS X install the MRE:
      - http://www.mono-project.com/download/#download-mac

  - Depending on your distribution, you might need to manually import
    certificates for Mono (you don't need to do this on Arch if you
    use the default mono package)

          $ mozroots --import --sync

  - Compile F* from sources

          $ git clone https://github.com/FStarLang/FStar.git
          $ cd FStar
          $ make -C src

  - Try out

          $ source setenv.sh
          $ make test.net -C src

  - If `make test.net` (`make boot` in fact) causes a stack overflow try
    issuing `ulimit -s unlimited` in the terminal beforehand.

### Prerequisite for steps 2 and 3: Working OCaml setup  ###

Steps 2 and 3 below require a working OCaml (4.02.2 or later) setup.

#### Instructions for Windows ####

0. Install the [OCaml Installer for
   Windows](http://protz.github.io/ocaml-installer/). Make sure you ask it to
   install Cygwin -- it will just launch Cygwin's setup.exe with the right set
   of packages pre-checked, to make sure you have everything you need.

1. Open the Cygwin terminal and fake the installation of OPAM package `conf-gmp`:

  ```sh
  $ opam install --fake conf-gmp
  ```

#### Instructions for Linux and Mac OS X ####

0. Install OCaml (version 4.02.2 or later)
   - Can be installed using either your package manager or using OPAM
     (see below).

#### Instructions for all OSes ####

1. Install OPAM (version 1.2.x).
   - Installation instructions are available at various places
     (e.g., https://github.com/realworldocaml/book/wiki/Installation-Instructions#getting-opam
     or http://opam.ocaml.org/doc/Install.html).

   - If you're on windows, the OCaml installer should have also installed opam for you.

2. Initialize and configure OPAM
   
   - You need to initialize it by running `opam init` and update the `PATH`
     variable to the `ocamlfind` and the OCaml libraries. If you allow
     `opam init` to edit your `~/.bashrc` or `~/.profile`, it is done
     automatically; otherwise, use: `eval $(opam config env)`.

  - If you're on Windows see https://github.com/FStarLang/FStar/blob/master/contrib/CoreCrypto/INSTALL.md
   for instructions on how to configure your environment for use with OPAM

3. Install `ocamlfind`, `batteries`, `stdint`, and `zarith` using OPAM:

  ```sh
  $ opam install ocamlfind batteries stdint zarith
  ```

### Step 2. Extracting the sources of F* itself to OCaml ###

0. Get an F* binary, either using the F#/.NET build process (step 1
   above; remember to build a Release version, else you'll get a StackOverflowException in `make ocaml -C src` below), 
   or the OCaml build process (step 3 above).

1. Make sure you follow the instructions above to get a working OCaml setup.

2. Once you satisfy the prerequisites for your platform,
   translate the F* sources from F# to OCaml using F* by running:

        $ make ocaml -C src

### Step 3. Building F* from the OCaml snapshot ###

Once you have a working OCaml setup (see above)
just run the following command:

        $ make -C src/ocaml-output

**Note:** On Windows this generates a native F* binary, that is, a binary that
does *not* depend on `cygwin1.dll`, since the installer above uses a
*native* Windows port of OCaml.  Cygwin is just there to provide `make` and
other utilities required for the build.
This also means that when linking C libraries with OCaml compiled objects one
needs to use the *correct* mingw libraries and *not* the Cygwin ones. OCaml uses
special `flexlink` technology for this. See `contrib/CoreCrypto/ml` and
`examples/crypto` for examples.


## Runtime dependency: Z3 SMT solver ##

To use F* for verification you need a Z3 4.4.1 binary.
Our binary packages include that already in `bin`, but if you compile
F* from sources you need to get a Z3 binary yourself and add it to
your `PATH`. We recommend you use the 4.4.1 binaries here:
https://github.com/Z3Prover/z3/releases/tag/z3-4.4.1

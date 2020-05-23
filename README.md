[![Travis][travis badge]][travis]
[![Erlang Versions][erlang versions badge]][erlang]
[![Last Commit][commit badge]][commit]

CutEr
=====

This is the source tree for CutEr, a concolic unit testing tool for Erlang.

***CAUTION: This tool is still under heavy development***

* [License](#license)
* [Dependencies](#dependencies)
* [Installation](#installation)
* [Usage](#usage)

License
-------

Copyright 2014-2020 by Aggelos Giantsios, Nikolaos Papaspyrou and Kostis Sagonas.

This program is distributed under the GPL, version 3 or later. Please see the COPYING file for details.

Dependencies
------------

In order to use CutEr, you need the following programs:

1. **Erlang/OTP**

  Although CutEr may still be working with older Erlang/OTP releases,
  we only support Erlang/OTP releases 19.x or later.
  Note that using a pre-built package or binaries will not suffice if
  the library modules have not been compiled with debug information.
  In that case, you will need to build and install Erlang/OTP from source.

  Download the latest [source code distribution of
  Erlang/OTP](http://www.erlang.org/download.html) or clone the
  Erlang/OTP github repository:

        git clone https://github.com/erlang/otp.git

  Then follow the instructions in
  [INSTALL.md](https://github.com/erlang/otp/blob/maint/HOWTO/INSTALL.md)
  for building and installing Erlang/OTP.

2. **Python 3.x**, x >= 6

  Download and install the latest [Python 3.x distribution](http://www.python.org).

  Also, you need to install the required Python dependencies.

        python3 -m pip install -r requirements.txt

  Note that CutEr requires Python 3.6 or higher.

3. **Z3 Theorem Prover**

  Download the [v4.8.8 Z3 release](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8)
  or clone the `z3-4.8.8` tag of Z3 from its git repository with the following command:

        git clone -b z3-4.8.8 --depth 1 https://github.com/Z3Prover/z3.git

  For your convenience, we include here a list of commands to build from source and install the above release of Z3:

        cd z3 ; python scripts/mk_make.py
        cd build ; make
        sudo make install

  If this sequence of commands does not work for you, follow the instructions in Z3's [GitHub repository](https://github.com/Z3Prover/z3/).

  Note that CutEr requires Z3 v4.8.8 or higher.

4. **Protocol Buffer Compiler**

  If you have a Linux or an OSX system then you can skip this step and, after you have downloaded or cloned this repository, you can run the provided `fetch_protoc.sh` script and follow the instructions.

  If you are running on some other OS, download the [3.11.3 version](https://github.com/google/protobuf/releases/tag/v3.11.3) of **protoc** for your OS
  and follow the instructions in *readme.txt*.

Installation
------------

* Download CutEr's sources or clone this repository:

        git clone https://github.com/cuter-testing/cuter.git
        cd cuter

* **[Optional]** If you want to run the full test suite of CutEr, you will also need [PropEr](https://github.com/proper-testing/proper). You can install it independently or go to CutEr's base directory and run:

        git submodule init && git submodule update
        git submodule foreach make

* **[Optional]** If you have not manually downloaded and installed the Protocol Buffer Compiler, run the following script that will fetch it:

        ./fetch_protoc.sh

* Configure and compile CutEr. For a default build use:

        autoconf
        ./configure	# see Note below
        make depend
        make

   **[If required]** Note that if you have installed *protoc* using `fetch_protoc.sh`
   then you need to specify the path of *protoc* to the configure script using a
   command like the following:

        ./configure --with-protoc=$PWD/lib/protoc-3.11.3/bin/protoc

* **[Optional]** You can run the unit and functional tests with `make test`

* **[Optional]** You can also run Dialyzer with `make dialyzer`

* Add CutEr's base directory to your Erlang library path by updating the `ERL_LIBS` environment variable. Just add

        export ERL_LIBS=/full/path/to/cuter:$ERL_LIBS

  to your shell startup file (e.g. `~/.bashrc` for Bash).

Usage
-----

Let's say that you have a simple module `foo` that just contains
the exported function `bar/2`. The source file `foo.erl` is:

```erlang
-module(foo).
-export([bar/2]).

-spec bar([number()], [number()]) -> number().
bar([], Ys) -> lists:sum(Ys);
bar([X|Xs], [Y|Ys]) -> X * Y + bar(Xs, Ys).
```

For single file tests, such as the above, the simplest way to run CutEr
is to use the `cuter` script as follows:

    ./cuter foo bar '[[1], [2]]'

i.e. supply it with three arguments: the module name, the function name,
and the list of arguments for the call that will act as a seed for the
concolic execution of the unit under test.  If there is no `foo.beam`
file, the `cuter` script will automatically compile the `foo.erl` file
and create a .beam file with debug information.

Alternatively, go to the directory of the source file and compile it
with debug information:

    erlc +debug_info foo.erl

CutEr can then be invoked by calling the `cuter:run/3` function:

    erl -noshell -eval "cuter:run(foo, bar, [[1], [2]])" -s init stop

This will report a list of inputs that lead to runtime errors, for
example `foo:bar([0], [])` and `foo:bar([3,2,1], [0.0,0])`.

To sum up, `cuter:run/3` is called as `cuter:run(M, F, As)` where

* `M` is the module
* `F` is the function
* `As` is the list of arguments of the seed input

There is also a `cuter:run/4` function that takes these three arguments
but also a numeric argument `Depth` that denotes the depth of the search
(i.e. roughly the number of branches that will be explored).  This depth
can also be specified as an option of the `cuter` script:

    ./cuter foo bar '[[1], [2]]' -d 42

CutEr provides more API functions that also come with options that
control the concolic execution of Erlang programs. These will be
explained in a set of forthcoming tutorials. In the meantime, you can
find out about them by the command:

    ./cuter --help

and by browsing the source code of CutEr.

Have fun with the tool!


<!-- Badges (alphabetically) -->
[commit badge]: https://img.shields.io/github/last-commit/cuter-testing/cuter.svg?style=flat-square
[erlang versions badge]: https://img.shields.io/badge/erlang-19.0%20to%2022.3-blue.svg?style=flat-square
[travis badge]: https://img.shields.io/travis/cuter-testing/cuter.svg?branch=master?style=flat-square

<!-- Links (alphabetically) -->
[commit]: https://github.com/cuter-testing/cuter/commit/HEAD
[erlang]: http://www.erlang.org
[travis]: https://travis-ci.org/cuter-testing/cuter

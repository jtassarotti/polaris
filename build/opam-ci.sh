#!/bin/bash
set -e
set -x
## This script installs the build dependencies for CI builds.

# Prepare OPAM configuration
export OPAMROOT="$(pwd)/opamroot"
export OPAMJOBS="$((2*$CPU_CORES))"
export OPAM_EDITOR="$(which false)"

# Make sure we got a good OPAM.
test -d "$OPAMROOT" || (mkdir "$OPAMROOT" && opam init --no-setup -y)
eval `opam conf env`

# Make sure the pin for the builddep package is not stale.
make build-dep/opam

# Update repositories
opam update

# Make sure we got the right set of repositories registered
if echo "$@" | fgrep "dev" > /dev/null; then
    # We are compiling against a dev version of something.  Get ourselves the dev repositories.
    test -d "$OPAMROOT/repo/coq-extra-dev" || opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev -p 0
    test -d "$OPAMROOT/repo/coq-core-dev" || opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev -p 5
else
    # No dev version, make sure we do not have the dev repositories.
    test -d "$OPAMROOT/repo/coq-extra-dev" && opam repo remove coq-extra-dev
    test -d "$OPAMROOT/repo/coq-core-dev" && opam repo remove coq-core-dev
fi
test -d "$OPAMROOT/repo/coq-released" || opam repo add coq-released https://coq.inria.fr/opam/released -p 10
test -d "$OPAMROOT/repo/iris-dev" || opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git -p 20
echo

# We really want to run all of the following in one opam transaction, but due to opam limitations,
# that is not currently possible.

# Install fixed versions of some dependencies.
echo
while (( "$#" )); do # while there are arguments left
    PACKAGE="$1" ; shift
    KIND="$1" ; shift
    VERSION="$1" ; shift

    # Check if the pin is already set
    read -a PIN <<< $(opam pin list | (egrep "^$PACKAGE[. ]"))
    if [[ "${PIN[1]}" == "$KIND" && "${PIN[2]}" == "$VERSION" ]]; then
        echo "[opam-ci] $PACKAGE already $KIND-pinned to $VERSION"
    else
        echo "[opam-ci] $KIND-pinning $PACKAGE to $VERSION"
        opam pin add -y -k "$KIND" "$PACKAGE" "$VERSION"
    fi
done

# Upgrade cached things.
echo
echo "[opam-ci] Upgrading opam"
opam upgrade -y --fixup && opam upgrade -y

# Install build-dependencies.
echo
echo "[opam-ci] Installing build-dependencies"
make build-dep OPAMFLAGS=-y

# done
echo
coqc -v

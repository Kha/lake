set -ex

(cd baz; ${LAKE:-../../../build/bin/lake} build)

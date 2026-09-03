#!/bin/sh

set -eu

srcdir=`CDPATH= cd -- "$(dirname "$0")/.." && pwd`
builddir=`mktemp -d "${TMPDIR:-/tmp}/lambdamoo-coverage.XXXXXX"`
if test "${KEEP_COVERAGE_BUILD:-no}" = yes; then
    printf 'coverage build: %s\n' "$builddir"
else
    trap 'rm -rf "$builddir"' EXIT HUP INT TERM
fi
coverage_cc=${CC:-gcc}
ccache_tmp="$builddir/ccache"
mkdir "$ccache_tmp"

cd "$srcdir"
git ls-files -z | tar --null -T - -cf - | (cd "$builddir" && tar -xf -)
cd "$builddir"
printf '%s\n' "moo_MAJOR='1'" "moo_MINOR='9'" "moo_RELEASE='0'" \
    "moo_EXT='coverage'" >version.fixed
autoconf
CCACHE_DISABLE=1 CCACHE_TEMPDIR="$ccache_tmp" CC="$coverage_cc" \
    ./configure --enable-jit --enable-unicode=code,core --enable-waifs=all \
    >configure.log

coverage_cflags='-std=c99 -Og -g --coverage -Wall -Wextra'
CCACHE_DISABLE=1 CCACHE_TEMPDIR="$ccache_tmp" make \
    CFLAGS="$coverage_cflags" LDFLAGS=--coverage uT-jit
./uT-jit
jit_report=`gcov -b -c unit-tests/jit_test_jit.gcno`

rm -f unit-tests/hir_tac_test.o unit-tests/hir_test_hir.o \
    unit-tests/hir_test_stubs.o \
    arena.o integer_arithmetic.o uT-hir-tac
CCACHE_DISABLE=1 CCACHE_TEMPDIR="$ccache_tmp" make \
    CFLAGS="$coverage_cflags" LDFLAGS=--coverage uT-hir-tac
./uT-hir-tac
hir_report=`gcov -b -c unit-tests/hir_test_hir.gcno`

report_file()
{
    report=$1
    source=$2
    section=`printf '%s\n' "$report" | sed -n "/^File '$source'$/,/^Creating/p"`
    lines=`printf '%s\n' "$section" | awk -F '[:%]' '/^Lines executed:/ { print $2 }'`
    branches=`printf '%s\n' "$section" | awk -F '[:%]' '/^Branches executed:/ { print $2 }'`
    outcomes=`printf '%s\n' "$section" | awk -F '[:%]' '/^Taken at least once:/ { print $2 }'`

    if test -z "$lines" || test -z "$branches" || test -z "$outcomes"; then
	echo "coverage report for $source is incomplete" >&2
	return 1
    fi
    printf '%s: lines %s%%, branch sites %s%%, outcomes %s%%\n' \
	"$source" "$lines" "$branches" "$outcomes"
    awk -v lines="$lines" -v branches="$branches" \
	'BEGIN { exit !(lines >= 90 && branches >= 90) }'
}

report_file "$jit_report" jit.c
report_file "$hir_report" hir.c

# --------------------------------------------------------------------
# MOO_GPERF_LEN_TYPE
#
# Determine the type used for gperf lookup-function length parameters.
#
AC_DEFUN([MOO_GPERF_LEN_TYPE],
[AC_MSG_CHECKING([for the gperf length parameter type])
GPERF_TEST="`echo foo,bar | $GPERF --language=ANSI-C`"
AC_COMPILE_IFELSE(
  [AC_LANG_PROGRAM([[
#include <string.h>
const char *in_word_set(const char *, size_t);
$GPERF_TEST
  ]])],
  [GPERF_LEN_TYPE=size_t],
  [AC_COMPILE_IFELSE(
    [AC_LANG_PROGRAM([[
#include <string.h>
const char *in_word_set(const char *, unsigned int);
$GPERF_TEST
    ]])],
    [GPERF_LEN_TYPE="unsigned int"],
    [AC_MSG_ERROR([unable to determine the gperf length parameter type])])])
AC_MSG_RESULT([$GPERF_LEN_TYPE])
AC_DEFINE_UNQUOTED([GPERF_LEN_TYPE], [$GPERF_LEN_TYPE],
  [Define to the type of gperf lookup-function length parameters.])])dnl

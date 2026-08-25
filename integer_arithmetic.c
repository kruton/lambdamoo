#include "integer_arithmetic.h"

#include "config.h"
#include "options.h"

#include <limits.h>
#include <string.h>

static Num
signed_bits(UNum bits)
{
    Num value;

    memcpy(&value, &bits, sizeof(value));
    return value;
}

static IntegerArithmeticResult
value_result(Num value)
{
    IntegerArithmeticResult result;

    result.succeeded = 1;
    result.value = value;
    result.error = E_NONE;
    return result;
}

static IntegerArithmeticResult
error_result(enum error error)
{
    IntegerArithmeticResult result;

    result.succeeded = 0;
    result.value = 0;
    result.error = error;
    return result;
}

IntegerArithmeticResult
integer_arithmetic(IntegerArithmeticOperation operation, Num lhs, Num rhs)
{
    UNum base;
    UNum power;
    UNum value;
    unsigned width = sizeof(Num) * CHAR_BIT;

    switch (operation) {
    case INTEGER_NEGATE:
	return value_result(signed_bits((UNum) 0 - (UNum) lhs));
    case INTEGER_COMPLEMENT:
	return value_result(signed_bits(~(UNum) lhs));
    case INTEGER_ADD:
	return value_result(signed_bits((UNum) lhs + (UNum) rhs));
    case INTEGER_SUBTRACT:
	return value_result(signed_bits((UNum) lhs - (UNum) rhs));
    case INTEGER_MULTIPLY:
	return value_result(signed_bits((UNum) lhs * (UNum) rhs));
    case INTEGER_DIVIDE:
	if (rhs == 0)
	    return error_result(E_DIV);
	if (lhs == NUM_MIN && rhs == -1)
	    return value_result(NUM_MIN);
	return value_result(lhs / rhs);
    case INTEGER_MODULUS:
	if (rhs == 0)
	    return error_result(E_DIV);
	if (lhs == NUM_MIN && rhs == -1)
	    return value_result(0);
	return value_result(lhs % rhs);
    case INTEGER_POWER:
	if (rhs < 0) {
	    if (lhs == 0)
		return error_result(E_DIV);
	    if (lhs == -1)
		return value_result((rhs & 1) ? 1 : -1);
	    return value_result(lhs == 1 ? 1 : 0);
	}
	base = (UNum) lhs;
	power = (UNum) rhs;
	value = 1;
	while (power != 0) {
	    if (power & 1)
		value *= base;
	    base *= base;
	    power >>= 1;
	}
	return value_result(signed_bits(value));
    case INTEGER_SHIFT_LEFT:
    case INTEGER_SHIFT_RIGHT:
    case INTEGER_LOGICAL_SHIFT_RIGHT:
	if (rhs < 0 || (UNum) rhs >= width)
	    return error_result(E_INVARG);
	if (operation == INTEGER_SHIFT_LEFT)
	    return value_result(signed_bits((UNum) lhs << rhs));
	value = (UNum) lhs >> rhs;
	if (operation == INTEGER_SHIFT_RIGHT && lhs < 0 && rhs != 0)
	    value |= ~(UNum) 0 << (width - rhs);
	return value_result(signed_bits(value));
    }
    return error_result(E_INVARG);
}

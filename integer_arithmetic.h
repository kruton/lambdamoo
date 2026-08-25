#ifndef Integer_Arithmetic_H
#define Integer_Arithmetic_H 1

#include "structures.h"

typedef enum {
    INTEGER_NEGATE,
    INTEGER_COMPLEMENT,
    INTEGER_ADD,
    INTEGER_SUBTRACT,
    INTEGER_MULTIPLY,
    INTEGER_DIVIDE,
    INTEGER_MODULUS,
    INTEGER_POWER,
    INTEGER_SHIFT_LEFT,
    INTEGER_SHIFT_RIGHT,
    INTEGER_LOGICAL_SHIFT_RIGHT
} IntegerArithmeticOperation;

typedef struct {
    int succeeded;
    Num value;
    enum error error;
} IntegerArithmeticResult;

extern IntegerArithmeticResult integer_arithmetic(IntegerArithmeticOperation,
						   Num, Num);

#endif /* !Integer_Arithmetic_H */

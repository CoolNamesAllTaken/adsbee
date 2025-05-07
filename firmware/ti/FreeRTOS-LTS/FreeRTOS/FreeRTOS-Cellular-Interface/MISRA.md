# MISRA Compliance

The FreeRTOS-Cellular-Interface library files conform to the
[MISRA C:2012](https://www.misra.org.uk/)
guidelines, with the deviations listed below. Compliance is checked with
Coverity static analysis. The specific deviations, suppressed inline, are listed
below.

Additionally,
[MISRA configuration file](https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/tools/coverity/misra.config)
contains the project wide deviations.

### Suppressed with Coverity Comments

To find the violation references in the source files run grep on the source code
with ( Assuming rule 10.4 violation; with justification in point 1 ):

```
grep 'MISRA Ref 10.4.1' . -rI
```

#### Directive 4.6

_Ref 4.6.1_

- MISRA C-2012 Directive 4.6 warns against using types that do not contain size
  and sign information. The use of isalpha, isdigit, and isspace set this
  directive off since they use base types that don't contain this information.
  We do not have control over these functions so we are suppressing these
  violations.

#### Directive 4.7

_Ref 4.7.1_

- MISRA C 2012 Directive 4.7 requires that when a function returns error
  information, that error information shall be tested. The following line
  violates MISRA rule 4.7 because return value of strtol() is not checked for
  error. This violation is justified because error checking by "errno" for any
  POSIX API is not thread safe in FreeRTOS unless "configUSE_POSIX_ERRNO" is
  enabled. In order to avoid the dependency on this feature, errno variable is
  not used.

#### Rule 10.4

_Ref 10.4.1_

- MISRA C-2012 Rule 10.4 warns about using different types in an operation. This
  rule is being flagged because of use of the standard library functions
  isalpha, isdigit, and isspace. We do not have control over these functions so
  we are suppressing these violations.

#### Rule 10.5

_Ref 10.5.1_

- MISRA C-2012 Rule 10.5 Converting to an enum type. The variables are checked
  to ensure that they are valid, and within a valid range. Hence, assigning the
  value of the variable with a enum cast.

#### Rule 10.8

_Ref 10.8.1_

- MISRA C-2012 Rule 10.8 warns about casting from unsigned to signed types. This
  rule is being flagged because of use of the standard library functions isalpha
  and isdigit. We do not have control over these so we are suppressing these
  violations.

#### Rule 11.3

_Ref 11.3.1_

- MISRA C-2012 Rule 11.3 does not allow casting of a pointer to different object
  types. We are passing in a length variable which is then checked to determine
  what to cast this value to. As such we are not worried about the chance of
  misaligned access when using the cast variable.

#### Rule 21.6

_Ref 21.6.1_

- MISRA C-2012 Rule 21.6 warns about the use of standard library input/output
  functions as they might have implementation defined or undefined behaviour.
  The max length of the strings are fixed and checked offline.

#### Rule 21.9

_Ref 21.9.1_

- MISRA C-2012 Rule 21.9 does not allow the use of bsearch. This is because of
  unspecified behavior, which relates to the treatment of elements that compare
  as equal, can be avoided by ensuring that the comparison function never
  returns 0. When two elements are otherwise equal, the comparison function
  could return a value that indicates their relative order in the initial array.
  This the token table must be checked without duplicated string. The return
  value is 0 only if the string is exactly the same.

#### Rule 22.8

_Ref 22.8.1_

- MISRA C 2012 Rule 22.8 Requires the errno variable must be "zero" before
  calling strtol function. This violation is justified because error checking by
  "errno" for any POSIX API is not thread safe in FreeRTOS unless
  "configUSE_POSIX_ERRNO" is enabled. In order to avoid the dependency on this
  feature, errno variable is not used. The function strtol returns LONG_MIN and
  LONG_MAX in case of underflow and overflow respectively and sets the errno to
  ERANGE. It is not possible to distinguish between valid LONG_MIN and LONG_MAX
  return values and underflow and overflow scenarios without checking errno.
  Therefore, we cannot check return value of strtol for errors. We ensure that
  strtol performed a valid conversion by checking that *pEndPtr is '\0'. strtol
  stores the address of the first invalid character in *pEndPtr and therefore,
  '\0' value of \*pEndPtr means that the complete pToken string passed for
  conversion was valid and a valid conversion wasperformed.

#### Rule 22.9

_Ref 22.9.1_

- MISRA C 2012 Rule 22.9 requires that errno must be tested after strtol
  function is called.This violation is justified because error checking by
  "errno" for any POSIX API is not thread safe in FreeRTOS unless
  "configUSE_POSIX_ERRNO" is enabled. In order to avoid the dependency on this
  feature, errno variable is not used. The function strtol returns LONG_MIN and
  LONG_MAX in case of underflow and overflow respectively and sets the errno to
  ERANGE. It is not possible to distinguish between valid LONG_MIN and LONG_MAX
  return values and underflow and overflow scenarios without checking errno.
  Therefore, we cannot check return value of strtol for errors. We ensure that
  strtol performed a valid conversion by checking that *pEndPtr is '\0'. strtol
  stores the address of the first invalid character in *pEndPtr and therefore,
  '\0' value of \*pEndPtr means that the complete pToken string passed for
  conversion was valid and a valid conversion wasperformed.

# MISRA Compliance

The coreJSON library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/FreeRTOS/coreJSON/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.3 violation; with justification in point 1 ):
```
grep 'MISRA Ref 11.3.1' . -rI
```

#### Rule 11.3
_Ref 11.3.1_

- MISRA C-2012 Rule 11.3 prohibits casting a pointer to a different type.
        This instance is a false positive, as the rule permits the
        addition of a const type qualifier.

#### Rule 14.3
_Ref 14.3.1_

- MISRA C-2012 Rule 14.3 False positive as the static analysis tool believes
        i can never be larger than SIZE_MAX - HEX_ESCAPE_LENGTH. This can be proven as
        a bug by setting i to be 18446744073709551615UL at initial assignment, then require
        start != NULL before assigning the value of i to start. This creates a case
        where i should be large enough to hit the else statement, but the tool still flags
        this as invariant.

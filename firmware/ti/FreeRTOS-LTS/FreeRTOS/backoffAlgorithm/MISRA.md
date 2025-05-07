# MISRA Compliance

The backoffAlgorithm library files conform to the
[MISRA C:2012](https://www.misra.org.uk) guidelines, with some noted exceptions.
Compliance is checked with Coverity static analysis. The specific deviations,
suppressed inline, are listed below.

Additionally,
[MISRA configuration file](https://github.com/FreeRTOS/backoffAlgorithm/blob/main/tools/coverity/misra.config)
contains the project wide deviations.

### Suppressed with Coverity Comments

To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.4 violation; with justification in point 2 ):

```
grep 'MISRA Ref 11.4.2' . -rI
```

_None._

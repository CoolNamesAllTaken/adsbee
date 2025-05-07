# MISRA Compliance

The jobs library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis
version 2023.6.1. The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.4 violation; with justification in point 2 ):
```
grep 'MISRA Ref 11.1.4' . -rI
```

*None.*

# MISRA Compliance

The coreSNTP library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/FreeRTOS/coreSNTP/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.5 violation; with justification in point 1 ):
```
grep 'MISRA Ref 11.5.1' . -rI
```
#### Rule 11.5
_Ref 11.5.1_
- MISRA C-2012 Rule 11.5 Allow casts from `void *`. The library casts the byte
    array information received network to a `SntpPacket_t *` for parsing SNTP packet.

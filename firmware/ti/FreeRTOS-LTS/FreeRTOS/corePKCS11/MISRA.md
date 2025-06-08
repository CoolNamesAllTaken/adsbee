# MISRA Compliance

The PKCS #11 library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/FreeRTOS/corePKCS11/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 10.5 violation; with justification in point 1 ):
```
grep 'MISRA Ref 10.5.1' . -rI
```

#### Rule 10.5

_Ref 10.5.1_

- MISRA C-2012 Rule 10.5 The value of an expression should not be cast to an
    inappropriate essential type. The boolean type of the PKCS #11 standard is
    an unsigned char, which is an acceptable base type for a boolean type.

#### Rule 11.1

_Ref 11.1.1_

- MISRA C-2012 Rule 11.1 Doesn't allow conversions between function pointers and any other type
    However, since we're just using this to suppress the compiler warning, we're also fine with
    suppressing the MISRA violation related to this line as well.


#### Rule 12.1

_Ref 12.1.1_

- MISRA C-2012 Rule 12.1 Requires precedence of operators within an expression to be explicit.
    The third party macro being used here throws a violation when used. Adding additional parens to the
    call or to the decleration doesn't remove the violation, so we suppress it.

#### Rule 11.5

_Ref 11.5.1_

- MISRA C-2012 Rule 11.5 Allow casts from `void *`. Fields such as publish
    payloads are passed as `void *` and must be cast to the correct data type before use.

# MISRA Compliance

The HTTP Client library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/FreeRTOS/coreHTTP/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the deviation references in the source files run grep on the source code
with ( Assuming rule 5.4 violation; with justification in point 2 ):
```
grep 'MISRA Ref 5.4.2' . -rI
```

#### Rule 5.4
_Ref 5.4-1_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the
        one postfixed with _LEN. This rule is suppressed for naming consistency with
        other HTTP header field and value string and length macros in this file.

_Ref 5.4-2_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the one
        above it. This rule is suppressed for naming consistency with other HTTP
        header field and value string and length macros in this file.

_Ref 5.4-3_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the one
        postfixed with _LEN. This rule is suppressed for naming consistency with
        other HTTP header field and value string and length macros in this file.

_Ref 5.4-4_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the one
        above it. This rule is suppressed for naming consistency with other HTTP
        header field and value string and length macros in this file.

_Ref 5.4-5_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the one
        postfixed with _LEN. This rule is suppressed for naming consistency with
        other HTTP header field and value string and length macros in this file.

_Ref 5.4-6_

- MISRA Rule 5.4 flags the following macro's name as ambiguous from the one
        above it. This rule is suppressed for naming consistency with other HTTP
        header field and value string and length macros in this file.

#### Rule 10.8
_Ref 10.8.1_

- MISRA Rule 10.8 The size of the headers is found by taking the current location
       being parsed and subtracting it from the start of the headers. The start of
       the headers is set on the first header field found from http-parser. This always
       comes before finding the header length; if it does not, an assertion is triggered.
       This rule is suppressed because in the previous statement it is
       asserted that the pointer difference will never be negative.

#### Rule 14.3
_Ref 14.3.1_

- MISRA Rule 14.3 The third-party http-parser library sets a uint64_t type field to
       `ULLONG_MAX` or `( ( uint64_t ) -1 )`, during its internal parsing. Coverity MISRA
       does not detect that this variable changes. This field is checked by the HTTP
       Client library. If the Content-Length header was found, then pHttpParser->content_length
       will not be equal to the maximum 64 bit integer.

#### Rule 11.4
_Ref 11.4.1_

- MISRA Rule 11.4 does not allow casting pointers to different data types as this may lead
       to misaligned pointers. But in this case, the pointers are casted to different data
       type to get the length of the header. It is not casted back to a pointer.

#### Rule 11.8
_Ref 11.8.1_

- MISRA Rule 11.8 flags casting away the const qualifier in the pointer
       type. This rule is suppressed because when the body is of transfer
       encoding chunked, the body must be copied over the chunk headers that
       precede it. This is done to have a contiguous response body. This does
       affect future parsing as the changed segment will always be before the
       next place to parse.

#### Rule 18.3
_Ref 18.3.1_

-  MISRA Rule 18.3 flags pLoc and pNextWriteLoc as pointing to two different
       objects. This rule is suppressed because both pNextWriteLoc and pLoc
       point to a location in the response buffer.

#### Rule 21.13
_Ref 21.13.1_

-  MISRA Rule 21.13 flags any value passed into a ctype.h function that isn't cast
        as an unsigned char. Thorough testing by use of our CBMC proofs shows that adding
        the cast to ( unsigned char ) inside of the toupper() call has potential to lead
        to errors. Due to this we suppress this warning for our use case.

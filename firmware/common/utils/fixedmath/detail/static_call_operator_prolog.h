#ifdef STATIC_CALL_OPERATOR_INCLUDED
#error "Multiple inclusion of static_call_operator"
#endif
#define STATIC_CALL_OPERATOR_INCLUDED

#pragma push_macro("static_constexpr")
#pragma push_macro("static_call_operator")
#pragma push_macro("static_call_operator_const")

#if __cplusplus >= 202301L && defined(__cpp_static_call_operator)
#define static_call_operator static
#define static_call_operator_const
#else
#define static_call_operator
#define static_call_operator_const const
#endif


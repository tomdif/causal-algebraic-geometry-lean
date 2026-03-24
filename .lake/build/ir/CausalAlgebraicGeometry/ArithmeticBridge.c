// Lean compiler output
// Module: CausalAlgebraicGeometry.ArithmeticBridge
// Imports: public import Init public import Mathlib.NumberTheory.ArithmeticFunction.Moebius public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra public import Mathlib.Data.Nat.Prime.Basic public import CausalAlgebraicGeometry.CausalAlgebra public import CausalAlgebraicGeometry.CausalPrimality
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Nat_decidable__dvd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg(lean_object*);
lean_object* lp_mathlib_Nat_divisors(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
static lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0;
static lean_object* _init_lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_Nat_decidable__dvd___boxed), 2, 0);
x_4 = lp_mathlib_Nat_divisors(x_1);
x_5 = lp_mathlib_Multiset_attach___redArg(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_Moebius(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_Enumerative_IncidenceAlgebra(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Prime_Basic(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_Moebius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_Enumerative_IncidenceAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Prime_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0 = _init_lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0();
lean_mark_persistent(lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge_divCAlg___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

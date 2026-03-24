// Lean compiler output
// Module: CausalAlgebraicGeometry.CSpecSheaf
// Imports: public import Init public import Mathlib.Order.Basic public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Finset.Basic public import CausalAlgebraicGeometry.CausalAlgebra public import CausalAlgebraicGeometry.CausalPrimality
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_6);
x_8 = lean_apply_2(x_3, x_6, x_4);
x_9 = lean_apply_2(x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__0), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_3);
x_9 = lp_mathlib_Finset_sum___redArg(x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_closure((void*)(lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg___lam__1___boxed), 7, 5);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf_cornerMul(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

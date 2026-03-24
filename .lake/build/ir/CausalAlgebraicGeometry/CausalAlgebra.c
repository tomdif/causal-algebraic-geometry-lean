// Lean compiler output
// Module: CausalAlgebraicGeometry.CausalAlgebra
// Imports: public import Init public import Mathlib.Algebra.Algebra.Basic public import Mathlib.Order.Basic public import Mathlib.Data.Matrix.Basic public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Finset.Basic public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_idempotent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_idempotent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_idempotent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
lean_inc_ref(x_12);
lean_inc(x_3);
x_13 = lean_apply_2(x_12, x_4, x_3);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec(x_3);
goto block_11;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_apply_2(x_12, x_5, x_3);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lp_mathlib_Field_toDivisionRing___redArg(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec_ref(x_20);
return x_21;
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_6);
x_8 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_7);
x_9 = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_idempotent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_idempotent___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_fromFinitePoset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
lean_inc(x_2);
x_5 = lp_mathlib_Multiset_product___redArg(x_2, x_2);
x_6 = lp_mathlib_Multiset_filter___redArg(x_4, x_5);
x_7 = l_List_lengthTR___redArg(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra_algebraDim(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Algebra_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Matrix_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Algebra_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Matrix_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

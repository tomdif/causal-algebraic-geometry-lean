// Lean compiler output
// Module: CausalAlgebraicGeometry
// Imports: public import Init public import CausalAlgebraicGeometry.CausalAlgebra public import CausalAlgebraicGeometry.CausalPrimality public import CausalAlgebraicGeometry.NoetherianRatio public import CausalAlgebraicGeometry.ArithmeticBridge public import CausalAlgebraicGeometry.CSpecSheaf public import CausalAlgebraicGeometry.OrderComplexCohomology
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_NoetherianRatio(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf(uint8_t builtin);
lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_OrderComplexCohomology(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CausalPrimality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_NoetherianRatio(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_ArithmeticBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_CSpecSheaf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CausalAlgebraicGeometry_CausalAlgebraicGeometry_OrderComplexCohomology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

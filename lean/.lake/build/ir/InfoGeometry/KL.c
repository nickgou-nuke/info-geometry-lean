// Lean compiler output
// Module: InfoGeometry.KL
// Imports: public import Init public import InfoGeometry.KL.Finite public import InfoGeometry.KL.Measure
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
lean_object* initialize_infogeometry_InfoGeometry_KL_Finite(uint8_t builtin);
lean_object* initialize_infogeometry_InfoGeometry_KL_Measure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_infogeometry_InfoGeometry_KL(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_infogeometry_InfoGeometry_KL_Finite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_infogeometry_InfoGeometry_KL_Measure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

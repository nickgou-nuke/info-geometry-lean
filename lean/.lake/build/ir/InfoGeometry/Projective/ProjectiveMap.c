// Lean compiler output
// Module: InfoGeometry.Projective.ProjectiveMap
// Imports: public import Init public import InfoGeometry.Projective.Rays public import InfoGeometry.Clifford.Grading public import Mathlib
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
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_info_x2dgeometry_projectiveMap(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_info_x2dgeometry_projectiveMapEven___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_info_x2dgeometry_projectiveMapEven(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_info_x2dgeometry_InfoGeometry_Projective_Rays(uint8_t builtin);
lean_object* initialize_info_x2dgeometry_InfoGeometry_Clifford_Grading(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_info_x2dgeometry_InfoGeometry_Projective_ProjectiveMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_info_x2dgeometry_InfoGeometry_Projective_Rays(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_info_x2dgeometry_InfoGeometry_Clifford_Grading(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

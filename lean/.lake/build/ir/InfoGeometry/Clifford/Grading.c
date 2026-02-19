// Lean compiler output
// Module: InfoGeometry.Clifford.Grading
// Imports: public import Init public import InfoGeometry.Clifford.Cl11 public import InfoGeometry.Core.Involution public import Mathlib.Algebra.Lie.OfAssociative public import Mathlib.Algebra.Lie.Submodule
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
lean_object* lp_mathlib_LinearMap_comp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_oddSubmodule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_oddSubmodule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_infogeometry_modularJInvolution___closed__0;
LEAN_EXPORT lean_object* lp_infogeometry_modularJInvolution___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_evenLieSubalgebra___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_infogeometry_modularJ___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_clmComm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_evenLieSubalgebra(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_modularJInvolution(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_6 = lp_mathlib_LinearMap_comp___redArg(x_2, x_3);
lean_inc_ref(x_4);
x_7 = lean_apply_1(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lp_mathlib_LinearMap_comp___redArg(x_3, x_2);
x_11 = lean_apply_1(x_10, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_5);
x_15 = lean_apply_2(x_5, x_8, x_13);
x_16 = lean_apply_2(x_5, x_9, x_14);
lean_ctor_set(x_11, 1, x_16);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_5);
x_19 = lean_apply_2(x_5, x_8, x_17);
x_20 = lean_apply_2(x_5, x_9, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(lp_infogeometry_clmComm___redArg___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_clmComm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_infogeometry_clmComm___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_clmComm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_infogeometry_clmComm(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_lp_infogeometry_modularJInvolution___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_infogeometry_modularJ___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_modularJInvolution(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_infogeometry_modularJInvolution___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_modularJInvolution___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_infogeometry_modularJInvolution(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_evenLieSubalgebra(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_evenLieSubalgebra___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_infogeometry_evenLieSubalgebra(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_oddSubmodule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_oddSubmodule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_infogeometry_oddSubmodule(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_5 = lp_infogeometry_clmComm___redArg(x_1, x_2, x_3);
x_6 = lp_infogeometry_clmComm___redArg(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_infogeometry_oddTriple___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_infogeometry_oddTriple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_infogeometry_oddTriple(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_infogeometry_InfoGeometry_Clifford_Cl11(uint8_t builtin);
lean_object* initialize_infogeometry_InfoGeometry_Core_Involution(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Lie_OfAssociative(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Lie_Submodule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_infogeometry_InfoGeometry_Clifford_Grading(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_infogeometry_InfoGeometry_Clifford_Cl11(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_infogeometry_InfoGeometry_Core_Involution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Lie_OfAssociative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Lie_Submodule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_infogeometry_modularJInvolution___closed__0 = _init_lp_infogeometry_modularJInvolution___closed__0();
lean_mark_persistent(lp_infogeometry_modularJInvolution___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

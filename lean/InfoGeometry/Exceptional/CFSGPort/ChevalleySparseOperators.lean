/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Sparse.lean and RootOps/Poly.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootBasis

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

/-- An external sparse entry: input index, output index, integer coefficient. -/
abbrev Entry := ℕ × ℕ × ℤ

variable (τ R) in
/-- Interpret sparse entries as endomorphisms of the actual root module. -/
@[expose] def entriesOp (L : List Entry) : Module.End R (RootModule τ R) :=
  (L.map fun e => (e.2.2 : R) • (posCoord τ R e.1).smulRight (posVec τ R e.2.1)).sum

@[simp] theorem entriesOp_nil : entriesOp τ R [] = 0 := rfl

theorem entriesOp_append (L M : List Entry) :
    entriesOp τ R (L ++ M) = entriesOp τ R L + entriesOp τ R M := by
  simp [entriesOp]

/-- Matrix-unit composition with the input/output convention of the
external certificates. The order of composition is explicit. -/
theorem entriesOp_single_mul_single (e f : Entry) (hf : f.2.1 < dim τ) :
    entriesOp τ R [e] * entriesOp τ R [f] =
      if e.1 = f.2.1 then entriesOp τ R [(f.1, e.2.1, e.2.2 * f.2.2)] else 0 := by
  refine LinearMap.ext fun v => ?_
  simp only [entriesOp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
    posCoord_posVec hf]
  split_ifs with h
  · simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, Int.cast_mul]
    module
  · simp

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

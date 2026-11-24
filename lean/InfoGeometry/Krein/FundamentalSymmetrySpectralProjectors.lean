/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

/-!
# Fundamental-symmetry spectral projectors on an involutive self-dual carrier

Retrieval context (authority `retrieval_context_only`, never Lean proof evidence):
`2103.04372v1` §4 states that a Krein space admits the canonical decomposition
`V = H₊ ⊕ H₋`, that the orthoprojectors `P±` are deduced from it, and that the
fundamental symmetry is `J = P₊ − P₋`.  `mccrimmon_jordan` §6.1 motivates the
Peirce/idempotent decomposition technique.

This module proves the algebraic half of that statement for the existing
`InvolutiveSelfDualCarrier`: from the fundamental symmetry `J` (with `J² = 1`)
it builds the complementary idempotents

```
P₊^J = (1 + J)/2,   P₋^J = (1 - J)/2
```

and proves the full projector algebra together with `P₊^J − P₋^J = J` and the
eigenspace characterizations.  No positivity of the induced form is asserted
here: that needs a positive/negative-definiteness hypothesis on `H±`, which is
not part of the carrier structure.  The symmetry of the induced form
`[J u, v]` *is* proved from the existing invariance and symmetry fields.
-/

noncomputable section

namespace InfoGeometry.Krein.FundamentalSymmetrySpectralProjectors

open InfoGeometry.Krein
open InfoGeometry.Krein.InvolutiveSelfDualCarrier

variable (X : InvolutiveSelfDualCarrier)

/-- The `+1` spectral projector of the fundamental symmetry: `P₊ = (1 + J)/2`. -/
def jPlus : X.H →L[ℝ] X.H :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ X.H + X.J)

/-- The `-1` spectral projector of the fundamental symmetry: `P₋ = (1 - J)/2`. -/
def jMinus : X.H →L[ℝ] X.H :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ X.H - X.J)

@[simp] theorem jPlus_apply (x : X.H) :
    jPlus X x = (2 : ℝ)⁻¹ • (x + X.J x) := by
  rfl

@[simp] theorem jMinus_apply (x : X.H) :
    jMinus X x = (2 : ℝ)⁻¹ • (x - X.J x) := by
  rfl

/-- The two involutions relate by `K = Jε`, so `J` is a linear involution. -/
private theorem j_apply_apply (x : X.H) : X.J (X.J x) = x := by
  have h := congrArg (fun f : X.H →L[ℝ] X.H => f x) X.J_sq
  simpa [ContinuousLinearMap.comp_apply] using h

@[simp] theorem jPlus_idempotent : jPlus X ∘L jPlus X = jPlus X := by
  ext x
  simp [jPlus, j_apply_apply (X := X)]
  module

@[simp] theorem jMinus_idempotent : jMinus X ∘L jMinus X = jMinus X := by
  ext x
  simp [jMinus, j_apply_apply (X := X), sub_eq_add_neg]
  module

@[simp] theorem jPlus_comp_jMinus : jPlus X ∘L jMinus X = 0 := by
  ext x
  simp [jPlus, jMinus, j_apply_apply (X := X), sub_eq_add_neg]
  module

@[simp] theorem jMinus_comp_jPlus : jMinus X ∘L jPlus X = 0 := by
  ext x
  simp [jPlus, jMinus, j_apply_apply (X := X), sub_eq_add_neg]

/-- The canonical decomposition `P₊ + P₋ = 1`. -/
@[simp] theorem jPlus_add_jMinus : jPlus X + jMinus X = ContinuousLinearMap.id ℝ X.H := by
  ext x
  simp [jPlus, jMinus]
  module

/-- The fundamental symmetry is recovered as `J = P₊ − P₋`. -/
theorem j_eq_jPlus_sub_jMinus : X.J = jPlus X - jMinus X := by
  ext x
  simp [jPlus, jMinus]
  module

theorem jPlus_sub_jMinus : jPlus X - jMinus X = X.J := by
  exact j_eq_jPlus_sub_jMinus (X := X) |>.symm

/-- The `+1` eigenspace of `J` is exactly the range characterization of `P₊`. -/
theorem jPlus_apply_eq_self_iff (x : X.H) : jPlus X x = x ↔ X.J x = x := by
  constructor
  · intro h
    have hx : (2 : ℝ)⁻¹ • (x + X.J x) = x := by simpa [jPlus] using h
    have hmul := congrArg (fun v : X.H => (2 : ℝ) • v) hx
    have hsum : x + X.J x = x + x := by
      have h2 : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := by norm_num
      simpa [smul_add, h2, two_smul] using hmul
    exact add_left_cancel hsum
  · intro h
    rw [jPlus_apply, h]
    module

/-- The `-1` eigenspace of `J` is exactly the range characterization of `P₋`. -/
theorem jMinus_apply_eq_self_iff (x : X.H) : jMinus X x = x ↔ X.J x = -x := by
  constructor
  · intro h
    have hx : (2 : ℝ)⁻¹ • (x - X.J x) = x := by simpa [jMinus] using h
    have hmul := congrArg (fun v : X.H => (2 : ℝ) • v) hx
    have hdiff : x + (-X.J x) = x + x := by
      have h2 : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := by norm_num
      simpa [sub_eq_add_neg, smul_add, smul_neg, h2, two_smul] using hmul
    have hneg : -X.J x = x := add_left_cancel hdiff
    simpa using congrArg Neg.neg hneg
  · intro h
    rw [jMinus_apply, h, sub_neg_eq_add, smul_add]
    rw [← add_smul]
    norm_num

/-- The form induced by the fundamental symmetry, `(u, v) ↦ [J u, v]`, is
symmetric.  This follows from the carrier's pairing symmetry and `J`
-invariance; positive definiteness is not claimed. -/
theorem inducedForm_symmetric (u v : X.H) :
    X.kreinPairing (X.J u) v = X.kreinPairing (X.J v) u := by
  calc
    X.kreinPairing (X.J u) v = X.kreinPairing (X.J u) (X.J (X.J v)) := by
      rw [j_apply_apply (X := X) v]
    _ = X.kreinPairing u (X.J v) := X.pairing_J_invariant u (X.J v)
    _ = X.kreinPairing (X.J v) u := X.pairing_symm _ _

end InfoGeometry.Krein.FundamentalSymmetrySpectralProjectors

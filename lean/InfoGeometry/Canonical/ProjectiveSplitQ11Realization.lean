import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.State
import InfoGeometry.Projective.Dynamics
import InfoGeometry.Quantum.RealSplitClifford

open scoped LinearAlgebra.Projectivization

/-!
# InfoGeometry.Canonical.ProjectiveSplitQ11Realization

This module is a **coherence surface**, not a new owner.

It records the exact junction between two already-existing presentations:

- the repo-native pointed ray quotient `Projective.ProjectiveState`, which keeps a
  distinguished vacuum class; and
- the Mathlib-standard projectivization `ℙ ℝ (DoubledSpace E)`, which excludes
  the vacuum by construction.

The file therefore works on the **nonvacuum** part of the old quotient. On that
surface it proves:

1. the old pointed quotient and the Mathlib projectivization are equivalent;
2. the doubled operators `J`, `ε`, and `I = J ∘ ε` descend compatibly across
   that equivalence; and
3. the existing doubled-space split-`Cl(1,1)` realization from
   `RealSplitClifford.lean` is the Clifford hinge for this comparison.

What does **not** descend here is the old distinguished vacuum point itself.
That remains an upstairs / pointed-quotient feature and is not silently erased.
-/

namespace InfoGeometry.Canonical.ProjectiveSplitQ11Realization

open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The Mathlib-standard projectivization of the doubled carrier. -/
abbrev MathlibProjectiveCarrier : Type := InfoGeometry.Convex.ProjectiveState (E := E)

/-- The strict Mathlib projective class of a nonzero doubled vector. -/
noncomputable def strictProjectivize (v : H₂) (hv : v ≠ 0) :
    InfoGeometry.Convex.ProjectiveState (E := E) :=
  InfoGeometry.Convex.projectivize (E := E) v hv

omit [CompleteSpace E] in
lemma same_ray_nonzero_right {v w : H₂}
    (h : InfoGeometry.Projective.same_ray v w) (hv : v ≠ 0) :
    w ≠ 0 := by
  intro hw
  rcases h with ⟨a, ha, hwa⟩
  rw [hw] at hwa
  have hsmul : a • v = 0 := by simpa using hwa.symm
  exact hv ((smul_eq_zero.mp hsmul).elim (fun ha0 => (ha ha0).elim) id)

omit [CompleteSpace E] in
lemma strict_projectivize_eq_of_same_ray {v w : H₂}
    (h : InfoGeometry.Projective.same_ray v w) (hv : v ≠ 0) (hw : w ≠ 0) :
    strictProjectivize v hv = strictProjectivize w hw := by
  rcases h with ⟨a, ha, rfl⟩
  simpa [strictProjectivize] using
    (InfoGeometry.Convex.projectivize_smul (E := E) a ha v hv).symm

lemma pointed_projectivize_ne_vacuum (v : H₂) (hv : v ≠ 0) :
    InfoGeometry.Projective.projectivize (E := E) v ≠
      InfoGeometry.Projective.vacuum (E := E) := by
  intro h
  have hsame : InfoGeometry.Projective.same_ray v (0 : H₂) := by
    exact (InfoGeometry.Projective.projectivize_eq_iff).mp (by
      simpa [InfoGeometry.Projective.vacuum] using h)
  exact (same_ray_nonzero_right hsame hv) rfl

lemma pointed_out_nonzero
    (q : { q : InfoGeometry.Projective.ProjectiveState (E := E) //
        q ≠ InfoGeometry.Projective.vacuum (E := E) }) :
    Quotient.out q.1 ≠ (0 : H₂) := by
  intro hout
  apply q.2
  calc
    q.1 = InfoGeometry.Projective.projectivize (E := E) (Quotient.out q.1) := by
      symm
      exact Quotient.out_eq' q.1
    _ = InfoGeometry.Projective.vacuum (E := E) := by
      simp [InfoGeometry.Projective.vacuum, hout]

/-- The canonical map from the nonvacuum pointed quotient to Mathlib projectivization. -/
noncomputable def projectiveRay_toMathlibProjectivization
    (q : { q : InfoGeometry.Projective.ProjectiveState (E := E) //
        q ≠ InfoGeometry.Projective.vacuum (E := E) }) :
    InfoGeometry.Convex.ProjectiveState (E := E) :=
  let v : DoubledSpace E := Quotient.out q.1
  strictProjectivize v (by simpa [v] using pointed_out_nonzero q)

@[simp] theorem projectiveRay_toMathlibProjectivization_projectivize
    (v : H₂) (hv : v ≠ 0) :
    projectiveRay_toMathlibProjectivization
        ⟨InfoGeometry.Projective.projectivize (E := E) v,
          pointed_projectivize_ne_vacuum v hv⟩
      =
    strictProjectivize v hv := by
  let q :
      { q : InfoGeometry.Projective.ProjectiveState (E := E) //
        q ≠ InfoGeometry.Projective.vacuum (E := E) } :=
    ⟨InfoGeometry.Projective.projectivize (E := E) v,
      pointed_projectivize_ne_vacuum v hv⟩
  have hclass :
      InfoGeometry.Projective.projectivize (E := E) (Quotient.out q.1) =
        InfoGeometry.Projective.projectivize (E := E) v := by
    calc
      InfoGeometry.Projective.projectivize (E := E) (Quotient.out q.1) = q.1 := by
        exact Quotient.out_eq' q.1
      _ = InfoGeometry.Projective.projectivize (E := E) v := rfl
  exact strict_projectivize_eq_of_same_ray
    ((InfoGeometry.Projective.projectivize_eq_iff).mp hclass)
    (pointed_out_nonzero q) hv

/-- The canonical map from Mathlib projectivization back to the nonvacuum pointed quotient. -/
noncomputable def mathlibProjectivization_toProjectiveRay
    (q : InfoGeometry.Convex.ProjectiveState (E := E)) :
    { q : InfoGeometry.Projective.ProjectiveState (E := E) //
      q ≠ InfoGeometry.Projective.vacuum (E := E) } :=
  let v : DoubledSpace E := q.rep
  ⟨InfoGeometry.Projective.projectivize (E := E) v,
    pointed_projectivize_ne_vacuum v (by simpa [v] using q.rep_nonzero)⟩

@[simp] theorem projectiveRay_toMathlibProjectivization_fromMathlibProjectivization
    (q : InfoGeometry.Convex.ProjectiveState (E := E)) :
    projectiveRay_toMathlibProjectivization
      (mathlibProjectivization_toProjectiveRay q) = q := by
  let r :
      { q : InfoGeometry.Projective.ProjectiveState (E := E) //
        q ≠ InfoGeometry.Projective.vacuum (E := E) } :=
    mathlibProjectivization_toProjectiveRay q
  have hclass :
      InfoGeometry.Projective.projectivize (E := E) (Quotient.out r.1) =
        InfoGeometry.Projective.projectivize (E := E) q.rep := by
    calc
      InfoGeometry.Projective.projectivize (E := E) (Quotient.out r.1) = r.1 := by
        exact Quotient.out_eq' r.1
      _ = InfoGeometry.Projective.projectivize (E := E) q.rep := rfl
  have hstrict : strictProjectivize q.rep q.rep_nonzero = q := by
    unfold strictProjectivize InfoGeometry.Convex.projectivize
    exact Projectivization.mk_rep (K := ℝ) (v := q)
  calc
    projectiveRay_toMathlibProjectivization (mathlibProjectivization_toProjectiveRay q)
      = strictProjectivize (Quotient.out r.1) (pointed_out_nonzero r) := by
          rfl
    _ = strictProjectivize q.rep q.rep_nonzero := by
          exact strict_projectivize_eq_of_same_ray
            ((InfoGeometry.Projective.projectivize_eq_iff).mp hclass)
            (pointed_out_nonzero r) q.rep_nonzero
    _ = q := hstrict

@[simp] theorem mathlibProjectivization_toProjectiveRay_toMathlibProjectivization
    (q : { q : InfoGeometry.Projective.ProjectiveState (E := E) //
        q ≠ InfoGeometry.Projective.vacuum (E := E) }) :
    mathlibProjectivization_toProjectiveRay
      (projectiveRay_toMathlibProjectivization q) = q := by
  apply Subtype.ext
  change InfoGeometry.Projective.projectivize (E := E)
      (projectiveRay_toMathlibProjectivization q).rep = q.1
  let v : H₂ := Quotient.out q.1
  have hv : v ≠ 0 := pointed_out_nonzero q
  obtain ⟨a, ha⟩ :=
    Projectivization.exists_smul_eq_mk_rep (K := ℝ) (v := v) hv
  calc
    InfoGeometry.Projective.projectivize (E := E)
        (projectiveRay_toMathlibProjectivization q).rep
      =
    InfoGeometry.Projective.projectivize (E := E) (a • v) := by
      simpa [projectiveRay_toMathlibProjectivization, strictProjectivize, v,
        InfoGeometry.Convex.projectivize] using
          congrArg (InfoGeometry.Projective.projectivize (E := E)) ha.symm
    _ = InfoGeometry.Projective.projectivize (E := E) v := by
      exact InfoGeometry.Projective.projectivize_smul (E := E) a v
    _ = q.1 := by
      change InfoGeometry.Projective.projectivize (E := E) (Quotient.out q.1) = q.1
      exact Quotient.out_eq' q.1

/-- The two projective presentations coincide away from the distinguished vacuum point. -/
noncomputable def projectiveRay_equiv_mathlibProjectivization :
    { q : InfoGeometry.Projective.ProjectiveState (E := E) //
      q ≠ InfoGeometry.Projective.vacuum (E := E) } ≃
      InfoGeometry.Convex.ProjectiveState (E := E) where
  toFun := projectiveRay_toMathlibProjectivization
  invFun := mathlibProjectivization_toProjectiveRay
  left_inv := mathlibProjectivization_toProjectiveRay_toMathlibProjectivization
  right_inv := projectiveRay_toMathlibProjectivization_fromMathlibProjectivization

lemma complex_i_injective :
    Function.Injective (InfoGeometry.Krein.complex_i (E := E)) := by
  intro x y hxy
  have hJ : Function.Injective (InfoGeometry.Krein.modular_j (E := E)) :=
    (InfoGeometry.Krein.modular_jLE (E := E)).injective
  have hε : Function.Injective (InfoGeometry.Krein.spectral_epsilon (E := E)) :=
    (InfoGeometry.Krein.spectral_epsilonLE (E := E)).injective
  apply hε
  apply hJ
  simpa [InfoGeometry.Krein.complex_i] using hxy

/-- The descended Mathlib projective action of `J`. -/
noncomputable def mathlibProjectiveJ :
    InfoGeometry.Convex.ProjectiveState (E := E) → InfoGeometry.Convex.ProjectiveState (E := E) :=
  Projectivization.map (InfoGeometry.Krein.modular_jLE (E := E)).toLinearMap
    (InfoGeometry.Krein.modular_jLE (E := E)).injective

/-- The descended Mathlib projective action of `ε`. -/
noncomputable def mathlibProjectiveEpsilon :
    InfoGeometry.Convex.ProjectiveState (E := E) → InfoGeometry.Convex.ProjectiveState (E := E) :=
  Projectivization.map (InfoGeometry.Krein.spectral_epsilonLE (E := E)).toLinearMap
    (InfoGeometry.Krein.spectral_epsilonLE (E := E)).injective

/-- The descended Mathlib projective action of `I = J ∘ ε`. -/
noncomputable def mathlibProjectiveI :
    InfoGeometry.Convex.ProjectiveState (E := E) → InfoGeometry.Convex.ProjectiveState (E := E) :=
  Projectivization.map (InfoGeometry.Krein.complex_i (E := E)).toLinearMap
    (complex_i_injective (E := E))

lemma modular_j_ne_zero {v : H₂} (hv : v ≠ 0) :
    InfoGeometry.Krein.modular_j (E := E) v ≠ 0 := by
  intro h0
  have h00 :
      InfoGeometry.Krein.modular_j (E := E) v = InfoGeometry.Krein.modular_j (E := E) 0 := by
    simpa using h0
  exact hv ((InfoGeometry.Krein.modular_jLE (E := E)).injective h00)

lemma spectral_epsilon_ne_zero {v : H₂} (hv : v ≠ 0) :
    InfoGeometry.Krein.spectral_epsilon (E := E) v ≠ 0 := by
  intro h0
  have h00 :
      InfoGeometry.Krein.spectral_epsilon (E := E) v
        = InfoGeometry.Krein.spectral_epsilon (E := E) 0 := by
    simpa using h0
  exact hv ((InfoGeometry.Krein.spectral_epsilonLE (E := E)).injective h00)

lemma complex_i_ne_zero {v : H₂} (hv : v ≠ 0) :
    InfoGeometry.Krein.complex_i (E := E) v ≠ 0 := by
  intro h0
  have h00 :
      InfoGeometry.Krein.complex_i (E := E) v
        = InfoGeometry.Krein.complex_i (E := E) 0 := by
    simpa using h0
  exact hv ((complex_i_injective) h00)

@[simp] theorem mathlibProjectiveJ_projectivize (v : H₂) (hv : v ≠ 0) :
    mathlibProjectiveJ (E := E) (strictProjectivize v hv)
      =
    strictProjectivize (InfoGeometry.Krein.modular_j (E := E) v) (modular_j_ne_zero (E := E) hv) := by
  rfl

@[simp] theorem mathlibProjectiveEpsilon_projectivize (v : H₂) (hv : v ≠ 0) :
    mathlibProjectiveEpsilon (E := E) (strictProjectivize v hv)
      =
    strictProjectivize
      (InfoGeometry.Krein.spectral_epsilon (E := E) v) (spectral_epsilon_ne_zero (E := E) hv) := by
  rfl

@[simp] theorem mathlibProjectiveI_projectivize (v : H₂) (hv : v ≠ 0) :
    mathlibProjectiveI (E := E) (strictProjectivize v hv)
      =
    strictProjectivize
      (InfoGeometry.Krein.complex_i (E := E) v) (complex_i_ne_zero (E := E) hv) := by
  rfl

/-- `J` descends compatibly on the old nonvacuum quotient and the Mathlib projectivization. -/
theorem doubled_modular_j_descends_compatibly (v : H₂) (hv : v ≠ 0) :
      projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.J (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.modular_j (E := E) v) (modular_j_ne_zero hv)⟩
      =
    mathlibProjectiveJ (strictProjectivize v hv) := by
  calc
    projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.J (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.modular_j (E := E) v) (modular_j_ne_zero hv)⟩
      = strictProjectivize (InfoGeometry.Krein.modular_j (E := E) v) (modular_j_ne_zero hv) := by
          simpa [projectiveRay_equiv_mathlibProjectivization,
            InfoGeometry.ProjectiveDynamics.J_projectivize] using
            (projectiveRay_toMathlibProjectivization_projectivize
              (v := InfoGeometry.Krein.modular_j (E := E) v)
              (hv := modular_j_ne_zero hv))
    _ = mathlibProjectiveJ (strictProjectivize v hv) := by
          exact (mathlibProjectiveJ_projectivize (E := E) (v := v) (hv := hv)).symm

/-- `ε` descends compatibly on the old nonvacuum quotient and the Mathlib projectivization. -/
theorem doubled_spectral_epsilon_descends_compatibly (v : H₂) (hv : v ≠ 0) :
      projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.epsilon (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.spectral_epsilon (E := E) v)
            (spectral_epsilon_ne_zero hv)⟩
      =
    mathlibProjectiveEpsilon (strictProjectivize v hv) := by
  calc
    projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.epsilon (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.spectral_epsilon (E := E) v)
            (spectral_epsilon_ne_zero hv)⟩
      = strictProjectivize
          (InfoGeometry.Krein.spectral_epsilon (E := E) v) (spectral_epsilon_ne_zero hv) := by
          simpa [projectiveRay_equiv_mathlibProjectivization,
            InfoGeometry.ProjectiveDynamics.epsilon_projectivize] using
            (projectiveRay_toMathlibProjectivization_projectivize
              (v := InfoGeometry.Krein.spectral_epsilon (E := E) v)
              (hv := spectral_epsilon_ne_zero hv))
    _ = mathlibProjectiveEpsilon (strictProjectivize v hv) := by
          exact
            (mathlibProjectiveEpsilon_projectivize (E := E) (v := v) (hv := hv)).symm

/-- `I = J ∘ ε` descends compatibly on the old nonvacuum quotient and the Mathlib projectivization. -/
theorem doubled_phaseAxis_descends_compatibly (v : H₂) (hv : v ≠ 0) :
      projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.I (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.complex_i (E := E) v) (complex_i_ne_zero hv)⟩
      =
    mathlibProjectiveI (strictProjectivize v hv) := by
  calc
    projectiveRay_equiv_mathlibProjectivization
        ⟨InfoGeometry.ProjectiveDynamics.I (E := E)
            (InfoGeometry.Projective.projectivize (E := E) v),
          pointed_projectivize_ne_vacuum
            (InfoGeometry.Krein.complex_i (E := E) v) (complex_i_ne_zero hv)⟩
      = strictProjectivize
          (InfoGeometry.Krein.complex_i (E := E) v) (complex_i_ne_zero hv) := by
          simpa [projectiveRay_equiv_mathlibProjectivization,
            InfoGeometry.ProjectiveDynamics.I_projectivize] using
            (projectiveRay_toMathlibProjectivization_projectivize
              (v := InfoGeometry.Krein.complex_i (E := E) v)
              (hv := complex_i_ne_zero hv))
    _ = mathlibProjectiveI (strictProjectivize v hv) := by
          exact (mathlibProjectiveI_projectivize (E := E) (v := v) (hv := hv)).symm

/-- The existing doubled-space split-`Cl(1,1)` realization is the Clifford hinge for this bridge. -/
theorem realSplitClifford_realizes_Q11 :
    (doubledSpaceCl11Action (E := E)).J
      =
        InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0))
    ∧
    (doubledSpaceCl11Action (E := E)).K
      =
        InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
    ∧
    (doubledSpaceCl11Action (E := E)).eps
      =
        InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
            * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  constructor
  · exact doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E)
  constructor
  · exact doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E)
  · exact doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar (E := E)

end InfoGeometry.Canonical.ProjectiveSplitQ11Realization

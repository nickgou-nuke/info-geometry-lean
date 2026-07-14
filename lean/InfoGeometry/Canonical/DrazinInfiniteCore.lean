import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Algebraic.Fitting
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinInfiniteCore

Infinite-dimensional operator core for the canonical Drazin lane.

This file separates:
- algebraic owner predicate: `Drazin.IsDrazinInverse`,
- spectral/ascent-descent/Riesz interfaces (assumption surfaces),
- constructive finite-dimensional bridge into a Riesz-style package.
-/

namespace InfoGeometry.Canonical.DrazinInfiniteCore

open InfoGeometry.Canonical

section AscentDescent

variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Kernel stabilization at index `k` (ascent interface). -/
@[rep_depth operator]
def AscentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  Algebraic.Fitting.AscentStabilized T k

/-- Range stabilization at index `k` (descent interface). -/
@[rep_depth operator]
def DescentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  Algebraic.Fitting.DescentStabilized T k

/-- Finite ascent/descent witness at the spectral point `0`. -/
@[rep_depth operator]
structure HasFiniteAscentDescentAtZero (T : Module.End K V) where
  k : ℕ
  ascent : AscentAtZero T k
  descent : DescentAtZero T k
  D : Module.End K V
  hIsDrazin : Drazin.IsDrazinInverse T D k

variable {T TD : Module.End K V} {k m : ℕ}

/--
Descent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse_le
    (hD : Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    DescentAtZero T m := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨TD x, ?_⟩
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      Drazin.IsDrazinInverse.power_le hD hm
    simpa using congrArg (fun f : Module.End K V => f x) hPow
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨T x, ?_⟩
    simp [pow_succ]

/--
Ascent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse_le
    (hD : Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    AscentAtZero T m := by
  apply le_antisymm
  · intro x hx
    change (T ^ (m + 1)) x = 0
    have hx0 : (T ^ m) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    calc
      (T ^ (m + 1)) x = (T * T ^ m) x := by simp [pow_succ']
      _ = T ((T ^ m) x) := rfl
      _ = T 0 := by rw [hx0]
      _ = 0 := by simp
  · intro x hx
    change (T ^ m) x = 0
    have hx0 : (T ^ (m + 1)) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      Drazin.IsDrazinInverse.power_le hD hm
    have hCommute : Commute T TD := Drazin.IsDrazinInverse.comm hD
    have hPowComm : T ^ (m + 1) * TD = TD * T ^ (m + 1) :=
      (hCommute.pow_left (m + 1)).eq
    have hLeft : TD * T ^ (m + 1) = T ^ m := by
      calc
        TD * T ^ (m + 1) = T ^ (m + 1) * TD := hPowComm.symm
        _ = T ^ m := hPow
    calc
      (T ^ m) x = (TD * T ^ (m + 1)) x := by
        simpa using congrArg (fun f : Module.End K V => f x) hLeft.symm
      _ = TD ((T ^ (m + 1)) x) := rfl
      _ = TD 0 := by rw [hx0]
      _ = 0 := by simp

/-- Descent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    DescentAtZero T k :=
  descentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/-- Ascent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    AscentAtZero T k :=
  ascentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/--
Canonical Drazin witness induces a finite ascent/descent witness at zero.
-/
@[rep_depth operator]
def finiteAscentDescentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    HasFiniteAscentDescentAtZero T where
  k := k
  ascent := ascentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  descent := descentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  D := TD
  hIsDrazin := hD

/--
Finite ascent/descent interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', Drazin.IsDrazinInverse T TD' k' :=
  ⟨h.k, h.D, h.hIsDrazin⟩

/--
Compatibility readback theorem for finite ascent/descent packages that already
store a witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent_readback
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', Drazin.IsDrazinInverse T TD' k' :=
  ⟨h.k, h.D, h.hIsDrazin⟩

/--
**The Fitting Transition:**
Algebraically construct the Drazin inverse from stabilized ascent and descent.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_fitting {T : Module.End K V} {k : ℕ}
    (ha : AscentAtZero T k) (hd : DescentAtZero T k) :
    ∃ TD, Drazin.IsDrazinInverse T TD k := by
  let Ker : Submodule K V := (T ^ k).ker
  let Ran : Submodule K V := (T ^ k).range

  have hk : IsCompl Ker Ran :=
    Algebraic.Fitting.isCompl_ker_pow_range_pow (T := T) (k := k) ha hd

  let πRan : V →ₗ[K] Ran := Ran.linearProjOfIsCompl Ker hk.symm

  have hT_map_Ran : ∀ x : Ran, T x.1 ∈ Ran := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    refine ⟨T y, ?_⟩
    calc
      (T ^ k) (T y) = T ((T ^ k) y) := by
        calc
          (T ^ k) (T y) = (T ^ k * T) y := by rfl
          _ = (T ^ (k + 1)) y := by simp [pow_succ]
          _ = (T * T ^ k) y := by simp [pow_succ']
          _ = T ((T ^ k) y) := by rfl
      _ = T x.1 := by simp [hy]

  let TR : Ran →ₗ[K] Ran := LinearMap.codRestrict Ran (T ∘ₗ Ran.subtype) hT_map_Ran

  have hTR_surj : Function.Surjective TR := by
    intro y
    rcases Algebraic.Fitting.surjective_on_range (T := T) (k := k) hd y.1 y.2 with
      ⟨x, hx, hTx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [TR] using hTx

  have hTR_inj : Function.Injective TR := by
    intro x y hxy
    apply Subtype.ext
    have hxy_val : T x.1 = T y.1 := by
      exact congrArg Subtype.val hxy
    have hT_sub : T (x.1 - y.1) = 0 := by
      calc
        T (x.1 - y.1) = T x.1 - T y.1 := by simp [map_sub]
        _ = 0 := by simp [hxy_val]
    have h_sub_eq_zero : x.1 - y.1 = 0 :=
      Algebraic.Fitting.injective_on_range (T := T) (k := k) ha hd
        (x.1 - y.1) (Submodule.sub_mem Ran x.2 y.2) hT_sub
    exact sub_eq_zero.mp h_sub_eq_zero

  let eRan : Ran ≃ₗ[K] Ran := LinearEquiv.ofBijective TR ⟨hTR_inj, hTR_surj⟩

  let D : Module.End K V := Ran.subtype ∘ₗ (eRan.symm : Ran →ₗ[K] Ran) ∘ₗ πRan
  let P : Module.End K V := Ran.subtype ∘ₗ πRan

  have hT_mul_D : T * D = P := by
    ext x
    have hright : TR (eRan.symm (πRan x)) = πRan x := by
      exact eRan.apply_symm_apply (πRan x)
    calc
      (T * D) x = T (Ran.subtype (eRan.symm (πRan x))) := by rfl
      _ = Ran.subtype (TR (eRan.symm (πRan x))) := by rfl
      _ = Ran.subtype (πRan x) := by rw [hright]
      _ = P x := by rfl

  have hpowT_apply : ∀ z : V, (T ^ k) (T z) = T ((T ^ k) z) := by
    intro z
    calc
      (T ^ k) (T z) = (T ^ k * T) z := by rfl
      _ = (T ^ (k + 1)) z := by simp [pow_succ]
      _ = (T * T ^ k) z := by simp [pow_succ']
      _ = T ((T ^ k) z) := by rfl

  have hT_map_Ker : ∀ x ∈ Ker, T x ∈ Ker := by
    intro x hx
    have hx0 : (T ^ k) x = 0 := by
      simpa [Ker, LinearMap.mem_ker] using hx
    change (T ^ k) (T x) = 0
    calc
      (T ^ k) (T x) = T ((T ^ k) x) := hpowT_apply x
      _ = 0 := by simp [hx0]

  have hD_mul_T : D * T = P := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hTK : T (xK : V) ∈ Ker := hT_map_Ker xK xK.2
    have hπTK : πRan (T (xK : V)) = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right' hk.symm _ hTK
    have hTRxR : T (xR : V) ∈ Ran := hT_map_Ran xR
    have hπTRxR : πRan (T (xR : V)) = ⟨T xR, hTRxR⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨T xR, hTRxR⟩
    have hTRxR_eq : (⟨T xR, hTRxR⟩ : Ran) = TR xR := by
      apply Subtype.ext
      rfl
    have hleftInv : eRan.symm (TR xR) = xR := by
      exact eRan.symm_apply_apply xR
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    calc
      (D * T) x = D (T ((xK : V) + xR)) := by simp [hsum]
      _ = D (T (xK : V) + T xR) := by simp [map_add]
      _ = Ran.subtype (eRan.symm (πRan (T (xK : V) + T xR))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan (T (xK : V)) + πRan (T xR))) := by
        simp [map_add]
      _ = Ran.subtype (eRan.symm (0 + ⟨T xR, hTRxR⟩)) := by rw [hπTK, hπTRxR]
      _ = Ran.subtype (eRan.symm (TR xR)) := by
        rw [hTRxR_eq]
        simp
      _ = (xR : V) := by simp [hleftInv]
      _ = P ((xK : V) + xR) := by symm; exact hP_on_sum
      _ = P x := by simp [hsum]

  have hD_mem_Ran : ∀ x : V, D x ∈ Ran := by
    intro x
    unfold D
    exact (eRan.symm (πRan x)).2

  have hD_mul_P : D * P = D := by
    ext x
    have hπPx : πRan (P x) = πRan x := by
      unfold P
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm (πRan x)
    calc
      (D * P) x = Ran.subtype (eRan.symm (πRan (P x))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan x)) := by rw [hπPx]
      _ = D x := by rfl

  have hP_mul_D : P * D = D := by
    ext x
    have hπDx : πRan (D x) = ⟨D x, hD_mem_Ran x⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨D x, hD_mem_Ran x⟩
    calc
      (P * D) x = Ran.subtype (πRan (D x)) := by rfl
      _ = Ran.subtype ⟨D x, hD_mem_Ran x⟩ := by rw [hπDx]
      _ = D x := by rfl

  have hTk_mul_P : (T ^ k) * P = T ^ k := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    have hTk_xK : (T ^ k) (xK : V) = 0 := xK.2
    calc
      ((T ^ k) * P) x = (T ^ k) (P ((xK : V) + xR)) := by simp [hsum]
      _ = (T ^ k) (xR : V) := by rw [hP_on_sum]
      _ = (T ^ k) ((xK : V) + xR) := by simp [map_add, hTk_xK]
      _ = (T ^ k) x := by simp [hsum]

  have hIdem : D * T * D = D := by
    calc
      D * T * D = (D * T) * D := by simp [mul_assoc]
      _ = P * D := by rw [hD_mul_T]
      _ = D := hP_mul_D

  have hComm : T * D = D * T := by
    exact hT_mul_D.trans hD_mul_T.symm

  have hPow : T ^ (k + 1) * D = T ^ k := by
    calc
      T ^ (k + 1) * D = (T ^ k) * (T * D) := by simp [pow_succ, mul_assoc]
      _ = (T ^ k) * P := by rw [hT_mul_D]
      _ = T ^ k := hTk_mul_P

  exact ⟨D, Drazin.IsDrazinInverse.mk hComm hIdem hPow⟩

/--
Constructive finite ascent/descent bridge:
recover a Drazin witness from stabilization fields only (without using any
stored witness field from the interface package).
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent_constructive
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', Drazin.IsDrazinInverse T TD' k' := by
  rcases exists_drazinInverse_of_fitting (T := T) (k := h.k) h.ascent h.descent with
    ⟨TD, hD⟩
  exact ⟨h.k, TD, hD⟩

end AscentDescent

section SpectralInterfaces

variable {𝕂 E : Type*}
variable [NormedField 𝕂]
variable [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/--
Topological isolation interface for the spectral point `0`.

This is intentionally stated as neighborhood isolation to stay lightweight.
-/
@[rep_depth operator]
def ZeroIsolatedInSpectrum (T : E →L[𝕂] E) : Prop :=
  ∃ U : Set 𝕂, IsOpen U ∧ (0 : 𝕂) ∈ U ∧
    ∀ z : 𝕂, z ∈ U → z ∈ spectrum 𝕂 T → z = 0

/--
Riesz-style decomposition interface at `0` for a bounded operator.
-/
@[rep_depth operator]
structure HasClassicalRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  k : ℕ
  D : E →L[𝕂] E
  hIsDrazin : Drazin.IsDrazinInverse T D k
  hP : P = Drazin.IsDrazinInverse.projection T D

/--
Generalized Riesz-style interface at `0` for a bounded operator.

This is intentionally weaker than the classical finite-index Drazin lane:
the defect side is tracked via a separate quasinilpotent witness field.
-/
@[rep_depth operator]
structure HasGeneralizedRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  S : E →L[𝕂] E
  left_inverse_on_regular :
    (T * P) * S = P
  right_inverse_on_regular :
    S * (T * P) = P
  quasinilpotent_on_defect : Prop

/--
Witness-free constructive Riesz decomposition surface at `0`.

This owner carries only projector/splitting data and does not store a
preconstructed Drazin witness.
-/
@[rep_depth operator]
structure ConstructiveRieszDecompositionAtZero (T : E →L[𝕂] E) where
  k : ℕ
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  S : E →L[𝕂] E
  left_inverse_on_regular : S * T = P
  right_inverse_on_regular : T * S = P
  S_supported_on_regular_left : S * P = S
  S_supported_on_regular_right : P * S = S
  nilpotent_on_complement : T ^ k * (1 - P) = 0
/--
Foundational Drazin data: the inverse is not primitive, but is carried together
with the projector and defect-annihilation laws that define it.
-/
@[rep_depth operator]
structure ConstructiveDrazinData (T : E →L[𝕂] E) where
  k : ℕ
  projector : E →L[𝕂] E
  inverse : E →L[𝕂] E
  projector_idempotent : projector * projector = projector
  projector_comm : T * projector = projector * T
  left_inverse_on_regular : inverse * T = projector
  right_inverse_on_regular : T * inverse = projector
  inverse_supported_on_regular_left : inverse * projector = inverse
  inverse_supported_on_regular_right : projector * inverse = inverse
  nilpotent_on_defect : T ^ k * (1 - projector) = 0

/--
A constructive Riesz decomposition canonically induces the foundational Drazin
package.
-/
@[rep_depth operator]
def constructiveDrazinData_of_constructiveRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ConstructiveDrazinData (𝕂 := 𝕂) T where
  k := hR.k
  projector := hR.P
  inverse := hR.S
  projector_idempotent := hR.P_idempotent
  projector_comm := hR.PT_comm
  left_inverse_on_regular := hR.left_inverse_on_regular
  right_inverse_on_regular := hR.right_inverse_on_regular
  inverse_supported_on_regular_left := hR.S_supported_on_regular_left
  inverse_supported_on_regular_right := hR.S_supported_on_regular_right
  nilpotent_on_defect := hR.nilpotent_on_complement

/-- Recover constructive Riesz data from the foundational Drazin package. -/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := h.k
  P := h.projector
  P_idempotent := h.projector_idempotent
  PT_comm := h.projector_comm
  S := h.inverse
  left_inverse_on_regular := h.left_inverse_on_regular
  right_inverse_on_regular := h.right_inverse_on_regular
  S_supported_on_regular_left := h.inverse_supported_on_regular_left
  S_supported_on_regular_right := h.inverse_supported_on_regular_right
  nilpotent_on_complement := h.nilpotent_on_defect

/-- Candidate Drazin inverse extracted from constructive Riesz data. -/
@[rep_depth operator]
def constructiveDrazinCandidate
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    E →L[𝕂] E :=
  hR.S

/-- Candidate commutes with the base operator. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_comm
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    T * constructiveDrazinCandidate hR = constructiveDrazinCandidate hR * T := by
  calc
    T * constructiveDrazinCandidate hR = T * hR.S := rfl
    _ = hR.P := hR.right_inverse_on_regular
    _ = hR.S * T := hR.left_inverse_on_regular.symm
    _ = constructiveDrazinCandidate hR * T := rfl

/-- Candidate satisfies the inner Drazin law `D * T * D = D`. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_inner
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    constructiveDrazinCandidate hR * T * constructiveDrazinCandidate hR
      = constructiveDrazinCandidate hR := by
  calc
    constructiveDrazinCandidate hR * T * constructiveDrazinCandidate hR
        = (hR.S * T) * hR.S := by
            simp [constructiveDrazinCandidate, mul_assoc]
    _ = hR.P * hR.S := by rw [hR.left_inverse_on_regular]
    _ = hR.S := hR.S_supported_on_regular_right
    _ = constructiveDrazinCandidate hR := rfl

/-- Candidate satisfies the finite-index Drazin power law. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_power
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    T ^ (hR.k + 1) * constructiveDrazinCandidate hR = T ^ hR.k := by
  calc
    T ^ (hR.k + 1) * constructiveDrazinCandidate hR
        = T ^ hR.k * (T * hR.S) := by
            simp [constructiveDrazinCandidate, pow_succ, mul_assoc]
    _ = T ^ hR.k * hR.P := by rw [hR.right_inverse_on_regular]
    _ = T ^ hR.k * (1 - (1 - hR.P)) := by simp
    _ = T ^ hR.k * 1 - T ^ hR.k * (1 - hR.P) := by rw [mul_sub]
    _ = T ^ hR.k - 0 := by rw [mul_one, hR.nilpotent_on_complement]
    _ = T ^ hR.k := by simp

/--
Foundational constructive Drazin data already carries a canonical Drazin witness
for its stored inverse, without first re-expanding through the Riesz package.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    Drazin.IsDrazinInverse T h.inverse h.k := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · calc
      T * h.inverse = h.projector := h.right_inverse_on_regular
      _ = h.inverse * T := h.left_inverse_on_regular.symm
  · calc
      h.inverse * T * h.inverse = h.projector * h.inverse := by
          rw [h.left_inverse_on_regular]
      _ = h.inverse := h.inverse_supported_on_regular_right
  · calc
      T ^ (h.k + 1) * h.inverse = T ^ h.k * (T * h.inverse) := by
          simp [pow_succ, mul_assoc]
      _ = T ^ h.k * h.projector := by rw [h.right_inverse_on_regular]
      _ = T ^ h.k * (1 - (1 - h.projector)) := by simp
      _ = T ^ h.k * 1 - T ^ h.k * (1 - h.projector) := by rw [mul_sub]
      _ = T ^ h.k - 0 := by rw [mul_one, h.nilpotent_on_defect]
      _ = T ^ h.k := by simp

/--
Foundational constructive Drazin data yields a canonical existential Drazin
witness without first converting to a constructive Riesz package.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    ∃ k TD, Drazin.IsDrazinInverse T TD k :=
  ⟨h.k, h.inverse, isDrazinInverse_of_constructiveDrazinData (𝕂 := 𝕂) h⟩

/--
Constructive Riesz decomposition at `0` yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, Drazin.IsDrazinInverse T TD k := by
  refine ⟨hR.k, constructiveDrazinCandidate hR, ?_⟩
  exact Drazin.IsDrazinInverse.mk
    (constructiveDrazinCandidate_comm (hR := hR))
    (constructiveDrazinCandidate_inner (hR := hR))
    (constructiveDrazinCandidate_power (hR := hR))

/--
Compatibility adapter: recover constructive Riesz data from the legacy
classical witness-bearing interface.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := h.k
  P := h.P
  P_idempotent := h.P_idempotent
  PT_comm := h.PT_comm
  S := h.D
  left_inverse_on_regular := by
    calc
      h.D * T = T * h.D := h.hIsDrazin.comm.symm
      _ = Drazin.IsDrazinInverse.projection T h.D := by rfl
      _ = h.P := h.hP.symm
  right_inverse_on_regular := by
    calc
      T * h.D = Drazin.IsDrazinInverse.projection T h.D := by rfl
      _ = h.P := h.hP.symm
  S_supported_on_regular_left := by
    calc
      h.D * h.P = h.D * Drazin.IsDrazinInverse.projection T h.D := by rw [h.hP]
      _ = h.D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using
              h.hIsDrazin.idempotent
  S_supported_on_regular_right := by
    calc
      h.P * h.D = Drazin.IsDrazinInverse.projection T h.D * h.D := by rw [h.hP]
      _ = h.D * Drazin.IsDrazinInverse.projection T h.D := by
            simpa using Drazin.IsDrazinInverse.projection_comm (h := h.hIsDrazin)
      _ = h.D := by
            simpa [Drazin.IsDrazinInverse.projection, mul_assoc] using
              h.hIsDrazin.idempotent
  nilpotent_on_complement := by
    calc
      T ^ h.k * (1 - h.P)
          = T ^ h.k * (1 - Drazin.IsDrazinInverse.projection T h.D) := by rw [h.hP]
      _ = T ^ h.k * (1 - T * h.D) := by rfl
      _ = T ^ h.k - T ^ h.k * (T * h.D) := by rw [mul_sub, mul_one]
      _ = T ^ h.k - T ^ (h.k + 1) * h.D := by rw [pow_succ, mul_assoc]
      _ = T ^ h.k - T ^ h.k := by rw [h.hIsDrazin.power]
      _ = 0 := by simp

/--
Bundle of spectral interfaces commonly used for infinite-dimensional Drazin
existence statements.
-/
@[rep_depth operator]
structure DrazinInfiniteAssumptions (T : E →L[𝕂] E) where
  finite_ascent_descent : HasFiniteAscentDescentAtZero (K := 𝕂) (V := E) T.toLinearMap
  zero_isolated_spectrum : ZeroIsolatedInSpectrum (𝕂 := 𝕂) T
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T
  generalized_riesz : HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T

/--
The bundled infinite-dimensional Drazin assumptions already carry a classical
Riesz packet, so they recover the witness-free constructive Riesz surface
without reintroducing a separate `HasClassicalRieszDecompositionAtZero`
hypothesis.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T :=
  constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
    (𝕂 := 𝕂) h.classical_riesz

/--
The bundled infinite-dimensional Drazin assumptions already determine the
canonical Drazin witness attached to their classical Riesz field.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    Drazin.IsDrazinInverse T h.classical_riesz.D h.classical_riesz.k :=
  h.classical_riesz.hIsDrazin

/--
Bundled infinite-dimensional Drazin assumptions yield a Drazin inverse through
their owned classical Riesz component, removing the need to thread that packet
as a separate theorem argument.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    ∃ k TD, Drazin.IsDrazinInverse T TD k :=
  exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    (hR := constructiveRieszDecompositionAtZero_of_drazinInfiniteAssumptions
      (𝕂 := 𝕂) h)

/--
Classical Riesz decomposition immediately yields the canonical Drazin witness.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_hasClassicalRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/--
Classical Riesz decomposition interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_rieszDecomposition
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, Drazin.IsDrazinInverse T TD k :=
  exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    (hR := constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero h)

end SpectralInterfaces

section RieszData

variable {R : Type*} [Ring R]

/--
Riesz-style Drazin package on an operator ring.

The load-bearing field remains the canonical algebraic witness.
-/
@[rep_depth operator]
structure RieszDrazinData (T : R) where
  k : ℕ
  D : R
  P : R
  hIsDrazin : Drazin.IsDrazinInverse T D k
  hP : P = Drazin.IsDrazinInverse.projection T D

variable {T : R}

/-- Extract canonical Drazin witness from a Riesz package. -/
@[rep_depth operator]
theorem isDrazinInverse_of_riesz
    (h : RieszDrazinData T) :
    Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/-- The regular projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem projector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    h.P * h.P = h.P := by
  rw [h.hP]
  exact Drazin.IsDrazinInverse.projection_is_idempotent h.hIsDrazin

/-- Complementary projector attached to a Riesz package. -/
@[rep_depth operator]
def complementaryProjector (h : RieszDrazinData T) : R :=
  Drazin.IsDrazinInverse.complementaryProjection T h.D

/-- Complementary projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem complementaryProjector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * complementaryProjector h = complementaryProjector h := by
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.complementaryProjection_is_idempotent h.hIsDrazin

/-- Regular/complementary projectors are left-orthogonal. -/
@[rep_depth operator]
theorem projector_mul_complementaryProjector_of_riesz
    (h : RieszDrazinData T) :
    h.P * complementaryProjector h = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.projection_mul_complementaryProjection h.hIsDrazin

/-- Regular/complementary projectors are right-orthogonal. -/
@[rep_depth operator]
theorem complementaryProjector_mul_projector_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * h.P = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.complementaryProjection_mul_projection h.hIsDrazin

end RieszData

section FiniteDimensionalBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
Finite-dimensional continuous-operator bridge into the Riesz-style package.
The finite-dimensional Drazin existence theorem supplies the package
existentially; this file does not choose a canonical inverse or index.
-/
@[rep_depth operator]
theorem exists_rieszDrazinData_endCLM (T : E →L[ℝ] E) :
    ∃ h : RieszDrazinData T, Drazin.IsDrazinInverse T h.D h.k := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) T with ⟨k, D, hD⟩
  let hpack : RieszDrazinData T :=
    { k := k
      D := D
      P := Drazin.IsDrazinInverse.projection T D
      hIsDrazin := hD
      hP := rfl }
  refine ⟨hpack, ?_⟩
  simpa [hpack] using hD

end FiniteDimensionalBridge

end InfoGeometry.Canonical.DrazinInfiniteCore

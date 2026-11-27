/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Clifford.LipschitzVectorAction
import InfoGeometry.Clifford.RealQuadraticReflectionCartanDieudonne
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Primary-Source Clifford, Lipschitz, Witt, and Riesz Foundations (`S2-11`..`S2-14`)

This module formalizes the foundational definitions, theorems, and structural contrasts from
the first half of Pillar 2 (`R3`), preserving basis-free `O(Q)` invariance (`R3.2`) and
Koszul `ℤ/2`-graded tensor products (`R3.3`):

* **`S2-11` — Clifford (1873, 1876 Paper XLIII, 1878)**:
  * Even/odd grade-involution decomposition `⅟2 • (x ± involute x)` and uniqueness via
    `CliffordAlgebra.evenOdd_isCompl`.
  * Coordinate-free `𝒜_n` orthogonal generator relations (`ι_sq_scalar`,
    `ι_mul_ι_comm_of_isOrtho`), basis-free 3D biquaternion witness (`ω² = +1` for
    `ι_r² = -1` as in Clifford 1878 *AJM* 1 p. 352 and Clifford 1873 §IV pp. 195–196;
    `ω² = -1` for `ι_r² = +1` as in Clifford 1876 Paper XLIII / Riesz §1.6), elliptic
    complexification `CliffordAlgebra.equivBaseChange ℂ`, and non-semisimple dual-quaternion
    nilpotent witness `CliffordAlgebraDualNumber.equiv` (`ω² = 0`, Clifford 1873 §II p. 186).
  * Basis-free realization of `Cl(e₀⊥, -Q(e₀)Q|_{e₀⊥}) →ₐ[R] CliffordAlgebra.even Q`
    (Clifford 1878 pp. 352–354).

* **`S2-12` — Lipschitz (1880, 1886)**:
  * Basis-free Lipschitz group homomorphism `lipschitzGroupToIsometryHom : lipschitzGroup Q →*
    Q.IsometryEquiv Q` (`R3.2`, no matrix coordinates), reflection action on `ι Q a`,
    multiplicative spinor norm `lipschitzSpinorNormHom : lipschitzGroup Q →* Rˣ`
    (`reverse g * g`), `pinGroupToIsometryHom`, compatibility with
    `CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.spinGroupToIsometryHom`, and `-1`
    double-cover kernel witness.
  * Explicit equivalence of `involute g * v * g⁻¹` and `g * v * (involute g)⁻¹` on all
    homogeneous Lipschitz units, and an explicit `dim ≥ 4` non-regular grade-4 obstruction
    (`1 + e₁ e₂ e₃ e₄` in `Cl(0,4)` failing `reverse x * x ∈ range (algebraMap ℝ _)`,
    Lipschitz 1886 Ch. II Art. 5 eq. (14) p. 84).

* **`S2-13` — Witt (1937)**:
  * Coordinate-free quadratic-space theory over `[Field K] [Invertible (2 : K)]` (Witt 1937
    §I p. 32 *die Charakteristik sei ≠ 2*): `hyperbolicPlaneQuad`, `IsHyperbolicPlane`,
    hyperbolic pair construction `exists_hyperbolic_pair_of_isotropic` (Hilfssatz p. 34),
    orthogonal/hyperbolic Witt decomposition `witt_orthogonal_hyperbolic_decomposition`
    (`V ≃_q V_aniso ⊥ ℍ^m`, Satz 5 p. 35), field-generic reflection alignment,
    Witt cancellation `witt_cancellation` (Satz 4 p. 34), nondegenerate-subspace Witt
    extension `witt_extension_nondegenerate` (Anmerkung p. 34), and graded tensor product
    compatibility `witt_clifford_graded_tensor_law` (properly attributing
    `C(q₁ ⊥ q₂) ≅ C(q₁) ⊗̂ C(q₂)` to Witt §II / Atiyah–Bott–Shapiro 1964 §1 Prop. (1.6)).

* **`S2-14` — Riesz (1946/1958)**:
  * Grade resolution (`CliffordAlgebra.equivExterior`, `cliffordGradeProj`), general-`k`
    `exteriorPower_reverse`, `cliffordGradeProj_reverse` (`(-1)^(k*(k-1)/2)`), and
    `cliffordGradeProj_star` (`(-1)^(k*(k+1)/2)`), distinguishing Riesz §1.4's `ū` reversion
    from ABS §1 Def. (1.8)'s `x̄` Clifford conjugation (`star`).
  * Klein-4 involution algebra (`involute`, `reverse`, `star`) commuting with
    `equivOfIsometry`.
  * Odd-dimension central idempotents `(1 ± P)/2` (Riesz 1958 Ch. I §1.5 pp. 16–18), and
    minimal left ideal spinor realizations (`RieszLeftIdeal`, `IsMinimalLeftIdeal`, tracing
    Riesz 1958 Preface / 1993 Ch. VI & Sushch 2015 eqs. (21)–(24)) witnessing split `Cl(1,1)`
    (`Cl(1,1) · f` of dimension 2) versus division-ring `Cl(0,2) ≃ₐ ℍ`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.LipschitzWittRieszPrimary

open CliffordAlgebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Clifford.LipschitzVectorAction
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

/-!
## Section 1 (`S2-11`): Clifford (1873, 1876 Paper XLIII, 1878) Biquaternions & Geometric Algebra
-/

section CliffordPrimary

section EvenOddSplit

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-- `S2-11` (Clifford 1876 Paper XLIII / 1878 §1): Coordinate-free even grade-involution
projector `⅟2 • (x + involute x)` onto `CliffordAlgebra.evenOdd Q 0` (`R3.2`). -/
def cliffordEvenPart (Q : QuadraticForm R M) :
    CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun x := (⅟(2 : R)) • (x + CliffordAlgebra.involute x)
  map_add' x y := by
    rw [map_add]
    simp only [smul_add]
    abel
  map_smul' r x := by
    simp only [RingHom.id_apply, map_smul]
    rw [← smul_add, smul_comm]

/-- `S2-11` (Clifford 1876 Paper XLIII / 1878 §1): Coordinate-free odd grade-involution
projector `⅟2 • (x - involute x)` onto `CliffordAlgebra.evenOdd Q 1` (`R3.2`). -/
def cliffordOddPart (Q : QuadraticForm R M) :
    CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun x := (⅟(2 : R)) • (x - CliffordAlgebra.involute x)
  map_add' x y := by
    rw [map_add]
    simp only [sub_eq_add_neg, neg_add, smul_add]
    abel
  map_smul' r x := by
    simp only [RingHom.id_apply, map_smul]
    rw [← smul_sub, smul_comm]

/-- `S2-11` (Clifford 1878 §1): `cliffordEvenPart Q x` lies in `evenOdd Q 0`,
`cliffordOddPart Q x` lies in `evenOdd Q 1`, and their sum is `x` (`R3.2`). -/
theorem clifford_evenOdd_canonical_decomposition (Q : QuadraticForm R M)
    (x : CliffordAlgebra Q) :
    cliffordEvenPart Q x ∈ CliffordAlgebra.evenOdd Q 0 ∧
      cliffordOddPart Q x ∈ CliffordAlgebra.evenOdd Q 1 ∧
      cliffordEvenPart Q x + cliffordOddPart Q x = x := by
  have heven : cliffordEvenPart Q x ∈ CliffordAlgebra.evenOdd Q 0 := by
    rw [← involute_eq_self_iff_mem_even]
    dsimp [cliffordEvenPart]
    rw [map_smul, map_add, CliffordAlgebra.involute_involute, add_comm]
  have hodd : cliffordOddPart Q x ∈ CliffordAlgebra.evenOdd Q 1 := by
    rw [← involute_eq_neg_self_iff_mem_odd]
    dsimp [cliffordOddPart]
    rw [map_smul, map_sub, CliffordAlgebra.involute_involute, ← smul_neg, neg_sub]
  have hsum : cliffordEvenPart Q x + cliffordOddPart Q x = x := by
    dsimp [cliffordEvenPart, cliffordOddPart]
    rw [← smul_add]
    have h2 : (x + CliffordAlgebra.involute x) + (x - CliffordAlgebra.involute x) =
        (2 : R) • x := by
      rw [two_smul]
      abel
    rw [h2, smul_smul, invOf_mul_self, one_smul]
  exact ⟨heven, hodd, hsum⟩

/-- `S2-11` (Clifford 1878 §1): Uniqueness of the `evenOdd` decomposition via
`CliffordAlgebra.evenOdd_isCompl` (`R3.2`). -/
theorem clifford_evenOdd_unique_decomposition (Q : QuadraticForm R M)
    {x e o : CliffordAlgebra Q}
    (he : e ∈ CliffordAlgebra.evenOdd Q 0)
    (ho : o ∈ CliffordAlgebra.evenOdd Q 1)
    (hsum : e + o = x) :
    e = cliffordEvenPart Q x ∧ o = cliffordOddPart Q x := by
  have hcomp := clifford_evenOdd_canonical_decomposition Q x
  have hdiff : e - cliffordEvenPart Q x = cliffordOddPart Q x - o := by
    have h0 : (e - cliffordEvenPart Q x) + (o - cliffordOddPart Q x) = 0 := by
      calc
        (e - cliffordEvenPart Q x) + (o - cliffordOddPart Q x)
            = (e + o) - (cliffordEvenPart Q x + cliffordOddPart Q x) := by abel
        _ = x - x := by rw [hsum, hcomp.2.2]
        _ = 0 := sub_self x
    calc
      e - cliffordEvenPart Q x = -(o - cliffordOddPart Q x) := eq_neg_of_add_eq_zero_left h0
      _ = cliffordOddPart Q x - o := by abel
  have hmem0 : e - cliffordEvenPart Q x ∈ CliffordAlgebra.evenOdd Q 0 :=
    Submodule.sub_mem _ he hcomp.1
  have hmem1 : e - cliffordEvenPart Q x ∈ CliffordAlgebra.evenOdd Q 1 := by
    rw [hdiff]
    exact Submodule.sub_mem _ hcomp.2.1 ho
  have hbot : e - cliffordEvenPart Q x ∈ (⊥ : Submodule R (CliffordAlgebra Q)) := by
    rw [← (CliffordAlgebra.evenOdd_isCompl Q).disjoint.eq_bot]
    exact Submodule.mem_inf.mpr ⟨hmem0, hmem1⟩
  rw [Submodule.mem_bot] at hbot
  have he_eq : e = cliffordEvenPart Q x := sub_eq_zero.mp hbot
  have ho_eq : o = cliffordOddPart Q x := by
    rw [hbot] at hdiff
    exact (sub_eq_zero.mp hdiff.symm).symm
  exact ⟨he_eq, ho_eq⟩

end EvenOddSplit

section GeneratorsAndBiquaternions

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `S2-11` (Clifford 1876 Paper XLIII p. 398; 1878 *AJM* 1 p. 352): Coordinate-free
`𝒜_n` generator relations `ι(eᵢ)² = Q(eᵢ)` and `ι(eᵢ)ι(eⱼ) = -ι(eⱼ)ι(eᵢ)` for pairwise
orthogonal vectors (`R3.2`). -/
theorem clifford1878_ortho_generator_laws (Q : QuadraticForm R M) {ιIdx : Type*}
    (e : ιIdx → M) (hortho : ∀ i j, i ≠ j → Q.IsOrtho (e i) (e j)) :
    (∀ i, CliffordAlgebra.ι Q (e i) * CliffordAlgebra.ι Q (e i) =
      algebraMap R (CliffordAlgebra Q) (Q (e i))) ∧
      (∀ i j, i ≠ j →
        CliffordAlgebra.ι Q (e i) * CliffordAlgebra.ι Q (e j) =
          -(CliffordAlgebra.ι Q (e j) * CliffordAlgebra.ι Q (e i))) := by
  refine ⟨fun i => CliffordAlgebra.ι_sq_scalar Q (e i), fun i j hij => ?_⟩
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (hortho i j hij)

/-- `S2-11` (Clifford 1873 §IV pp. 195–196; 1876 Paper XLIII p. 398; 1878 *AJM* 1 p. 354):
Basis-free 3D biquaternion relations inside any `CliffordAlgebra Q` containing three
pairwise orthogonal vectors `e₁, e₂, e₃` with equal norm `Q eᵢ = c`:
* `i := ι e₂ * ι e₃`, `j := ι e₃ * ι e₁`, `k := ι e₁ * ι e₂` lie in `CliffordAlgebra.even Q`
  with `i² = j² = k² = -(c²) • 1` (hence `-1` for both `c = +1` and `c = -1`).
* For `c = -1` (Clifford 1878 *AJM* 1 p. 352 `ι_r² = -1`), `i * j = k` and the central
  pseudoscalar `ω := ι e₁ * ι e₂ * ι e₃` satisfies `ω² = +1` (elliptic/split biquaternion).
* For `c = +1` (Clifford 1876 Paper XLIII p. 398 `ι_r² = +1` / Riesz §1.6), `ω² = -1`
  (complex biquaternion).
Notice `ω` is central in the subalgebra generated by `e₁, e₂, e₃` (`ω * ι eᵣ = ι eᵣ * ω`,
hence `ω` commutes with `i, j, k`), and `ω ∈ evenOdd Q 1` (`R3.2`). -/
theorem clifford1873_pseudoscalar_biquaternion_relations (Q : QuadraticForm R M)
    (e₁ e₂ e₃ : M) (c : R)
    (h12 : Q.IsOrtho e₁ e₂) (h13 : Q.IsOrtho e₁ e₃) (h23 : Q.IsOrtho e₂ e₃)
    (hq1 : Q e₁ = c) (hq2 : Q e₂ = c) (hq3 : Q e₃ = c) :
    let v₁ := CliffordAlgebra.ι Q e₁
    let v₂ := CliffordAlgebra.ι Q e₂
    let v₃ := CliffordAlgebra.ι Q e₃
    let i := v₂ * v₃
    let j := v₃ * v₁
    let k := v₁ * v₂
    let ω := v₁ * v₂ * v₃
    (i ∈ CliffordAlgebra.even Q ∧ j ∈ CliffordAlgebra.even Q ∧ k ∈ CliffordAlgebra.even Q) ∧
      (ω ∈ CliffordAlgebra.evenOdd Q 1) ∧
      (i * i = (-(c * c)) • (1 : CliffordAlgebra Q) ∧
        j * j = (-(c * c)) • (1 : CliffordAlgebra Q) ∧
        k * k = (-(c * c)) • (1 : CliffordAlgebra Q)) ∧
      (ω * i = i * ω ∧ ω * j = j * ω ∧ ω * k = k * ω) ∧
      (ω * ω = (-(c * c * c)) • (1 : CliffordAlgebra Q)) ∧
      (i * j = (-c) • k) := by
  intro v₁ v₂ v₃ i j k ω
  have hv1sq : v₁ * v₁ = c • (1 : CliffordAlgebra Q) := by
    rw [show v₁ = CliffordAlgebra.ι Q e₁ from rfl, CliffordAlgebra.ι_sq_scalar, hq1,
      Algebra.algebraMap_eq_smul_one]
  have hv2sq : v₂ * v₂ = c • (1 : CliffordAlgebra Q) := by
    rw [show v₂ = CliffordAlgebra.ι Q e₂ from rfl, CliffordAlgebra.ι_sq_scalar, hq2,
      Algebra.algebraMap_eq_smul_one]
  have hv3sq : v₃ * v₃ = c • (1 : CliffordAlgebra Q) := by
    rw [show v₃ = CliffordAlgebra.ι Q e₃ from rfl, CliffordAlgebra.ι_sq_scalar, hq3,
      Algebra.algebraMap_eq_smul_one]
  have h12c : v₁ * v₂ = -(v₂ * v₁) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h12
  have h21c : v₂ * v₁ = -(v₁ * v₂) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h12.symm
  have h13c : v₁ * v₃ = -(v₃ * v₁) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h13
  have h31c : v₃ * v₁ = -(v₁ * v₃) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h13.symm
  have h23c : v₂ * v₃ = -(v₃ * v₂) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h23
  have h32c : v₃ * v₂ = -(v₂ * v₃) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h23.symm
  have heven : i ∈ CliffordAlgebra.even Q ∧ j ∈ CliffordAlgebra.even Q ∧
      k ∈ CliffordAlgebra.even Q := by
    refine ⟨?_, ?_, ?_⟩
    · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q e₂ e₃
    · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q e₃ e₁
    · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q e₁ e₂
  have hω_odd : ω ∈ CliffordAlgebra.evenOdd Q 1 := by
    have h12m : v₁ * v₂ ∈ CliffordAlgebra.evenOdd Q 0 :=
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q e₁ e₂
    have h3m : v₃ ∈ CliffordAlgebra.evenOdd Q 1 := CliffordAlgebra.ι_mem_evenOdd_one Q e₃
    have hmul := CliffordAlgebra.evenOdd_mul_le Q 0 1 (Submodule.mul_mem_mul h12m h3m)
    simpa [ω, zero_add] using hmul
  have hisq : i * i = (-(c * c)) • (1 : CliffordAlgebra Q) := by
    have hsm : (c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) =
        (c * c) • (1 : CliffordAlgebra Q) := by
      rw [smul_mul_smul_comm, _root_.mul_one]
    calc
      (v₂ * v₃) * (v₂ * v₃) = v₂ * (v₃ * v₂) * v₃ := by noncomm_ring
      _ = v₂ * (-(v₂ * v₃)) * v₃ := by rw [h32c]
      _ = -((v₂ * v₂) * (v₃ * v₃)) := by noncomm_ring
      _ = -((c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q))) := by
          rw [hv2sq, hv3sq]
      _ = (-(c * c)) • (1 : CliffordAlgebra Q) := by rw [hsm, neg_smul]
  have hjsq : j * j = (-(c * c)) • (1 : CliffordAlgebra Q) := by
    have hsm : (c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) =
        (c * c) • (1 : CliffordAlgebra Q) := by
      rw [smul_mul_smul_comm, _root_.mul_one]
    calc
      (v₃ * v₁) * (v₃ * v₁) = v₃ * (v₁ * v₃) * v₁ := by noncomm_ring
      _ = v₃ * (-(v₃ * v₁)) * v₁ := by rw [h13c]
      _ = -((v₃ * v₃) * (v₁ * v₁)) := by noncomm_ring
      _ = -((c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q))) := by
          rw [hv3sq, hv1sq]
      _ = (-(c * c)) • (1 : CliffordAlgebra Q) := by rw [hsm, neg_smul]
  have hksq : k * k = (-(c * c)) • (1 : CliffordAlgebra Q) := by
    have hsm : (c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) =
        (c * c) • (1 : CliffordAlgebra Q) := by
      rw [smul_mul_smul_comm, _root_.mul_one]
    calc
      (v₁ * v₂) * (v₁ * v₂) = v₁ * (v₂ * v₁) * v₂ := by noncomm_ring
      _ = v₁ * (-(v₁ * v₂)) * v₂ := by rw [h21c]
      _ = -((v₁ * v₁) * (v₂ * v₂)) := by noncomm_ring
      _ = -((c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q))) := by
          rw [hv1sq, hv2sq]
      _ = (-(c * c)) • (1 : CliffordAlgebra Q) := by rw [hsm, neg_smul]
  have hω1 : ω * v₁ = v₁ * ω := by
    calc
      (v₁ * v₂ * v₃) * v₁ = v₁ * v₂ * (v₃ * v₁) := by noncomm_ring
      _ = v₁ * v₂ * (-(v₁ * v₃)) := by rw [h31c]
      _ = -(v₁ * (v₂ * v₁) * v₃) := by noncomm_ring
      _ = -(v₁ * (-(v₁ * v₂)) * v₃) := by rw [h21c]
      _ = v₁ * (v₁ * v₂ * v₃) := by noncomm_ring
  have hω2 : ω * v₂ = v₂ * ω := by
    calc
      (v₁ * v₂ * v₃) * v₂ = v₁ * v₂ * (v₃ * v₂) := by noncomm_ring
      _ = v₁ * v₂ * (-(v₂ * v₃)) := by rw [h32c]
      _ = -((v₁ * v₂) * v₂ * v₃) := by noncomm_ring
      _ = -((-(v₂ * v₁)) * v₂ * v₃) := by rw [h12c]
      _ = v₂ * (v₁ * v₂ * v₃) := by noncomm_ring
  have hω3 : ω * v₃ = v₃ * ω := by
    calc
      (v₁ * v₂ * v₃) * v₃ = v₁ * (v₂ * v₃) * v₃ := by noncomm_ring
      _ = v₁ * (-(v₃ * v₂)) * v₃ := by rw [h23c]
      _ = -((v₁ * v₃) * v₂ * v₃) := by noncomm_ring
      _ = -((-(v₃ * v₁)) * v₂ * v₃) := by rw [h13c]
      _ = v₃ * (v₁ * v₂ * v₃) := by noncomm_ring
  have hωcomm : ω * i = i * ω ∧ ω * j = j * ω ∧ ω * k = k * ω := by
    refine ⟨?_, ?_, ?_⟩
    · calc
        ω * (v₂ * v₃) = (ω * v₂) * v₃ := by noncomm_ring
        _ = (v₂ * ω) * v₃ := by rw [hω2]
        _ = v₂ * (ω * v₃) := by noncomm_ring
        _ = v₂ * (v₃ * ω) := by rw [hω3]
        _ = (v₂ * v₃) * ω := by noncomm_ring
    · calc
        ω * (v₃ * v₁) = (ω * v₃) * v₁ := by noncomm_ring
        _ = (v₃ * ω) * v₁ := by rw [hω3]
        _ = v₃ * (ω * v₁) := by noncomm_ring
        _ = v₃ * (v₁ * ω) := by rw [hω1]
        _ = (v₃ * v₁) * ω := by noncomm_ring
    · calc
        ω * (v₁ * v₂) = (ω * v₁) * v₂ := by noncomm_ring
        _ = (v₁ * ω) * v₂ := by rw [hω1]
        _ = v₁ * (ω * v₂) := by noncomm_ring
        _ = v₁ * (v₂ * ω) := by rw [hω2]
        _ = (v₁ * v₂) * ω := by noncomm_ring
  have hωsq : ω * ω = (-(c * c * c)) • (1 : CliffordAlgebra Q) := by
    have hsm1 : (c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) =
        (c * c) • (1 : CliffordAlgebra Q) := by
      rw [smul_mul_smul_comm, _root_.mul_one]
    have hsm2 : ((c * c) • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) =
        (c * c * c) • (1 : CliffordAlgebra Q) := by
      rw [smul_mul_smul_comm, _root_.mul_one]
    calc
      (v₁ * v₂ * v₃) * (v₁ * v₂ * v₃)
          = v₁ * v₂ * (v₃ * v₁) * v₂ * v₃ := by noncomm_ring
      _ = v₁ * v₂ * (-(v₁ * v₃)) * v₂ * v₃ := by rw [h31c]
      _ = -(v₁ * (v₂ * v₁) * (v₃ * v₂) * v₃) := by noncomm_ring
      _ = -(v₁ * (-(v₁ * v₂)) * (-(v₂ * v₃)) * v₃) := by rw [h21c, h32c]
      _ = -((v₁ * v₁) * (v₂ * v₂) * (v₃ * v₃)) := by noncomm_ring
      _ = -((c • (1 : CliffordAlgebra Q)) * (c • (1 : CliffordAlgebra Q)) *
            (c • (1 : CliffordAlgebra Q))) := by
          rw [hv1sq, hv2sq, hv3sq]
      _ = -((c * c * c) • (1 : CliffordAlgebra Q)) := by rw [hsm1, hsm2]
      _ = (-(c * c * c)) • (1 : CliffordAlgebra Q) := (neg_smul _ _).symm
  have hij : i * j = (-c) • k := by
    have hsm : v₂ * (c • (1 : CliffordAlgebra Q)) = c • v₂ := by
      rw [mul_smul_comm, _root_.mul_one]
    calc
      (v₂ * v₃) * (v₃ * v₁) = v₂ * (v₃ * v₃) * v₁ := by noncomm_ring
      _ = v₂ * (c • (1 : CliffordAlgebra Q)) * v₁ := by rw [hv3sq]
      _ = (c • v₂) * v₁ := by rw [hsm]
      _ = c • (v₂ * v₁) := smul_mul_assoc c v₂ v₁
      _ = c • (-(v₁ * v₂)) := by rw [h21c]
      _ = (-c) • k := by rw [smul_neg, neg_smul]
  exact ⟨heven, hω_odd, ⟨hisq, hjsq, hksq⟩, hωcomm, hωsq, hij⟩

/-- `S2-11` (Clifford 1873 §II p. 186): Nilpotent generator law `ε² = 0` in the parabolic
dual-number Clifford algebra `Cl(R, 0)`. -/
theorem clifford1873_dual_parabolic_nilpotent (R_coeff : Type*) [CommRing R_coeff] (r : R_coeff) :
    CliffordAlgebra.ι (0 : QuadraticForm R_coeff R_coeff) r *
      CliffordAlgebra.ι (0 : QuadraticForm R_coeff R_coeff) r = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, zero_apply, map_zero]

/-- `S2-11` (Clifford 1878 *AJM* 1 pp. 352–354): For any vector `e₀ : M`, let
`S := LinearMap.BilinForm.orthogonal Q.polarBilin (R ∙ e₀)` be its orthogonal subspace. The
linear map `v ↦ ι Q v * ι Q e₀` lifts to an algebra homomorphism
`CliffordAlgebra ((-Q e₀) • Q.restrict S) →ₐ[R] CliffordAlgebra.even Q`, realizing
Clifford's isomorphism `Cl⁰(V, Q) ≅ Cl(e₀⊥, -Q(e₀) Q|_{e₀⊥})` basis-freely (`R3.2`). -/
def clifford1878_even_from_perp_hom (Q : QuadraticForm R M) (e₀ : M) :
    CliffordAlgebra
        ((-Q e₀) • Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin (R ∙ e₀))) →ₐ[R]
      CliffordAlgebra.even Q :=
  let S := LinearMap.BilinForm.orthogonal Q.polarBilin (R ∙ e₀)
  CliffordAlgebra.lift ((-Q e₀) • Q.restrict S)
    ⟨{  toFun := fun v =>
          ⟨CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀,
            CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q v.1 e₀⟩
        map_add' := fun u v => by
          apply Subtype.ext
          change CliffordAlgebra.ι Q (u.1 + v.1) * CliffordAlgebra.ι Q e₀ =
            CliffordAlgebra.ι Q u.1 * CliffordAlgebra.ι Q e₀ +
              CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀
          rw [map_add, add_mul]
        map_smul' := fun r u => by
          apply Subtype.ext
          change CliffordAlgebra.ι Q (r • u.1) * CliffordAlgebra.ι Q e₀ =
            r • (CliffordAlgebra.ι Q u.1 * CliffordAlgebra.ι Q e₀)
          rw [map_smul, smul_mul_assoc] },
      fun v => by
        apply Subtype.ext
        change (CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀) *
            (CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀) =
          algebraMap R (CliffordAlgebra Q) (((-Q e₀) • Q.restrict S) v)
        have hv_mem : Q.polarBilin e₀ v.1 = 0 :=
          v.2 e₀ (Submodule.mem_span_singleton_self e₀)
        have h_ortho : Q.IsOrtho v.1 e₀ := by
          have hpol : QuadraticMap.polar Q v.1 e₀ = 0 := by
            rw [QuadraticMap.polar_comm]
            exact hv_mem
          rw [QuadraticMap.isOrtho_def]
          change Q (v.1 + e₀) - Q v.1 - Q e₀ = 0 at hpol
          exact sub_eq_zero.mp (by rw [sub_add_eq_sub_sub, hpol])
        have hcomm : CliffordAlgebra.ι Q e₀ * CliffordAlgebra.ι Q v.1 =
            -(CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀) :=
          CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h_ortho.symm
        calc
          (CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀) *
              (CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀)
              = CliffordAlgebra.ι Q v.1 * (CliffordAlgebra.ι Q e₀ * CliffordAlgebra.ι Q v.1) *
                  CliffordAlgebra.ι Q e₀ := by noncomm_ring
          _ = CliffordAlgebra.ι Q v.1 * (-(CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q e₀)) *
                  CliffordAlgebra.ι Q e₀ := by rw [hcomm]
          _ = -((CliffordAlgebra.ι Q v.1 * CliffordAlgebra.ι Q v.1) *
                  (CliffordAlgebra.ι Q e₀ * CliffordAlgebra.ι Q e₀)) := by noncomm_ring
          _ = -(algebraMap R (CliffordAlgebra Q) (Q v.1) *
                  algebraMap R (CliffordAlgebra Q) (Q e₀)) := by
              rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar]
          _ = algebraMap R (CliffordAlgebra Q) (((-Q e₀) • Q.restrict S) v) := by
              rw [← map_mul, ← map_neg]
              congr 1
              change -(Q v.1 * Q e₀) = (-Q e₀) * Q v.1
              ring⟩

end GeneratorsAndBiquaternions

end CliffordPrimary

section EllipticBaseChange

open scoped TensorProduct

/-- `S2-11` (Clifford 1873 §IV pp. 195–196; Riesz §1.6 p. 21): Complexification of any
real Clifford algebra via `CliffordAlgebra.equivBaseChange ℂ Q` (`BaseChange.lean:183`),
realizing complex biquaternions `ℂ ⊗[ℝ] Cl(0,2)` (`ω² = -1` from `I² = -1`). -/
def clifford1873_elliptic_baseChange {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) :
    CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] ℂ ⊗[ℝ] CliffordAlgebra Q :=
  CliffordAlgebra.equivBaseChange ℂ Q

end EllipticBaseChange

/-- `S2-11` (Clifford 1878 *AJM* 1 p. 352; `R3.2`): Explicit non-commutativity witness
showing Clifford's polar multiplication `e₁ * e₂ ≠ e₂ * e₁` in `Cl(1,1)`. -/
theorem clifford1878_noncommutative_generator_witness :
    CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) ≠
      CliffordAlgebra.ι q11 (0, 1) * CliffordAlgebra.ι q11 (1, 0) := by
  intro h
  have hm := congrArg cl11EquivMat h
  rw [map_mul, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg] at hm
  have h01 := congrArg (fun M : Mat2 => M 0 1) hm
  simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- `S2-11` (Clifford 1878 *AJM* 1 p. 352): Explicit matrix-algebra non-commutativity witness
using `Eplus` and `Eminus` in `Mat2` (`Cl11Matrix`), complementing the basis-free
`clifford1878_noncommutative_generator_witness`. -/
theorem clifford1878_pauli_noncomm_witness : Eplus * Eminus ≠ Eminus * Eplus := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-!
## Section 2 (`S2-12`): Lipschitz (1880, 1886) Group, Spinor Norm, & `O(Q)` Double Cover
-/

section LipschitzPrimary

section LipschitzIsometryAndNorm

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

private theorem hTrace_cl_algebraMap_local (Q : QuadraticForm R M) (r : R) :
    InfoGeometry.Riemannian.hTrace_cl Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  change ExteriorAlgebra.algebraMapInv
      (CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) r)) = r
  rw [equivExterior_algebraMap]
  exact AlgHom.commutes
    (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R) r

private theorem clifford_algebraMap_injective (Q : QuadraticForm R M) :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r₁ r₂ h
  have ht := congrArg (InfoGeometry.Riemannian.hTrace_cl Q) h
  rwa [hTrace_cl_algebraMap_local, hTrace_cl_algebraMap_local] at ht

/-- `S2-12` (Lipschitz 1880 *C. R.* 91 p. 662; 1886 Ch. II Art. 3–5): The twisted
conjugation action of Mathlib's `_root_.lipschitzGroup Q` preserves the quadratic form `Q`
basis-freely without coordinate matrices (`R3.2`). -/
theorem lipschitzGroup_twisted_preserves_Q (Q : QuadraticForm R M)
    (g : _root_.lipschitzGroup Q) (v : M) :
    Q (twistedActionHom Q (clifford_ι_injective Q) g v) = Q v := by
  exact twistedVectorMap_preserves_quadraticForm Q (clifford_ι_injective Q)
    (clifford_algebraMap_injective Q) g v

/-- `S2-12` (Lipschitz 1880, 1886 Ch. II Art. 3–5; ABS Def. (3.1)): Basis-free group
homomorphism `_root_.lipschitzGroup Q →* Q.IsometryEquiv Q` sending `g` to the twisted
conjugation isometry `v ↦ ι⁻¹(involute g * ι v * g⁻¹)` (`R3.2`). -/
def lipschitzGroupToIsometryHom (Q : QuadraticForm R M) :
    _root_.lipschitzGroup Q →* Q.IsometryEquiv Q where
  toFun g :=
    { toLinearEquiv := twistedActionHom Q (clifford_ι_injective Q) g
      map_app' := lipschitzGroup_twisted_preserves_Q Q g }
  map_one' := by
    apply DFunLike.ext
    intro v
    change twistedActionHom Q (clifford_ι_injective Q) 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply DFunLike.ext
    intro v
    change twistedActionHom Q (clifford_ι_injective Q) (g * h) v =
      twistedActionHom Q (clifford_ι_injective Q) g
        (twistedActionHom Q (clifford_ι_injective Q) h v)
    rw [map_mul]
    rfl

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 3–5): Characterization of `lipschitzGroupToIsometryHom`
inside `CliffordAlgebra Q` via twisted conjugation (`R3.2`). -/
@[simp] theorem ι_lipschitzGroupToIsometryHom (Q : QuadraticForm R M)
    (g : _root_.lipschitzGroup Q) (v : M) :
    CliffordAlgebra.ι Q (lipschitzGroupToIsometryHom Q g v) =
      CliffordAlgebra.involute (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
        (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
  change CliffordAlgebra.ι Q (twistedVectorMap Q (clifford_ι_injective Q) g v) = _
  exact ι_twistedVectorMap Q (clifford_ι_injective Q) g v

/-- `S2-12` (Lipschitz 1886 Ch. II; Riesz Ch. II §2.3): An invertible vector generator
`ι Q a` (`Invertible (Q a)`) in `_root_.lipschitzGroup Q` acts via `lipschitzGroupToIsometryHom`
as the orthogonal hyperplane reflection `v ↦ v - (⅟(Q a) * polar Q a v) • a`, sending
`a ↦ -a` and fixing every vector orthogonal to `a` (`R3.2`). -/
theorem lipschitzGroupToIsometryHom_ι_eq_reflection (Q : QuadraticForm R M)
    (a : M) [Invertible (Q a)] :
    let u : (CliffordAlgebra Q)ˣ :=
      ⟨CliffordAlgebra.ι Q a, CliffordAlgebra.ι Q (⅟(Q a) • a),
        by
          rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
        by
          rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
    let g : _root_.lipschitzGroup Q := ⟨u, Subgroup.subset_closure ⟨a, rfl⟩⟩
    (∀ v : M, lipschitzGroupToIsometryHom Q g v =
      v - (⅟(Q a) * QuadraticMap.polar Q a v) • a) ∧
    (lipschitzGroupToIsometryHom Q g a = -a) ∧
    (∀ v : M, Q.IsOrtho a v → lipschitzGroupToIsometryHom Q g v = v) := by
  intro u g
  have hact : ∀ v : M, lipschitzGroupToIsometryHom Q g v =
      v - (⅟(Q a) * QuadraticMap.polar Q a v) • a := by
    intro v
    apply clifford_ι_injective Q
    rw [ι_lipschitzGroupToIsometryHom]
    have hgu : (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = CliffordAlgebra.ι Q a := rfl
    have hgi : (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
        CliffordAlgebra.ι Q (⅟(Q a) • a) := rfl
    rw [hgu, hgi, CliffordAlgebra.involute_ι, neg_mul]
    have hswap : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v =
        algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a v) -
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a :=
      eq_sub_of_add_eq (CliffordAlgebra.ι_mul_ι_add_swap a v)
    calc
      -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v) * CliffordAlgebra.ι Q (⅟(Q a) • a)
          = -(algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a v) -
              CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a) *
              CliffordAlgebra.ι Q (⅟(Q a) • a) := by rw [hswap]
      _ = CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q (⅟(Q a) • a)) -
            algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a v) *
              CliffordAlgebra.ι Q (⅟(Q a) • a) := by noncomm_ring
      _ = CliffordAlgebra.ι Q v * 1 -
            algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a v) *
              (⅟(Q a) • CliffordAlgebra.ι Q a) := by
          rw [show CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q (⅟(Q a) • a) = 1 from u.val_inv,
            map_smul]
      _ = CliffordAlgebra.ι Q v -
            (⅟(Q a) * QuadraticMap.polar Q a v) • CliffordAlgebra.ι Q a := by
          rw [_root_.mul_one, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
            _root_.one_mul, smul_smul]
      _ = CliffordAlgebra.ι Q (v - (⅟(Q a) * QuadraticMap.polar Q a v) • a) := by
          rw [map_sub, map_smul]
  refine ⟨hact, ?_, ?_⟩
  · rw [hact a, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat, mul_left_comm,
      invOf_mul_self, _root_.mul_one, two_smul R a]
    abel
  · intro v hv
    rw [QuadraticMap.isOrtho_def] at hv
    have hpol : QuadraticMap.polar Q a v = 0 := by
      change Q (a + v) - Q a - Q v = 0
      rw [hv]
      ring
    rw [hact v, hpol, mul_zero, zero_smul, sub_zero]

omit [Invertible (2 : R)] in
/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5 eq. (10), p. 82): On any homogeneous element `g`
satisfying `involute g = ±g` (in particular every `g ∈ _root_.lipschitzGroup Q`),
`involute g * ι Q v * g⁻¹` equals `g * ι Q v * (Units.map involute.toMonoidHom g)⁻¹`,
documenting why Mathlib/ABS's `α(g) v g⁻¹` and Lipschitz's `g v α(g)⁻¹` coincide on
the Lipschitz group. -/
theorem lipschitz_homogeneous_involute_conjugation_equiv (Q : QuadraticForm R M)
    (g : _root_.lipschitzGroup Q) (v : M) :
    CliffordAlgebra.involute (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v * (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
      (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑((Units.map (CliffordAlgebra.involute (Q := Q)).toMonoidHom
          (g : (CliffordAlgebra Q)ˣ))⁻¹) : CliffordAlgebra Q) := by
  have hinv_coe :
      (↑((Units.map (CliffordAlgebra.involute (Q := Q)).toMonoidHom
        (g : (CliffordAlgebra Q)ˣ))⁻¹) : CliffordAlgebra Q) =
        CliffordAlgebra.involute (Q := Q) (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
    exact Units.coe_map_inv (CliffordAlgebra.involute (Q := Q)).toMonoidHom _
  rw [hinv_coe]
  rcases lipschitz_involute_eq_self_or_neg Q g.property with hpos | hneg
  · have hginv : CliffordAlgebra.involute (Q := Q)
        (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
        (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
      have h1 : (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          CliffordAlgebra.involute (Q := Q)
            (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) = 1 := by
        calc
          _ = CliffordAlgebra.involute (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
                CliffordAlgebra.involute (Q := Q)
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by rw [hpos]
          _ = CliffordAlgebra.involute (Q := Q)
                ((↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := (map_mul _ _ _).symm
          _ = 1 := by simp
      calc
        CliffordAlgebra.involute (Q := Q) (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)
            = (1 : CliffordAlgebra Q) *
                CliffordAlgebra.involute (Q := Q)
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := (_root_.one_mul _).symm
        _ = ((↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) *
                (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
                CliffordAlgebra.involute (Q := Q)
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
              rw [Units.inv_mul]
        _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) *
                ((↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
                  CliffordAlgebra.involute (Q := Q)
                    (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := _root_.mul_assoc _ _ _
        _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) * 1 := by rw [h1]
        _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := _root_.mul_one _
    rw [hpos, hginv]
  · have hginv : CliffordAlgebra.involute (Q := Q)
        (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
        -(↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
      have h1 : (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          (-CliffordAlgebra.involute (Q := Q)
            (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) = 1 := by
        calc
          _ = (-CliffordAlgebra.involute (Q := Q)
                (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
                (-CliffordAlgebra.involute (Q := Q)
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := by rw [hneg, neg_neg]
          _ = CliffordAlgebra.involute (Q := Q)
                ((↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
                  (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := by
                rw [neg_mul_neg, map_mul]
          _ = 1 := by simp
      have hneg' : -CliffordAlgebra.involute (Q := Q)
          (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
          (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := by
        calc
          -CliffordAlgebra.involute (Q := Q)
              (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)
              = (1 : CliffordAlgebra Q) *
                  (-CliffordAlgebra.involute (Q := Q)
                    (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := (_root_.one_mul _).symm
          _ = ((↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) *
                  (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
                  (-CliffordAlgebra.involute (Q := Q)
                    (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) := by
                rw [Units.inv_mul]
          _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) *
                  ((↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
                    (-CliffordAlgebra.involute (Q := Q)
                      (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q))) := _root_.mul_assoc _ _ _
          _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) * 1 := by rw [h1]
          _ = (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) := _root_.mul_one _
      rw [← neg_neg (CliffordAlgebra.involute (Q := Q)
        (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)), hneg']
    rw [hneg, hginv]
    noncomm_ring

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5 eqs. (21)–(25), pp. 84–86): For every element
`g ∈ _root_.lipschitzGroup Q`, `reverse g * g` lies in the scalar subring
`range (algebraMap R (CliffordAlgebra Q))` (defining the scalar spinor norm). -/
theorem lipschitzGroup_reverse_mul_self_mem_range (Q : QuadraticForm R M)
    (g : _root_.lipschitzGroup Q) :
    CliffordAlgebra.reverse (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (algebraMap R (CliffordAlgebra Q)).range := by
  have hg := g.property
  generalize (g : (CliffordAlgebra Q)ˣ) = u at hg ⊢
  unfold _root_.lipschitzGroup at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    rw [← ha, CliffordAlgebra.reverse_ι, CliffordAlgebra.ι_sq_scalar]
    exact ⟨Q a, rfl⟩
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let _ : Invertible (x : CliffordAlgebra Q) := x.invertible
    let _ : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
    let _ : Invertible (Q a) := CliffordAlgebra.invertibleOfInvertibleι Q a
    have hinv : (↑(x⁻¹) : CliffordAlgebra Q) = CliffordAlgebra.ι Q (⅟(Q a) • a) := by
      calc
        (↑(x⁻¹) : CliffordAlgebra Q)
            = (↑(x⁻¹) : CliffordAlgebra Q) * 1 := (_root_.mul_one _).symm
        _ = (↑(x⁻¹) : CliffordAlgebra Q) *
              (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q (⅟(Q a) • a)) := by
            rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
              Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]
        _ = ((↑(x⁻¹) : CliffordAlgebra Q) * (x : CliffordAlgebra Q)) *
              CliffordAlgebra.ι Q (⅟(Q a) • a) := by
            rw [← ha, ← _root_.mul_assoc]
        _ = CliffordAlgebra.ι Q (⅟(Q a) • a) := by rw [Units.inv_mul, _root_.one_mul]
    rw [hinv, CliffordAlgebra.reverse_ι, CliffordAlgebra.ι_sq_scalar]
    exact ⟨Q (⅟(Q a) • a), rfl⟩
  | one =>
    rw [Units.val_one, CliffordAlgebra.reverse.map_one,
      show (1 : CliffordAlgebra Q) * 1 = 1 from _root_.mul_one _]
    exact ⟨1, map_one _⟩
  | mul y z _ _ hy hz =>
    rcases hy with ⟨ry, hry⟩
    rcases hz with ⟨rz, hrz⟩
    rw [Units.val_mul, CliffordAlgebra.reverse.map_mul]
    have hcalc : CliffordAlgebra.reverse (Q := Q) (z : CliffordAlgebra Q) *
          CliffordAlgebra.reverse (Q := Q) (y : CliffordAlgebra Q) *
          ((y : CliffordAlgebra Q) * (z : CliffordAlgebra Q)) =
        algebraMap R (CliffordAlgebra Q) (ry * rz) := by
      calc
        CliffordAlgebra.reverse (Q := Q) (z : CliffordAlgebra Q) *
            CliffordAlgebra.reverse (Q := Q) (y : CliffordAlgebra Q) *
            ((y : CliffordAlgebra Q) * (z : CliffordAlgebra Q))
            = CliffordAlgebra.reverse (Q := Q) (z : CliffordAlgebra Q) *
                (CliffordAlgebra.reverse (Q := Q) (y : CliffordAlgebra Q) * (y : CliffordAlgebra Q)) *
                (z : CliffordAlgebra Q) := by noncomm_ring
        _ = CliffordAlgebra.reverse (Q := Q) (z : CliffordAlgebra Q) *
                algebraMap R (CliffordAlgebra Q) ry * (z : CliffordAlgebra Q) := by rw [← hry]
        _ = algebraMap R (CliffordAlgebra Q) ry *
                (CliffordAlgebra.reverse (Q := Q) (z : CliffordAlgebra Q) *
                  (z : CliffordAlgebra Q)) := by
              rw [← Algebra.commutes ry _]
              noncomm_ring
        _ = algebraMap R (CliffordAlgebra Q) ry * algebraMap R (CliffordAlgebra Q) rz := by
              rw [← hrz]
        _ = algebraMap R (CliffordAlgebra Q) (ry * rz) := (map_mul _ _ _).symm
    exact ⟨ry * rz, hcalc.symm⟩

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5, pp. 84–86): Scalar value of the spinor norm
`N(g) = hTrace_cl Q (reverse g * g)` on `_root_.lipschitzGroup Q`. -/
def lipschitzSpinorNormVal (Q : QuadraticForm R M) (g : _root_.lipschitzGroup Q) : R :=
  InfoGeometry.Riemannian.hTrace_cl Q
    (CliffordAlgebra.reverse (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5): `lipschitzSpinorNormVal` lifts back via
`algebraMap` to `reverse g * g`. -/
theorem algebraMap_lipschitzSpinorNormVal (Q : QuadraticForm R M)
    (g : _root_.lipschitzGroup Q) :
    algebraMap R (CliffordAlgebra Q) (lipschitzSpinorNormVal Q g) =
      CliffordAlgebra.reverse (Q := Q) (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rcases lipschitzGroup_reverse_mul_self_mem_range Q g with ⟨r, hr⟩
  dsimp [lipschitzSpinorNormVal]
  rw [← hr, hTrace_cl_algebraMap_local]

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5): Spinor norm of the identity is `1`. -/
theorem lipschitzSpinorNormVal_one (Q : QuadraticForm R M) :
    lipschitzSpinorNormVal Q 1 = 1 := by
  apply clifford_algebraMap_injective Q
  rw [algebraMap_lipschitzSpinorNormVal, map_one]
  simp

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5): Multiplicativity of `lipschitzSpinorNormVal`
on `_root_.lipschitzGroup Q`. -/
theorem lipschitzSpinorNormVal_mul (Q : QuadraticForm R M)
    (g h : _root_.lipschitzGroup Q) :
    lipschitzSpinorNormVal Q (g * h) =
      lipschitzSpinorNormVal Q g * lipschitzSpinorNormVal Q h := by
  apply clifford_algebraMap_injective Q
  rw [map_mul, algebraMap_lipschitzSpinorNormVal, algebraMap_lipschitzSpinorNormVal,
    algebraMap_lipschitzSpinorNormVal]
  have hg := algebraMap_lipschitzSpinorNormVal Q g
  have hh := algebraMap_lipschitzSpinorNormVal Q h
  rw [Subgroup.coe_mul, Units.val_mul, CliffordAlgebra.reverse.map_mul]
  let cg : CliffordAlgebra Q := (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  let ch : CliffordAlgebra Q := (↑(h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  change CliffordAlgebra.reverse (Q := Q) ch * CliffordAlgebra.reverse (Q := Q) cg * (cg * ch) =
    (CliffordAlgebra.reverse (Q := Q) cg * cg) * (CliffordAlgebra.reverse (Q := Q) ch * ch)
  have hg' : algebraMap R (CliffordAlgebra Q) (lipschitzSpinorNormVal Q g) =
      CliffordAlgebra.reverse (Q := Q) cg * cg := hg
  calc
    CliffordAlgebra.reverse (Q := Q) ch * CliffordAlgebra.reverse (Q := Q) cg * (cg * ch)
        = CliffordAlgebra.reverse (Q := Q) ch *
            (CliffordAlgebra.reverse (Q := Q) cg * cg) * ch := by noncomm_ring
    _ = CliffordAlgebra.reverse (Q := Q) ch *
            algebraMap R (CliffordAlgebra Q) (lipschitzSpinorNormVal Q g) * ch := by rw [← hg']
    _ = algebraMap R (CliffordAlgebra Q) (lipschitzSpinorNormVal Q g) *
            (CliffordAlgebra.reverse (Q := Q) ch * ch) := by
          rw [← Algebra.commutes (lipschitzSpinorNormVal Q g) _]
          noncomm_ring
    _ = (CliffordAlgebra.reverse (Q := Q) cg * cg) *
            (CliffordAlgebra.reverse (Q := Q) ch * ch) := by
          rw [hg']

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5 eqs. (21)–(25), pp. 84–86): Multiplicative
spinor norm homomorphism `lipschitzSpinorNormHom Q : _root_.lipschitzGroup Q →* Rˣ`,
satisfying `algebraMap R _ (N g : R) = reverse g * g` (`R3.2`). -/
def lipschitzSpinorNormHom (Q : QuadraticForm R M) : _root_.lipschitzGroup Q →* Rˣ where
  toFun g :=
    { val := lipschitzSpinorNormVal Q g
      inv := lipschitzSpinorNormVal Q g⁻¹
      val_inv := by
        rw [← lipschitzSpinorNormVal_mul, mul_inv_cancel, lipschitzSpinorNormVal_one]
      inv_val := by
        rw [← lipschitzSpinorNormVal_mul, inv_mul_cancel, lipschitzSpinorNormVal_one] }
  map_one' := Units.ext (lipschitzSpinorNormVal_one Q)
  map_mul' g h := Units.ext (lipschitzSpinorNormVal_mul Q g h)

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5): On an invertible vector generator `ι Q a`,
the spinor norm evaluates to `Q a`. -/
theorem lipschitzSpinorNormHom_ι (Q : QuadraticForm R M) (a : M) [Invertible (Q a)] :
    let u : (CliffordAlgebra Q)ˣ :=
      ⟨CliffordAlgebra.ι Q a, CliffordAlgebra.ι Q (⅟(Q a) • a),
        by
          rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
        by
          rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
    (lipschitzSpinorNormHom Q ⟨u, Subgroup.subset_closure ⟨a, rfl⟩⟩ : R) = Q a := by
  intro u
  apply clifford_algebraMap_injective Q
  rw [show (lipschitzSpinorNormHom Q ⟨u, Subgroup.subset_closure ⟨a, rfl⟩⟩ : R) =
      lipschitzSpinorNormVal Q ⟨u, Subgroup.subset_closure ⟨a, rfl⟩⟩ from rfl,
    algebraMap_lipschitzSpinorNormVal]
  change CliffordAlgebra.reverse (CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q a = _
  rw [CliffordAlgebra.reverse_ι, CliffordAlgebra.ι_sq_scalar]

/-- `S2-12` (Lipschitz 1886; ABS Prop. (3.13)): On `_root_.spinGroup Q`, `reverse g * g = 1`,
so the Lipschitz spinor norm is identically `1`. -/
theorem spinGroup_reverse_mul_self_eq_one (Q : QuadraticForm R M) (g : _root_.spinGroup Q) :
    CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q) = 1 ∧
      lipschitzSpinorNormHom Q
        ⟨_root_.spinGroup.toUnits g, _root_.spinGroup.units_mem_lipschitzGroup g.2⟩ = 1 := by
  have hrev : CliffordAlgebra.reverse (g : CliffordAlgebra Q) = star (g : CliffordAlgebra Q) := by
    rw [CliffordAlgebra.star_def, _root_.spinGroup.involute_eq g.2]
  have hmul : CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q) = 1 := by
    rw [hrev]
    exact _root_.spinGroup.coe_star_mul_self g
  refine ⟨hmul, ?_⟩
  apply Units.ext
  apply clifford_algebraMap_injective Q
  change algebraMap R (CliffordAlgebra Q)
      (lipschitzSpinorNormVal Q ⟨_root_.spinGroup.toUnits g, _⟩) =
    algebraMap R (CliffordAlgebra Q) 1
  rw [algebraMap_lipschitzSpinorNormVal, map_one]
  exact hmul

/-- `S2-12` (ABS Thm. (3.11); Lipschitz 1886): Basis-free homomorphism from Mathlib's
`_root_.pinGroup Q` to `Q.IsometryEquiv Q` (`R3.2`). -/
def pinGroupToIsometryHom (Q : QuadraticForm R M) :
    _root_.pinGroup Q →* Q.IsometryEquiv Q where
  toFun g :=
    lipschitzGroupToIsometryHom Q
      ⟨_root_.pinGroup.toUnits g, _root_.pinGroup.units_mem_lipschitzGroup g.2⟩
  map_one' := by
    have h1 : (⟨_root_.pinGroup.toUnits (1 : _root_.pinGroup Q),
        _root_.pinGroup.units_mem_lipschitzGroup (1 : _root_.pinGroup Q).2⟩ :
        _root_.lipschitzGroup Q) = 1 := by
      apply Subtype.ext
      simp
    rw [h1, map_one]
  map_mul' g h := by
    have hm : (⟨_root_.pinGroup.toUnits (g * h),
        _root_.pinGroup.units_mem_lipschitzGroup (g * h).2⟩ : _root_.lipschitzGroup Q) =
      ⟨_root_.pinGroup.toUnits g, _root_.pinGroup.units_mem_lipschitzGroup g.2⟩ *
        ⟨_root_.pinGroup.toUnits h, _root_.pinGroup.units_mem_lipschitzGroup h.2⟩ := by
      apply Subtype.ext
      simp
    rw [hm, map_mul]

/-- `S2-12` (Compatibility): Restricting `pinGroupToIsometryHom` (and
`lipschitzGroupToIsometryHom`) to `_root_.spinGroup Q` agrees with
`CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.spinGroupToIsometryHom Q` (`R3.2`). -/
theorem spinGroup_to_lipschitz_eq_spinGroupToIsometryHom (Q : QuadraticForm R M)
    (g : _root_.spinGroup Q) :
    pinGroupToIsometryHom Q ⟨g.1, _root_.spinGroup.mem_pin g.2⟩ =
      spinGroupToIsometryHom Q g := by
  apply DFunLike.ext
  intro v
  apply clifford_ι_injective Q
  change CliffordAlgebra.ι Q
      (lipschitzGroupToIsometryHom Q
        ⟨_root_.pinGroup.toUnits ⟨g.1, _root_.spinGroup.mem_pin g.2⟩, _⟩ v) =
    CliffordAlgebra.ι Q (spinGroupToIsometryHom Q g v)
  rw [ι_lipschitzGroupToIsometryHom,
    show spinGroupToIsometryHom Q g v = spinGroupIsometryEquiv Q g v from rfl,
    ι_spinGroupIsometryEquiv]
  have hval : (↑(_root_.pinGroup.toUnits ⟨g.1, _root_.spinGroup.mem_pin g.2⟩) : CliffordAlgebra Q) =
      (g : CliffordAlgebra Q) := rfl
  have hinv : (↑((_root_.pinGroup.toUnits ⟨g.1, _root_.spinGroup.mem_pin g.2⟩)⁻¹) :
      CliffordAlgebra Q) = CliffordAlgebra.reverse (g : CliffordAlgebra Q) := by
    change (↑((⟨g.1, _root_.spinGroup.mem_pin g.2⟩ : _root_.pinGroup Q)⁻¹ : _root_.pinGroup Q) :
        CliffordAlgebra Q) = _
    rw [← _root_.pinGroup.star_eq_inv]
    change star (g : CliffordAlgebra Q) = CliffordAlgebra.reverse (g : CliffordAlgebra Q)
    rw [CliffordAlgebra.star_def, _root_.spinGroup.involute_eq g.2]
  change CliffordAlgebra.involute (Q := Q)
      (↑(_root_.pinGroup.toUnits ⟨g.1, _root_.spinGroup.mem_pin g.2⟩) : CliffordAlgebra Q) *
      CliffordAlgebra.ι Q v *
      (↑((_root_.pinGroup.toUnits ⟨g.1, _root_.spinGroup.mem_pin g.2⟩)⁻¹) : CliffordAlgebra Q) =
    (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (g : CliffordAlgebra Q)
  rw [hval, hinv, _root_.spinGroup.involute_eq g.2]

/-- `S2-12` (Lipschitz 1886; ABS Thm. (3.11)): Explicit double-cover kernel witness: whenever
`[Nontrivial R]` and `∃ a : M, IsUnit (Q a)`, the central element `-1` belongs to
`_root_.lipschitzGroup Q`, `_root_.pinGroup Q`, and `_root_.spinGroup Q`, is nontrivial
(`-1 ≠ 1`), and lies in the kernel of `lipschitzGroupToIsometryHom Q`,
`pinGroupToIsometryHom Q`, and `spinGroupToIsometryHom Q` (`R3.2`). -/
theorem lipschitz_pin_spin_doubleCover_witness (Q : QuadraticForm R M) [Nontrivial R]
    (ha : ∃ a : M, IsUnit (Q a)) :
    (-1 : (CliffordAlgebra Q)ˣ) ∈ _root_.lipschitzGroup Q ∧
      (-1 : CliffordAlgebra Q) ∈ _root_.pinGroup Q ∧
      (-1 : CliffordAlgebra Q) ∈ _root_.spinGroup Q ∧
      (-1 : CliffordAlgebra Q) ≠ 1 ∧
      ∀ hmem : (-1 : (CliffordAlgebra Q)ˣ) ∈ _root_.lipschitzGroup Q,
        lipschitzGroupToIsometryHom Q ⟨-1, hmem⟩ = 1 := by
  rcases ha with ⟨a, hQa⟩
  let _ : Invertible (Q a) := hQa.invertible
  let u₁ : (CliffordAlgebra Q)ˣ :=
    ⟨CliffordAlgebra.ι Q a, CliffordAlgebra.ι Q (⅟(Q a) • a),
      by
        rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
      by
        rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
  let u₂ : (CliffordAlgebra Q)ˣ :=
    ⟨CliffordAlgebra.ι Q (-(⅟(Q a) • a)), -CliffordAlgebra.ι Q a,
      by
        rw [map_neg, map_smul, neg_mul_neg, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
      by
        rw [map_neg, map_smul, neg_mul_neg, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
  have hu1 : u₁ ∈ _root_.lipschitzGroup Q := Subgroup.subset_closure ⟨a, rfl⟩
  have hu2 : u₂ ∈ _root_.lipschitzGroup Q := Subgroup.subset_closure ⟨-(⅟(Q a) • a), rfl⟩
  have hmul : u₁ * u₂ = -1 := by
    apply Units.ext
    change CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q (-(⅟(Q a) • a)) = -1
    rw [map_neg, map_smul, mul_neg, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
      Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]
  have hneg_lip : (-1 : (CliffordAlgebra Q)ˣ) ∈ _root_.lipschitzGroup Q := by
    rw [← hmul]
    exact Subgroup.mul_mem _ hu1 hu2
  have hneg_unitary : (-1 : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) := by
    rw [Unitary.mem_iff]
    simp [star_neg, star_one]
  have hneg_pin : (-1 : CliffordAlgebra Q) ∈ _root_.pinGroup Q :=
    ⟨⟨-1, hneg_lip, by simp⟩, hneg_unitary⟩
  have hneg_even : (-1 : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q :=
    Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  have hneg_spin : (-1 : CliffordAlgebra Q) ∈ _root_.spinGroup Q :=
    ⟨hneg_pin, hneg_even⟩
  have hneg_ne_one : (-1 : CliffordAlgebra Q) ≠ 1 := by
    intro heq
    have h2 : (2 : R) = 0 := by
      apply clifford_algebraMap_injective Q
      have h11 : algebraMap R (CliffordAlgebra Q) (2 : R) = (1 : CliffordAlgebra Q) + 1 := by
        rw [← one_add_one_eq_two, map_add, map_one]
      rw [h11, map_zero]
      calc
        (1 : CliffordAlgebra Q) + 1 = (-1 : CliffordAlgebra Q) + 1 := by rw [heq]
        _ = 0 := neg_add_cancel 1
    have h10 : (1 : R) = 0 := by
      have hmul2 := congrArg (fun t : R => ⅟(2 : R) * t) h2
      rw [invOf_mul_self, mul_zero] at hmul2
      exact hmul2
    exact one_ne_zero h10
  refine ⟨hneg_lip, hneg_pin, hneg_spin, hneg_ne_one, fun hmem => ?_⟩
  apply DFunLike.ext
  intro v
  apply clifford_ι_injective Q
  rw [ι_lipschitzGroupToIsometryHom]
  change CliffordAlgebra.involute (Q := Q) (-1 : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
      (-1 : CliffordAlgebra Q) = CliffordAlgebra.ι Q v
  rw [map_neg, map_one]
  noncomm_ring

end LipschitzIsometryAndNorm

section LipschitzDimFourObstruction

private local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- `S2-12` (Lipschitz 1886 Ch. II Art. 5 eq. (14), p. 84): Non-regular grade-4
obstruction in `Cl(0, 4)`: the even element `x := 1 + e₁ e₂ e₃ e₄` satisfies
`reverse x * x = 2 + 2 • (e₁ e₂ e₃ e₄) ∉ range (algebraMap ℝ _)`, proving that for
`dim ≥ 4` the generic even Clifford algebra strictly contains the regular Lipschitz
group (`12b` pp. 81, 84). -/
theorem lipschitz1886_dim4_grade4_obstruction :
    let Q4 : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) :=
      (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)).prod
        (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ))
    let e₁ : CliffordAlgebra Q4 := CliffordAlgebra.ι Q4 ((1, 0), (0, 0))
    let e₂ : CliffordAlgebra Q4 := CliffordAlgebra.ι Q4 ((0, 1), (0, 0))
    let e₃ : CliffordAlgebra Q4 := CliffordAlgebra.ι Q4 ((0, 0), (1, 0))
    let e₄ : CliffordAlgebra Q4 := CliffordAlgebra.ι Q4 ((0, 0), (0, 1))
    let x : CliffordAlgebra Q4 := 1 + e₁ * e₂ * e₃ * e₄
    x ∈ CliffordAlgebra.even Q4 ∧
      (CliffordAlgebra.reverse x * x = 2 + (2 : ℝ) • (e₁ * e₂ * e₃ * e₄)) ∧
      CliffordAlgebra.reverse x * x ∉ (algebraMap ℝ (CliffordAlgebra Q4)).range := by
  intro Q4 e₁ e₂ e₃ e₄ x
  have hq1 : Q4 ((1, 0), (0, 0)) = -1 := by simp [Q4]
  have hq2 : Q4 ((0, 1), (0, 0)) = -1 := by simp [Q4]
  have hq3 : Q4 ((0, 0), (1, 0)) = -1 := by simp [Q4]
  have hq4 : Q4 ((0, 0), (0, 1)) = -1 := by simp [Q4]
  have h1sq : e₁ * e₁ = -1 := by
    rw [show e₁ = CliffordAlgebra.ι Q4 _ from rfl, CliffordAlgebra.ι_sq_scalar, hq1, map_neg,
      map_one]
  have h2sq : e₂ * e₂ = -1 := by
    rw [show e₂ = CliffordAlgebra.ι Q4 _ from rfl, CliffordAlgebra.ι_sq_scalar, hq2, map_neg,
      map_one]
  have h3sq : e₃ * e₃ = -1 := by
    rw [show e₃ = CliffordAlgebra.ι Q4 _ from rfl, CliffordAlgebra.ι_sq_scalar, hq3, map_neg,
      map_one]
  have h4sq : e₄ * e₄ = -1 := by
    rw [show e₄ = CliffordAlgebra.ι Q4 _ from rfl, CliffordAlgebra.ι_sq_scalar, hq4, map_neg,
      map_one]
  have ho12 : Q4.IsOrtho ((1, 0), (0, 0)) ((0, 1), (0, 0)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have ho13 : Q4.IsOrtho ((1, 0), (0, 0)) ((0, 0), (1, 0)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have ho14 : Q4.IsOrtho ((1, 0), (0, 0)) ((0, 0), (0, 1)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have ho23 : Q4.IsOrtho ((0, 1), (0, 0)) ((0, 0), (1, 0)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have ho24 : Q4.IsOrtho ((0, 1), (0, 0)) ((0, 0), (0, 1)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have ho34 : Q4.IsOrtho ((0, 0), (1, 0)) ((0, 0), (0, 1)) := by
    simp [Q4, QuadraticMap.isOrtho_def]
  have c12 : e₁ * e₂ = -(e₂ * e₁) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho12
  have c13 : e₁ * e₃ = -(e₃ * e₁) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho13
  have c14 : e₁ * e₄ = -(e₄ * e₁) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho14
  have c23 : e₂ * e₃ = -(e₃ * e₂) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho23
  have c24 : e₂ * e₄ = -(e₄ * e₂) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho24
  have c34 : e₃ * e₄ = -(e₄ * e₃) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho34
  have c21 : e₂ * e₁ = -(e₁ * e₂) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho12.symm
  have c31 : e₃ * e₁ = -(e₁ * e₃) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho13.symm
  have c32 : e₃ * e₂ = -(e₂ * e₃) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho23.symm
  have c41 : e₄ * e₁ = -(e₁ * e₄) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho14.symm
  have c42 : e₄ * e₂ = -(e₂ * e₄) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho24.symm
  have c43 : e₄ * e₃ = -(e₃ * e₄) := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ho34.symm
  have he1234_even : e₁ * e₂ * e₃ * e₄ ∈ CliffordAlgebra.even Q4 := by
    have h12 : e₁ * e₂ ∈ CliffordAlgebra.evenOdd Q4 0 :=
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q4 _ _
    have h34 : e₃ * e₄ ∈ CliffordAlgebra.evenOdd Q4 0 :=
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q4 _ _
    have hmul := CliffordAlgebra.evenOdd_mul_le Q4 0 0 (Submodule.mul_mem_mul h12 h34)
    change (e₁ * e₂) * (e₃ * e₄) ∈ CliffordAlgebra.even Q4 at hmul
    rw [← _root_.mul_assoc (e₁ * e₂) e₃ e₄] at hmul
    exact hmul
  have hx_even : x ∈ CliffordAlgebra.even Q4 :=
    Subalgebra.add_mem _ (Subalgebra.one_mem _) he1234_even
  have hrev_eq : e₄ * e₃ * e₂ * e₁ = e₁ * e₂ * e₃ * e₄ := by
    calc
      e₄ * e₃ * e₂ * e₁ = e₄ * (e₃ * (e₂ * e₁)) := by noncomm_ring
      _ = e₄ * (e₃ * (-(e₁ * e₂))) := by rw [c21]
      _ = -(e₄ * ((e₃ * e₁) * e₂)) := by noncomm_ring
      _ = -(e₄ * ((-(e₁ * e₃)) * e₂)) := by rw [c31]
      _ = (e₄ * e₁) * (e₃ * e₂) := by noncomm_ring
      _ = (-(e₁ * e₄)) * (-(e₂ * e₃)) := by rw [c41, c32]
      _ = e₁ * (e₄ * e₂) * e₃ := by noncomm_ring
      _ = e₁ * (-(e₂ * e₄)) * e₃ := by rw [c42]
      _ = -(e₁ * e₂ * (e₄ * e₃)) := by noncomm_ring
      _ = -(e₁ * e₂ * (-(e₃ * e₄))) := by rw [c43]
      _ = e₁ * e₂ * e₃ * e₄ := by noncomm_ring
  have hrev_4 : CliffordAlgebra.reverse (e₁ * e₂ * e₃ * e₄) = e₁ * e₂ * e₃ * e₄ := by
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul,
      CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι,
      CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
    change e₄ * (e₃ * (e₂ * e₁)) = e₁ * e₂ * e₃ * e₄
    calc
      e₄ * (e₃ * (e₂ * e₁)) = e₄ * e₃ * e₂ * e₁ := by noncomm_ring
      _ = e₁ * e₂ * e₃ * e₄ := hrev_eq
  have hsq_4 : (e₁ * e₂ * e₃ * e₄) * (e₁ * e₂ * e₃ * e₄) = 1 := by
    calc
      (e₁ * e₂ * e₃ * e₄) * (e₁ * e₂ * e₃ * e₄)
          = (e₁ * e₂ * e₃ * e₄) * (e₄ * e₃ * e₂ * e₁) := by rw [hrev_eq]
      _ = e₁ * e₂ * e₃ * (e₄ * e₄) * e₃ * e₂ * e₁ := by noncomm_ring
      _ = -(e₁ * e₂ * (e₃ * e₃) * e₂ * e₁) := by rw [h4sq]; noncomm_ring
      _ = (e₁ * (e₂ * e₂) * e₁) := by rw [h3sq]; noncomm_ring
      _ = -(e₁ * e₁) := by rw [h2sq]; noncomm_ring
      _ = 1 := by rw [h1sq, neg_neg]
  have hnorm : CliffordAlgebra.reverse x * x = 2 + (2 : ℝ) • (e₁ * e₂ * e₃ * e₄) := by
    have hrevx : CliffordAlgebra.reverse x = x := by
      dsimp [x]
      rw [map_add, CliffordAlgebra.reverse.map_one, hrev_4]
    rw [hrevx]
    dsimp [x]
    calc
      (1 + e₁ * e₂ * e₃ * e₄) * (1 + e₁ * e₂ * e₃ * e₄)
          = 1 + e₁ * e₂ * e₃ * e₄ + e₁ * e₂ * e₃ * e₄ +
              (e₁ * e₂ * e₃ * e₄) * (e₁ * e₂ * e₃ * e₄) := by noncomm_ring
      _ = 1 + 1 + (e₁ * e₂ * e₃ * e₄ + e₁ * e₂ * e₃ * e₄) := by rw [hsq_4]; abel
      _ = 2 + (2 : ℝ) • (e₁ * e₂ * e₃ * e₄) := by
          rw [one_add_one_eq_two, ← two_smul ℝ]
  have hnot_range : CliffordAlgebra.reverse x * x ∉ (algebraMap ℝ (CliffordAlgebra Q4)).range := by
    rw [hnorm]
    rintro ⟨r, hr⟩
    have htrace : InfoGeometry.Riemannian.hTrace_cl Q4 (e₁ * e₂ * e₃ * e₄) = 0 := by
      have heq_ext : CliffordAlgebra.equivExterior Q4 (e₁ * e₂ * e₃ * e₄) =
          ExteriorAlgebra.ι ℝ ((1, 0), (0, 0)) * ExteriorAlgebra.ι ℝ ((0, 1), (0, 0)) *
            ExteriorAlgebra.ι ℝ ((0, 0), (1, 0)) * ExteriorAlgebra.ι ℝ ((0, 0), (0, 1)) := by
        have h34_ext : CliffordAlgebra.equivExterior Q4 (e₃ * e₄) =
            ExteriorAlgebra.ι ℝ ((0, 0), (1, 0)) * ExteriorAlgebra.ι ℝ ((0, 0), (0, 1)) := by
          change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
              (e₃ * e₄) = _
          rw [CliffordAlgebra.changeForm_ι_mul_ι]
          have ha : QuadraticMap.associated (R := ℝ) (-Q4) ((0, 0), (1, 0)) ((0, 0), (0, 1)) = 0 := by
            simp [QuadraticMap.associated_apply, Q4]
          rw [ha, map_zero, sub_zero]
        have h234_ext : CliffordAlgebra.equivExterior Q4 (e₂ * (e₃ * e₄)) =
            ExteriorAlgebra.ι ℝ ((0, 1), (0, 0)) *
              (ExteriorAlgebra.ι ℝ ((0, 0), (1, 0)) * ExteriorAlgebra.ι ℝ ((0, 0), (0, 1))) := by
          change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
              (e₂ * (e₃ * e₄)) = _
          rw [CliffordAlgebra.changeForm_ι_mul]
          have hc1 : CliffordAlgebra.contractLeft (QuadraticMap.associated (R := ℝ) (-Q4) ((0, 1), (0, 0)))
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof (e₃ * e₄)) = 0 := by
            have h' := h34_ext
            change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof (e₃ * e₄) = _ at h'
            rw [h', CliffordAlgebra.contractLeft_ι_mul]
            have ha1 : QuadraticMap.associated (R := ℝ) (-Q4) ((0, 1), (0, 0)) ((0, 0), (1, 0)) = 0 := by
              simp [Q4, QuadraticMap.associated_apply]
            have ha2 : QuadraticMap.associated (R := ℝ) (-Q4) ((0, 1), (0, 0)) ((0, 0), (0, 1)) = 0 := by
              simp [Q4, QuadraticMap.associated_apply]
            rw [CliffordAlgebra.contractLeft_ι, ha1, ha2]
            simp
          rw [hc1, sub_zero]
          change ExteriorAlgebra.ι ℝ ((0, 1), (0, 0)) * CliffordAlgebra.equivExterior Q4 (e₃ * e₄) = _
          rw [h34_ext]
        have h1234_ext : CliffordAlgebra.equivExterior Q4 (e₁ * (e₂ * (e₃ * e₄))) =
            ExteriorAlgebra.ι ℝ ((1, 0), (0, 0)) *
              (ExteriorAlgebra.ι ℝ ((0, 1), (0, 0)) *
                (ExteriorAlgebra.ι ℝ ((0, 0), (1, 0)) * ExteriorAlgebra.ι ℝ ((0, 0), (0, 1)))) := by
          change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
              (e₁ * (e₂ * (e₃ * e₄))) = _
          rw [CliffordAlgebra.changeForm_ι_mul]
          have hc2 : CliffordAlgebra.contractLeft (QuadraticMap.associated (R := ℝ) (-Q4) ((1, 0), (0, 0)))
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof (e₂ * (e₃ * e₄))) = 0 := by
            have h' := h234_ext
            change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof (e₂ * (e₃ * e₄)) = _ at h'
            rw [h', CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
              CliffordAlgebra.contractLeft_ι]
            have ha1 : QuadraticMap.associated (R := ℝ) (-Q4) ((1, 0), (0, 0)) ((0, 1), (0, 0)) = 0 := by
              simp [Q4, QuadraticMap.associated_apply]
            have ha2 : QuadraticMap.associated (R := ℝ) (-Q4) ((1, 0), (0, 0)) ((0, 0), (1, 0)) = 0 := by
              simp [Q4, QuadraticMap.associated_apply]
            have ha3 : QuadraticMap.associated (R := ℝ) (-Q4) ((1, 0), (0, 0)) ((0, 0), (0, 1)) = 0 := by
              simp [Q4, QuadraticMap.associated_apply]
            rw [ha1, ha2, ha3]
            simp
          rw [hc2, sub_zero]
          change ExteriorAlgebra.ι ℝ ((1, 0), (0, 0)) * CliffordAlgebra.equivExterior Q4 (e₂ * (e₃ * e₄)) = _
          rw [h234_ext]
        simp only [← _root_.mul_assoc] at h1234_ext
        exact h1234_ext
      change ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q4 (e₁ * e₂ * e₃ * e₄)) = 0
      rw [heq_ext, map_mul, map_mul, map_mul]
      have hι0 : ∀ v : (ℝ × ℝ) × ℝ × ℝ, ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ι ℝ v) = 0 :=
        fun v => by
          change (ExteriorAlgebra.lift ℝ ⟨(0 : ((ℝ × ℝ) × ℝ × ℝ) →ₗ[ℝ] ℝ), _⟩)
            (ExteriorAlgebra.ι ℝ v) = 0
          rw [ExteriorAlgebra.lift_ι_apply]
          rfl
      rw [hι0, hι0, hι0, hι0]
      simp
    have hr_eq : r = 2 := by
      have ht := congrArg (InfoGeometry.Riemannian.hTrace_cl Q4) hr
      rw [hTrace_cl_algebraMap_local, map_add, map_smul, htrace, smul_zero, add_zero] at ht
      have h2eq : InfoGeometry.Riemannian.hTrace_cl Q4 (2 : CliffordAlgebra Q4) = 2 := by
        rw [show (2 : CliffordAlgebra Q4) = algebraMap ℝ (CliffordAlgebra Q4) 2 from
          (map_ofNat _ 2).symm, hTrace_cl_algebraMap_local]
      rw [h2eq] at ht
      exact ht
    rw [hr_eq] at hr
    have h2zero : (2 : ℝ) • (e₁ * e₂ * e₃ * e₄) = 0 := by
      have hr' : algebraMap ℝ (CliffordAlgebra Q4) (2 : ℝ) = (2 : CliffordAlgebra Q4) :=
        map_ofNat _ 2
      rw [hr'] at hr
      have hadd : (2 : CliffordAlgebra Q4) + (2 : ℝ) • (e₁ * e₂ * e₃ * e₄) =
          (2 : CliffordAlgebra Q4) + 0 := by rw [add_zero]; exact hr.symm
      exact add_left_cancel hadd
    have hzero : e₁ * e₂ * e₃ * e₄ = 0 := by
      have h2 := congrArg (fun z : CliffordAlgebra Q4 => (⅟(2 : ℝ)) • z) h2zero
      simpa [smul_smul, invOf_mul_self, one_smul] using h2
    rw [hzero, mul_zero] at hsq_4
    exact zero_ne_one hsq_4
  exact ⟨hx_even, hnorm, hnot_range⟩

end LipschitzDimFourObstruction

end LipschitzPrimary

/-!
## Section 3 (`S2-13`): Witt (1937) Coordinate-Free Quadratic Modules, Hyperbolic Plane,
Decomposition, Cancellation, & Extension
-/

section WittPrimary

section WittHyperbolicPlane

/-- `S2-13` (Witt 1937 *Crelle* 176 Hilfssatz p. 34): Standard coordinate-free hyperbolic
plane quadratic form `Q(x, y) = x * y` on `K × K`. -/
def hyperbolicPlaneQuad (K : Type*) [CommRing K] : QuadraticForm K (K × K) :=
  QuadraticMap.linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K)

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): Evaluation formula `hyperbolicPlaneQuad K v = v.1 * v.2`. -/
@[simp] theorem hyperbolicPlaneQuad_apply {K : Type*} [CommRing K] (v : K × K) :
    hyperbolicPlaneQuad K v = v.1 * v.2 :=
  rfl

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): `hyperbolicPlaneQuad K` is nondegenerate over any
field `K` with `Invertible (2 : K)` (`R3.2`). -/
theorem hyperbolicPlaneQuad_nondegenerate {K : Type*} [Field K] [Invertible (2 : K)] :
    (hyperbolicPlaneQuad K).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  ext ⟨x, y⟩
  simp only [QuadraticMap.mem_radical_iff', Submodule.mem_bot, Prod.mk_eq_zero,
    hyperbolicPlaneQuad_apply, Prod.fst_add, Prod.snd_add]
  refine ⟨fun ⟨hxy, h⟩ => ?_, fun ⟨hx, hy⟩ => ⟨by rw [hx, zero_mul], fun ⟨a, b⟩ => by
    rw [hx, hy, zero_add, zero_add]⟩⟩
  have h1 := h (0, 1)
  have h2 := h (1, 0)
  simp only [add_zero, zero_mul, mul_zero] at h1 h2
  have hx0 : x = 0 := by
    calc
      x = x * (y + 1) - x * y := by ring
      _ = 0 - 0 := by rw [h1, hxy]
      _ = 0 := sub_zero 0
  have hy0 : y = 0 := by
    calc
      y = (x + 1) * y - x * y := by ring
      _ = 0 - 0 := by rw [h2, hxy]
      _ = 0 := sub_zero 0
  exact ⟨hx0, hy0⟩

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): `hyperbolicPlaneQuad K` is isotropic (`¬ Anisotropic`). -/
theorem hyperbolicPlaneQuad_not_anisotropic {K : Type*} [Field K] :
    ¬ (hyperbolicPlaneQuad K).Anisotropic := by
  intro h
  have h1 := h (1, 0) (by simp)
  simp at h1

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): Every hyperbolic plane `x * y` is isometric to the
split difference of squares `x² - y²` over `[Field K] [Invertible (2 : K)]`. -/
def hyperbolicPlaneQuad_equiv_split (K : Type*) [Field K] [Invertible (2 : K)] :
    (hyperbolicPlaneQuad K).IsometryEquiv
      ((QuadraticMap.sq (R := K)).prod (-QuadraticMap.sq (R := K))) where
  toFun v := (⅟(2 : K) * (v.1 + v.2), ⅟(2 : K) * (v.1 - v.2))
  invFun w := (w.1 + w.2, w.1 - w.2)
  left_inv v := by
    ext <;> dsimp
    · rw [← mul_add, show (v.1 + v.2) + (v.1 - v.2) = (2 : K) * v.1 by ring,
        ← _root_.mul_assoc (⅟(2 : K)), invOf_mul_self, _root_.one_mul]
    · rw [← mul_sub, show (v.1 + v.2) - (v.1 - v.2) = (2 : K) * v.2 by ring,
        ← _root_.mul_assoc (⅟(2 : K)), invOf_mul_self, _root_.one_mul]
  right_inv w := by
    ext <;> dsimp
    · rw [show ⅟(2 : K) * (w.1 + w.2 + (w.1 - w.2)) = ⅟(2 : K) * ((2 : K) * w.1) by ring,
        ← _root_.mul_assoc (⅟(2 : K)), invOf_mul_self, _root_.one_mul]
    · rw [show ⅟(2 : K) * (w.1 + w.2 - (w.1 - w.2)) = ⅟(2 : K) * ((2 : K) * w.2) by ring,
        ← _root_.mul_assoc (⅟(2 : K)), invOf_mul_self, _root_.one_mul]
  map_add' u v := by ext <;> dsimp <;> ring
  map_smul' c v := by ext <;> dsimp <;> ring
  map_app' v := by
    simp only [QuadraticMap.prod_apply, neg_apply, QuadraticMap.sq_apply,
      hyperbolicPlaneQuad_apply]
    have h22 : ⅟(2 : K) * ⅟(2 : K) * (4 : K) = 1 := by
      calc
        ⅟(2 : K) * ⅟(2 : K) * (4 : K) = (⅟(2 : K) * (2 : K)) * (⅟(2 : K) * (2 : K)) := by ring
        _ = 1 * 1 := by rw [invOf_mul_self]
        _ = 1 := _root_.mul_one (1 : K)
    calc
      (⅟(2 : K) * (v.1 + v.2)) * (⅟(2 : K) * (v.1 + v.2)) +
          -(⅟(2 : K) * (v.1 - v.2) * (⅟(2 : K) * (v.1 - v.2)))
          = (⅟(2 : K) * ⅟(2 : K) * (4 : K)) * (v.1 * v.2) := by ring
      _ = 1 * (v.1 * v.2) := by rw [h22]
      _ = v.1 * v.2 := _root_.one_mul (v.1 * v.2)

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): Coordinate-free characterization of a hyperbolic
plane: a 2-dimensional nondegenerate isotropic quadratic space. -/
def IsHyperbolicPlane {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  Module.finrank K V = 2 ∧ Q.Nondegenerate ∧ ¬ Q.Anisotropic

/-- `S2-13` (Witt 1937 Satz 1 & Hilfssatz, pp. 33–34): Given a nondegenerate quadratic
space `(V, Q)` over `[Field K] [Invertible (2 : K)]` and any nonzero isotropic vector
`u ≠ 0`, `Q u = 0`, there exists a complementary isotropic vector `w : V` with `Q w = 0`,
`QuadraticMap.polar Q u w = 1`, such that `H := span K {u, w}` has `finrank K H = 2`,
`(Q.restrict H).Nondegenerate`, `IsCompl H (LinearMap.BilinForm.orthogonal Q.associated H)`, and
`(Q.restrict H).IsometryEquiv (hyperbolicPlaneQuad K)` (`R3.2`). -/
theorem exists_hyperbolic_pair_of_isotropic {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {u : V} (hu_ne : u ≠ 0) (hu_iso : Q u = 0) :
    ∃ w : V, Q w = 0 ∧ QuadraticMap.polar Q u w = 1 ∧
      Module.finrank K (Submodule.span K ({u, w} : Set V)) = 2 ∧
      (Q.restrict (Submodule.span K ({u, w} : Set V))).Nondegenerate ∧
      IsCompl (Submodule.span K ({u, w} : Set V))
        (LinearMap.BilinForm.orthogonal Q.associated (Submodule.span K ({u, w} : Set V))) ∧
      Nonempty ((Q.restrict (Submodule.span K ({u, w} : Set V))).IsometryEquiv
        (hyperbolicPlaneQuad K)) := by
  have hP_nondeg : (QuadraticMap.polarBilin Q).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff).mpr hQ
  have hP_ker : (QuadraticMap.polarBilin Q).ker = ⊥ :=
    LinearMap.separatingLeft_iff_ker_eq_bot.mp hP_nondeg.1
  have hu_not_ker : QuadraticMap.polarBilin Q u ≠ 0 := by
    intro hzero
    have hker : u ∈ (QuadraticMap.polarBilin Q).ker := by
      rw [LinearMap.mem_ker]
      exact hzero
    rw [hP_ker, Submodule.mem_bot] at hker
    exact hu_ne hker
  obtain ⟨y₀, hy₀⟩ := DFunLike.ne_iff.mp hu_not_ker
  have hy₀' : QuadraticMap.polar Q u y₀ ≠ 0 := hy₀
  let y : V := (QuadraticMap.polar Q u y₀)⁻¹ • y₀
  have huy : QuadraticMap.polar Q u y = 1 := by
    dsimp [y]
    rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy₀']
  let w : V := y - Q y • u
  have huw : QuadraticMap.polar Q u w = 1 := by
    dsimp [w]
    rw [QuadraticMap.polar_sub_right, huy, QuadraticMap.polar_smul_right, QuadraticMap.polar_self,
      hu_iso, nsmul_zero, smul_zero, sub_zero]
  have hw_iso : Q w = 0 := by
    dsimp [w]
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
      QuadraticMap.map_smul Q (Q y) u, hu_iso, smul_zero, add_zero,
      QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q y u,
      huy, smul_eq_mul, _root_.mul_one, add_neg_cancel]
  let H : Submodule K V := Submodule.span K ({u, w} : Set V)
  have huH : u ∈ H := Submodule.subset_span (by simp)
  have hwH : w ∈ H := Submodule.subset_span (by simp)
  let toH : K × K →ₗ[K] H :=
    { toFun := fun p => ⟨p.1 • u + p.2 • w,
        Submodule.add_mem _ (Submodule.smul_mem _ _ huH) (Submodule.smul_mem _ _ hwH)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
        abel
      map_smul' := fun c p => by
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, SetLike.val_smul,
          smul_add, smul_smul, smul_eq_mul] }
  have htoH_inj : Function.Injective toH := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have hpv : p.1 • u + p.2 • w = 0 := congrArg Subtype.val hp
    have hp_w : p.2 = 0 := by
      have h' := congrArg (fun z => QuadraticMap.polar Q u z) hpv
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hu_iso, nsmul_zero, smul_zero,
        zero_add, huw, smul_eq_mul, _root_.mul_one, QuadraticMap.polar_zero_right] at h'
      exact h'
    have hp_u : p.1 = 0 := by
      have h' := congrArg (fun z => QuadraticMap.polar Q z w) hpv
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hw_iso, nsmul_zero, smul_zero,
        add_zero, huw, smul_eq_mul, _root_.mul_one, QuadraticMap.polar_zero_left] at h'
      exact h'
    ext <;> assumption
  have htoH_surj : Function.Surjective toH := by
    intro ⟨z, hz⟩
    induction hz using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨(1, 0), by apply Subtype.ext; simp [toH]⟩
      · exact ⟨(0, 1), by apply Subtype.ext; simp [toH]⟩
    | zero => exact ⟨(0, 0), by apply Subtype.ext; simp [toH]⟩
    | add x y _ _ ihx ihy =>
      rcases ihx with ⟨px, hpx⟩
      rcases ihy with ⟨py, hpy⟩
      refine ⟨px + py, ?_⟩
      apply Subtype.ext
      have h1 := congrArg Subtype.val hpx
      have h2 := congrArg Subtype.val hpy
      simp only [toH, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2 ⊢
      simp only [Prod.fst_add, Prod.snd_add, add_smul]
      rw [← h1, ← h2]
      abel
    | smul c x _ ihx =>
      rcases ihx with ⟨px, hpx⟩
      refine ⟨c • px, ?_⟩
      apply Subtype.ext
      have h1 := congrArg Subtype.val hpx
      simp only [toH, LinearMap.coe_mk, AddHom.coe_mk] at h1 ⊢
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [← smul_smul, ← smul_smul, ← smul_add, h1]
  let e_lin : (K × K) ≃ₗ[K] H := LinearEquiv.ofBijective toH ⟨htoH_inj, htoH_surj⟩
  let e_iso : (hyperbolicPlaneQuad K).IsometryEquiv (Q.restrict H) :=
    { toLinearEquiv := e_lin
      map_app' := fun p => by
        change Q (p.1 • u + p.2 • w) = p.1 * p.2
        rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q,
          hu_iso, hw_iso, smul_zero, smul_zero, zero_add, zero_add,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, huw,
          smul_eq_mul, smul_eq_mul, _root_.mul_one] }
  have hfin : Module.finrank K H = 2 := by
    rw [← LinearEquiv.finrank_eq e_lin, Module.finrank_prod, Module.finrank_self]
  have hH_nondeg : (Q.restrict H).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_bot, Subtype.ext_iff, ZeroMemClass.coe_zero]
    rw [QuadraticMap.mem_radical_iff']
    constructor
    · intro ⟨hx0_Q, hx_pol⟩
      change Q x = 0 at hx0_Q
      obtain ⟨p, hp⟩ := htoH_surj ⟨x, hx⟩
      have hpx : x = p.1 • u + p.2 • w := (congrArg Subtype.val hp).symm
      have hp1 : Q (x + u) = Q u := hx_pol ⟨u, huH⟩
      have hp2 : Q (x + w) = Q w := hx_pol ⟨w, hwH⟩
      have hpol_u : QuadraticMap.polar Q x u = 0 := by
        change Q (x + u) - Q x - Q u = 0
        rw [hp1, hx0_Q, sub_zero, sub_self]
      have hpol_w : QuadraticMap.polar Q x w = 0 := by
        change Q (x + w) - Q x - Q w = 0
        rw [hp2, hx0_Q, sub_zero, sub_self]
      rw [hpx, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hu_iso, nsmul_zero, smul_zero,
        zero_add, QuadraticMap.polar_comm, huw, smul_eq_mul, _root_.mul_one] at hpol_u
      rw [hpx, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hw_iso, nsmul_zero, smul_zero,
        add_zero, huw, smul_eq_mul, _root_.mul_one] at hpol_w
      rw [hpx, hpol_u, hpol_w, zero_smul, zero_smul, add_zero]
    · intro hx0
      subst hx0
      exact ⟨by simp, fun y => by simp⟩
  have hB_H_nondeg : (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) H).Nondegenerate := by
    have h1 : LinearMap.BilinForm.restrict (QuadraticMap.associated Q) H =
        QuadraticMap.associated (Q.restrict H) := rfl
    change LinearMap.Nondegenerate (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) H)
    rw [h1]
    exact (QuadraticMap.nondegenerate_associated_iff (Q := Q.restrict H)).mpr hH_nondeg
  have hB_refl : (QuadraticMap.associated (R := K) Q).IsRefl := fun x y h => by
    have hs := QuadraticMap.associated_isSymm K Q y x
    dsimp only [QuadraticMap.associated] at hs h ⊢
    rwa [hs]
  have hcompl : IsCompl H (LinearMap.BilinForm.orthogonal Q.associated H) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB_refl hB_H_nondeg
  exact ⟨w, hw_iso, huw, hfin, hH_nondeg, hcompl, ⟨e_iso.symm⟩⟩

/-- `S2-13` (Witt 1937 Hilfssatz p. 34): A 2-dimensional nondegenerate quadratic space is
a hyperbolic plane (`IsHyperbolicPlane Q`) if and only if it is isometric to
`hyperbolicPlaneQuad K` (`R3.2`). -/
theorem isHyperbolicPlane_equiv_hyperbolicPlaneQuad {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    IsHyperbolicPlane Q ↔ Nonempty (Q.IsometryEquiv (hyperbolicPlaneQuad K)) := by
  constructor
  · rintro ⟨hfin, hnondeg, haniso⟩
    have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ (n := 1) hfin
    rw [QuadraticMap.not_anisotropic_iff_exists] at haniso
    rcases haniso with ⟨u, hu_ne, hu_iso⟩
    obtain ⟨w, _, _, hHfin, _, _, ⟨eH⟩⟩ :=
      exists_hyperbolic_pair_of_isotropic Q hnondeg hu_ne hu_iso
    let H := Submodule.span K ({u, w} : Set V)
    have htop : H = ⊤ := Submodule.eq_top_of_finrank_eq (hHfin.trans hfin.symm)
    let eTop : Q.IsometryEquiv (Q.restrict H) :=
      { toLinearEquiv := (Submodule.topEquiv).symm.trans (LinearEquiv.ofEq ⊤ H htop.symm)
        map_app' := fun _ => rfl }
    exact ⟨eTop.trans eH⟩
  · rintro ⟨e⟩
    have hfin : Module.finrank K V = 2 := by
      rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_prod, Module.finrank_self]
    have hnondeg : Q.Nondegenerate := by
      rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
      have hrad : (hyperbolicPlaneQuad K).radical = ⊥ :=
        (QuadraticMap.nondegenerate_iff_radical_eq_bot).mp hyperbolicPlaneQuad_nondegenerate
      ext v
      simp only [Submodule.mem_bot]
      constructor
      · intro hv
        have hev : e v ∈ (hyperbolicPlaneQuad K).radical := by
          rw [QuadraticMap.mem_radical_iff'] at hv ⊢
          refine ⟨by rw [e.map_app]; exact hv.1, fun w => ?_⟩
          have hw : Q (v + e.symm w) = Q (e.symm w) := hv.2 (e.symm w)
          rw [← e.map_app (v + e.symm w), ← e.map_app (e.symm w), map_add,
            e.apply_symm_apply] at hw
          exact hw
        rw [hrad, Submodule.mem_bot] at hev
        exact e.injective (hev.trans (map_zero e).symm)
      · rintro rfl
        rw [QuadraticMap.mem_radical_iff']
        exact ⟨map_zero Q, fun y => by rw [zero_add]⟩
    have haniso : ¬ Q.Anisotropic := by
      intro h
      apply hyperbolicPlaneQuad_not_anisotropic (K := K)
      intro w hw
      have hv : e.symm w = 0 := h (e.symm w) (by
        rw [← e.map_app, e.apply_symm_apply, hw])
      calc
        w = e (e.symm w) := (e.apply_symm_apply w).symm
        _ = e 0 := by rw [hv]
        _ = 0 := map_zero e
    exact ⟨hfin, hnondeg, haniso⟩

/-- `S2-13` (Witt 1937 Satz 5 p. 35): Orthogonal sum of `m` hyperbolic planes
`ℍ^m := ⨁_{i : Fin m} hyperbolicPlaneQuad K`. -/
def hyperbolicSumQuad (K : Type*) [CommRing K] (m : ℕ) :
    QuadraticForm K (Fin m → K × K) :=
  QuadraticMap.pi (fun _ : Fin m => hyperbolicPlaneQuad K)

private def isometryEquivProdOfIsCompl {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {S T : Submodule K V}
    (hcompl : IsCompl S T) (hortho : ∀ s ∈ S, ∀ t ∈ T, Q.associated s t = 0) :
    Q.IsometryEquiv ((Q.restrict S).prod (Q.restrict T)) where
  toLinearEquiv := (Submodule.prodEquivOfIsCompl S T hcompl).symm
  map_app' v := by
    let p := (Submodule.prodEquivOfIsCompl S T hcompl).symm v
    have hv : v = p.1.1 + p.2.1 := by
      have hp := (Submodule.prodEquivOfIsCompl S T hcompl).apply_symm_apply v
      exact congrArg id hp.symm
    change Q p.1.1 + Q p.2.1 = Q v
    rw [hv, QuadraticMap.map_add Q]
    have hp : QuadraticMap.polar Q p.1.1 p.2.1 = (2 : K) * Q.associated p.1.1 p.2.1 := by
      change QuadraticMap.polar Q p.1.1 p.2.1 =
        (2 : K) * (⅟(2 : K) * QuadraticMap.polar Q p.1.1 p.2.1)
      rw [← _root_.mul_assoc, mul_invOf_self, _root_.one_mul]
    rw [hp, hortho p.1.1 p.1.2 p.2.1 p.2.2, mul_zero, add_zero]

private def hyperbolicSumSuccEquiv (K : Type*) [CommRing K] (m : ℕ) :
    ((hyperbolicPlaneQuad K).prod (hyperbolicSumQuad K m)).IsometryEquiv
      (hyperbolicSumQuad K (m + 1)) where
  toLinearEquiv :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun f => (f 0, fun i => f i.succ)
      left_inv := fun p => by
        ext <;> simp [Fin.cons_zero, Fin.cons_succ]
      right_inv := fun f => by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]
      map_add' := fun p q => by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]
      map_smul' := fun c p => by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ] }
  map_app' p := by
    simp only [hyperbolicSumQuad, QuadraticMap.pi_apply, QuadraticMap.prod_apply]
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]

private def prodAssocSwapMid {K A B C : Type*} [CommRing K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (QA : QuadraticForm K A) (QB : QuadraticForm K B) (QC : QuadraticForm K C) :
    (QA.prod (QB.prod QC)).IsometryEquiv (QB.prod (QA.prod QC)) where
  toLinearEquiv :=
    { toFun := fun ⟨a, b, c⟩ => (b, a, c)
      invFun := fun ⟨b, a, c⟩ => (a, b, c)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl
      map_add' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => rfl
      map_smul' := fun _ ⟨_, _, _⟩ => rfl }
  map_app' := fun ⟨a, b, c⟩ => by
    simp only [QuadraticMap.prod_apply]
    ring

/-- `S2-13` (Witt 1937 Satz 5, p. 35): **Witt Orthogonal/Hyperbolic Decomposition**:
Every finite-dimensional nondegenerate quadratic space `(V, Q)` over `[Field K] [Invertible (2 : K)]`
decomposes orthogonally as `V ≃_q W ⊥ ℍ^m` where `W ≤ V` is a subspace on which `Q.restrict W`
is anisotropic (`R3.2`). -/
theorem witt_orthogonal_hyperbolic_decomposition {K : Type*} [Field K] [Invertible (2 : K)] :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V),
      Module.finrank K V = n → Q.Nondegenerate →
        ∃ (m : ℕ) (W : Subspace K V),
          (Q.restrict W).Anisotropic ∧
          Nonempty (Q.IsometryEquiv ((Q.restrict W).prod (hyperbolicSumQuad K m))) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro V _ _ _ Q hfin hQ
    by_cases haniso : Q.Anisotropic
    · refine ⟨0, ⊤, ?_, ?_⟩
      · intro w hw
        apply Subtype.ext
        exact haniso w.1 hw
      · refine ⟨{
          toLinearEquiv :=
            { toFun := fun v => (⟨v, trivial⟩, fun i => Fin.elim0 i)
              invFun := fun p => p.1.1
              left_inv := fun _ => rfl
              right_inv := fun p => Prod.ext rfl (funext fun i => Fin.elim0 i)
              map_add' := fun _ _ => Prod.ext rfl (funext fun i => Fin.elim0 i)
              map_smul' := fun _ _ => Prod.ext rfl (funext fun i => Fin.elim0 i) }
          map_app' := fun v => by
            simp [hyperbolicSumQuad, QuadraticMap.pi_apply] }⟩
    · rw [QuadraticMap.not_anisotropic_iff_exists] at haniso
      rcases haniso with ⟨u, hu_ne, hu_iso⟩
      obtain ⟨w, _, _, hHfin, _, hcompl, ⟨eH⟩⟩ :=
        exists_hyperbolic_pair_of_isotropic Q hQ hu_ne hu_iso
      let H := Submodule.span K ({u, w} : Set V)
      let Hperp := LinearMap.BilinForm.orthogonal Q.associated H
      have hortho : ∀ h ∈ H, ∀ k ∈ Hperp, Q.associated h k = 0 := by
        intro h hh k hk
        exact hk h hh
      let eSplit : Q.IsometryEquiv ((Q.restrict H).prod (Q.restrict Hperp)) :=
        isometryEquivProdOfIsCompl Q hcompl hortho
      have hB_nondeg : (Q.associated (R := K)).Nondegenerate :=
        (QuadraticMap.nondegenerate_associated_iff).mpr hQ
      have hB_refl : (Q.associated (R := K)).IsRefl := fun x y h =>
        (QuadraticMap.associated_isSymm K Q y x).trans h
      have hB_perp_nondeg :
          (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) Hperp).Nondegenerate := by
        refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
          Q.associated hB_refl ?_
        change Disjoint Hperp (LinearMap.BilinForm.orthogonal Q.associated Hperp)
        rw [LinearMap.BilinForm.orthogonal_orthogonal hB_nondeg hB_refl H]
        exact hcompl.symm.disjoint
      have hperp_nondeg : (Q.restrict Hperp).Nondegenerate := by
        have h1 : LinearMap.BilinForm.restrict (QuadraticMap.associated Q) Hperp =
            QuadraticMap.associated (Q.restrict Hperp) := rfl
        change LinearMap.Nondegenerate
          (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) Hperp) at hB_perp_nondeg
        rw [h1] at hB_perp_nondeg
        exact (QuadraticMap.nondegenerate_associated_iff (Q := Q.restrict Hperp)).mp hB_perp_nondeg
      have hfin_perp : Module.finrank K Hperp < n := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
        change Module.finrank K H + Module.finrank K Hperp = Module.finrank K V at hsum
        rw [hHfin, hfin] at hsum
        omega
      obtain ⟨m', W', hW'_aniso, ⟨ePerp⟩⟩ :=
        ih (Module.finrank K Hperp) hfin_perp (Q.restrict Hperp) rfl hperp_nondeg
      let W : Subspace K V := Submodule.map Hperp.subtype W'
      let eW : W' ≃ₗ[K] W := Submodule.equivMapOfInjective Hperp.subtype (Submodule.subtype_injective Hperp) W'
      let eW_iso : ((Q.restrict Hperp).restrict W').IsometryEquiv (Q.restrict W) :=
        { toLinearEquiv := eW
          map_app' := fun ⟨_, _⟩ => rfl }
      have hW_aniso : (Q.restrict W).Anisotropic := by
        intro x hx
        have hx' := hW'_aniso (eW_iso.symm x)
          (by rw [← eW_iso.map_app, eW_iso.apply_symm_apply]; exact hx)
        simpa using congrArg eW_iso hx'
      let eTotal : Q.IsometryEquiv ((Q.restrict W).prod (hyperbolicSumQuad K (m' + 1))) :=
        eSplit.trans
          ((QuadraticMap.IsometryEquiv.prod eH
              (ePerp.trans (QuadraticMap.IsometryEquiv.prod eW_iso
                (QuadraticMap.IsometryEquiv.refl _)))).trans
            ((prodAssocSwapMid (hyperbolicPlaneQuad K) (Q.restrict W) (hyperbolicSumQuad K m')).trans
              (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl _)
                (hyperbolicSumSuccEquiv K m'))))
      exact ⟨m' + 1, W, hW_aniso, ⟨eTotal⟩⟩

end WittHyperbolicPlane

section WittCancellationAndExtension

/-- `S2-13` (Witt 1937 §I): Field-generic hyperplane reflection in `Q.IsometryEquiv Q`
over any `[Field K] [Invertible (2 : K)]` (`R3.2`). -/
def fieldQuadraticReflection {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) : Q.IsometryEquiv Q where
  toFun x := x - (QuadraticMap.polar Q x v / Q v) • v
  invFun x := x - (QuadraticMap.polar Q x v / Q v) • v
  left_inv x := by
    have hpol : QuadraticMap.polar Q (x - (QuadraticMap.polar Q x v / Q v) • v) v =
        -(QuadraticMap.polar Q x v) := by
      rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self,
        nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, mul_comm (2 : K) (Q v), ← _root_.mul_assoc,
        div_mul_cancel₀ _ hv]
      ring
    dsimp only
    rw [hpol, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]
  right_inv x := by
    have hpol : QuadraticMap.polar Q (x - (QuadraticMap.polar Q x v / Q v) • v) v =
        -(QuadraticMap.polar Q x v) := by
      rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self,
        nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, mul_comm (2 : K) (Q v), ← _root_.mul_assoc,
        div_mul_cancel₀ _ hv]
      ring
    dsimp only
    rw [hpol, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]
  map_add' x y := by
    rw [QuadraticMap.polar_add_left, add_div]
    module
  map_smul' c x := by
    simp only [RingHom.id_apply, QuadraticMap.polar_smul_left, smul_eq_mul]
    rw [mul_div_assoc]
    module
  map_app' x := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, QuadraticMap.map_smul Q,
      QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul]
    field_simp [hv]
    ring

/-- `S2-13` (Witt 1937 §I): Evaluation formula for `fieldQuadraticReflection`. -/
@[simp] theorem fieldQuadraticReflection_apply {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (v : V) (hv : Q v ≠ 0) (x : V) :
    fieldQuadraticReflection Q v hv x = x - (QuadraticMap.polar Q x v / Q v) • v :=
  rfl

/-- `S2-13` (Witt 1937 Satz 4 proof, p. 34): Field-generic reflection alignment: if
`Q x = Q y ≠ 0` over `[Field K] [Invertible (2 : K)]`, there exist at most two reflections
sending `y` to `x` (`R3.2`). -/
theorem field_reflection_alignment {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) (hxy : Q x = Q y) (hy : Q y ≠ 0) :
    ∃ f : Q.IsometryEquiv Q, f y = x := by
  by_cases h_eq : y = x
  · subst h_eq
    exact ⟨QuadraticMap.IsometryEquiv.refl Q, rfl⟩
  by_cases h_neg : y = -x
  · subst h_neg
    have hx : Q x ≠ 0 := by simpa using hy
    refine ⟨fieldQuadraticReflection Q x hx, ?_⟩
    rw [fieldQuadraticReflection_apply, QuadraticMap.polar_neg_left, QuadraticMap.polar_self,
      nsmul_eq_mul, Nat.cast_ofNat, neg_div, mul_div_cancel_right₀ _ hx, neg_smul,
      sub_neg_eq_add, two_smul K x]
    abel
  by_cases hsub : Q (y - x) ≠ 0
  · refine ⟨fieldQuadraticReflection Q (y - x) hsub, ?_⟩
    rw [fieldQuadraticReflection_apply]
    have hpol : QuadraticMap.polar Q y (y - x) = Q (y - x) := by
      have h1 : Q (y - x) = Q y + Q x - QuadraticMap.polar Q y x := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
          QuadraticMap.polar_neg_right]
        ring
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat,
        h1, hxy]
      ring
    rw [hpol, div_self hsub, one_smul, sub_sub_cancel]
  · have hsub0 : Q (y - x) = 0 := not_ne_iff.mp hsub
    have h4 : Q (y + x) + Q (y - x) = (4 : K) * Q y := by
      have hp : Q (y + x) = Q y + Q x + QuadraticMap.polar Q y x := QuadraticMap.map_add Q y x
      have hm : Q (y - x) = Q y + Q x - QuadraticMap.polar Q y x := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
          QuadraticMap.polar_neg_right]
        ring
      rw [hp, hm, hxy]
      ring
    have h2ne : (2 : K) ≠ 0 := fun h =>
      absurd (invOf_mul_self (2 : K)) (by rw [mul_eq_zero.mpr (Or.inr h)]; exact zero_ne_one)
    have h4ne : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by ring]
      exact mul_ne_zero h2ne h2ne
    have hadd : Q (y + x) ≠ 0 := by
      intro hadd0
      rw [hadd0, hsub0, add_zero] at h4
      exact (mul_ne_zero h4ne hy) h4.symm
    have hx : Q x ≠ 0 := by rwa [hxy]
    refine ⟨(fieldQuadraticReflection Q (y + x) hadd).trans (fieldQuadraticReflection Q x hx), ?_⟩
    change fieldQuadraticReflection Q x hx (fieldQuadraticReflection Q (y + x) hadd y) = x
    have h1 : fieldQuadraticReflection Q (y + x) hadd y = -x := by
      rw [fieldQuadraticReflection_apply]
      have hpol : QuadraticMap.polar Q y (y + x) = Q (y + x) := by
        rw [QuadraticMap.polar_add_right, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat,
          QuadraticMap.map_add Q, hxy]
        ring
      rw [hpol, div_self hadd, one_smul]
      abel
    rw [h1, fieldQuadraticReflection_apply, QuadraticMap.polar_neg_left, QuadraticMap.polar_self,
      nsmul_eq_mul, Nat.cast_ofNat, neg_div, mul_div_cancel_right₀ _ hx, neg_smul,
      sub_neg_eq_add, two_smul]
    abel

/-- `S2-13` (Witt 1937 Satz 4, p. 34): 1-dimensional Witt cancellation over any
`[Field K] [Invertible (2 : K)]`: if `(⟨a⟩ ⊥ Q₁) ≃_q (⟨a⟩ ⊥ Q₂)` with `a ≠ 0`, then
`Q₁ ≃_q Q₂` (`R3.2`). -/
theorem witt_cancellation_one_dim {K M₁ M₂ : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
    {a : K} (ha : a ≠ 0) (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂)
    (he : ((a • QuadraticMap.sq).prod Q₁).Equivalent ((a • QuadraticMap.sq).prod Q₂)) :
    Q₁.Equivalent Q₂ := by
  rcases he with ⟨e⟩
  let Qleft := (a • QuadraticMap.sq (R := K)).prod Q₁
  let Qright := (a • QuadraticMap.sq (R := K)).prod Q₂
  have hQ10_right : Qright (e (1, 0)) = a := by
    rw [e.map_app]
    simp
  have hQ10 : Qright (1, 0) = a := by simp [Qright]
  obtain ⟨r, hr⟩ := field_reflection_alignment Qright (1, 0) (e (1, 0))
    (hQ10.trans hQ10_right.symm) (by rwa [hQ10_right])
  let F : Qleft.IsometryEquiv Qright := e.trans r
  have hF10 : F (1, 0) = (1, 0) := hr
  have hFinv10 : F.symm (1, 0) = (1, 0) := by
    rw [← hF10, F.symm_apply_apply]
  have horth_right : ∀ m₁ : M₁, (F (0, m₁)).1 = 0 := by
    intro m₁
    have hpol1 : QuadraticMap.polar Qleft (1, 0) (0, m₁) = 0 := by
      simp only [Qleft, QuadraticMap.polar, QuadraticMap.prod_apply, smul_apply,
        QuadraticMap.sq_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
      rw [QuadraticMap.map_zero]
      ring
    have hpol2 : QuadraticMap.polar Qright (1, 0) (F (0, m₁)) = 0 := by
      rw [← hF10]
      change Qright (F (1, 0) + F (0, m₁)) - Qright (F (1, 0)) - Qright (F (0, m₁)) = 0
      rw [← map_add, F.map_app, F.map_app, F.map_app]
      exact hpol1
    have hpol3 : QuadraticMap.polar Qright (1, 0) (F (0, m₁)) =
        (2 : K) * a * (F (0, m₁)).1 := by
      simp only [Qright, QuadraticMap.polar, QuadraticMap.prod_apply, smul_apply,
        QuadraticMap.sq_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, zero_add]
      rw [QuadraticMap.map_zero]
      ring
    rw [hpol3] at hpol2
    have h2ne : (2 : K) ≠ 0 := fun h =>
      absurd (invOf_mul_self (2 : K)) (by rw [mul_eq_zero.mpr (Or.inr h)]; exact zero_ne_one)
    exact (mul_eq_zero.mp hpol2).resolve_left (mul_ne_zero h2ne ha)
  have horth_left : ∀ m₂ : M₂, (F.symm (0, m₂)).1 = 0 := by
    intro m₂
    have hpol1 : QuadraticMap.polar Qright (1, 0) (0, m₂) = 0 := by
      simp only [Qright, QuadraticMap.polar, QuadraticMap.prod_apply, smul_apply,
        QuadraticMap.sq_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
      rw [QuadraticMap.map_zero]
      ring
    have hpol2 : QuadraticMap.polar Qleft (1, 0) (F.symm (0, m₂)) = 0 := by
      rw [← hFinv10]
      change Qleft (F.symm (1, 0) + F.symm (0, m₂)) - Qleft (F.symm (1, 0)) -
        Qleft (F.symm (0, m₂)) = 0
      rw [← map_add, F.symm.map_app, F.symm.map_app, F.symm.map_app]
      exact hpol1
    have hpol3 : QuadraticMap.polar Qleft (1, 0) (F.symm (0, m₂)) =
        (2 : K) * a * (F.symm (0, m₂)).1 := by
      simp only [Qleft, QuadraticMap.polar, QuadraticMap.prod_apply, smul_apply,
        QuadraticMap.sq_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, zero_add]
      rw [QuadraticMap.map_zero]
      ring
    rw [hpol3] at hpol2
    have h2ne : (2 : K) ≠ 0 := fun h =>
      absurd (invOf_mul_self (2 : K)) (by rw [mul_eq_zero.mpr (Or.inr h)]; exact zero_ne_one)
    exact (mul_eq_zero.mp hpol2).resolve_left (mul_ne_zero h2ne ha)
  refine ⟨{
    toFun := fun m₁ => (F (0, m₁)).2
    invFun := fun m₂ => (F.symm (0, m₂)).2
    left_inv := fun m₁ => by
      have hF0 : (0, (F (0, m₁)).2) = F (0, m₁) := by
        ext
        · exact (horth_right m₁).symm
        · rfl
      dsimp only
      rw [hF0, F.symm_apply_apply]
    right_inv := fun m₂ => by
      have hF0 : (0, (F.symm (0, m₂)).2) = F.symm (0, m₂) := by
        ext
        · exact (horth_left m₂).symm
        · rfl
      dsimp only
      rw [hF0, F.apply_symm_apply]
    map_add' := fun x y => by
      have hadd : ((0 : K), x + y) = ((0 : K), x) + ((0 : K), y) := by ext <;> simp
      rw [hadd, map_add, Prod.snd_add]
    map_smul' := fun c x => by
      have hsmul : ((0 : K), c • x) = c • ((0 : K), x) := by ext <;> simp
      rw [hsmul, map_smul]
      rfl
    map_app' := fun m₁ => by
      have hF0 : (0, (F (0, m₁)).2) = F (0, m₁) := by
        ext
        · exact (horth_right m₁).symm
        · rfl
      calc
        Q₂ (F (0, m₁)).2 = Qright (0, (F (0, m₁)).2) := by simp [Qright]
        _ = Qright (F (0, m₁)) := by rw [hF0]
        _ = Qleft (0, m₁) := F.map_app (0, m₁)
        _ = Q₁ m₁ := by simp [Qleft] }⟩

private def weightedSumSquaresSuccEquiv {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin (n + 1) → K) :
    (QuadraticMap.weightedSumSquares K w).IsometryEquiv
      ((w 0 • QuadraticMap.sq).prod (QuadraticMap.weightedSumSquares K (w ∘ Fin.succ))) where
  toLinearEquiv :=
    { toFun := fun f => (f 0, fun i => f i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun f => by
        ext i
        refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]
      right_inv := fun p => by
        ext <;> simp [Fin.cons_zero, Fin.cons_succ]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_app' f := by
    simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply,
      QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul, Function.comp_apply]

private theorem witt_cancellation_weighted {K : Type*} [Field K] [Invertible (2 : K)] :
    ∀ {n : ℕ} (w : Fin n → Kˣ) {M₁ M₂ : Type*}
      [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
      (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂),
      ((QuadraticMap.weightedSumSquares K w).prod Q₁).Equivalent
        ((QuadraticMap.weightedSumSquares K w).prod Q₂) →
      Q₁.Equivalent Q₂
  | 0, w, M₁, M₂, _, _, _, _, Q₁, Q₂, ⟨e⟩ => by
    have he1 : Q₁.Equivalent ((QuadraticMap.weightedSumSquares K w).prod Q₁) :=
      ⟨{ toLinearEquiv :=
          { toFun := fun m => (0, m)
            invFun := fun p => p.2
            left_inv := fun _ => rfl
            right_inv := fun p => Prod.ext (Subsingleton.elim _ p.1) rfl
            map_add' := fun _ _ => Prod.ext (Subsingleton.elim _ _) rfl
            map_smul' := fun _ _ => Prod.ext (Subsingleton.elim _ _) rfl }
         map_app' := fun m => by simp }⟩
    have he2 : ((QuadraticMap.weightedSumSquares K w).prod Q₂).Equivalent Q₂ :=
      ⟨{ toLinearEquiv :=
          { toFun := fun p => p.2
            invFun := fun m => (0, m)
            left_inv := fun p => Prod.ext (Subsingleton.elim _ p.1) rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
         map_app' := fun p => by
           have h0 : p.1 = 0 := Subsingleton.elim _ _
           rw [QuadraticMap.prod_apply, h0, QuadraticMap.map_zero, zero_add] }⟩
    have hmid1 : Q₁.Equivalent ((QuadraticMap.weightedSumSquares K w).prod Q₁) := he1
    have hmid2 : ((QuadraticMap.weightedSumSquares K w).prod Q₁).Equivalent
        ((QuadraticMap.weightedSumSquares K w).prod Q₂) := ⟨e⟩
    exact hmid1.trans (hmid2.trans he2)
  | n + 1, w, M₁, M₂, _, _, _, _, Q₁, Q₂, he => by
    let eAssoc1 :
        (((w 0 : K) • QuadraticMap.sq).prod
          ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₁)).IsometryEquiv
        (((QuadraticMap.weightedSumSquares K w).prod Q₁)) :=
      { toLinearEquiv :=
          { toFun := fun ⟨x, f, m⟩ => (Fin.cons x f, m)
            invFun := fun ⟨g, m⟩ => (g 0, fun (i : Fin n) => g i.succ, m)
            left_inv := fun ⟨_, _, _⟩ => by ext <;> simp [Fin.cons_zero, Fin.cons_succ]
            right_inv := fun ⟨g, m⟩ => by
              refine Prod.ext (funext fun i => ?_) rfl
              refine Fin.cases ?_ ?_ i <;> simp
            map_add' := fun ⟨x₁, f₁, m₁⟩ ⟨x₂, f₂, m₂⟩ =>
              Prod.ext (funext fun i => Fin.cases rfl (fun _ => rfl) i) rfl
            map_smul' := fun c ⟨x, f, m⟩ =>
              Prod.ext (funext fun i => Fin.cases rfl (fun _ => rfl) i) rfl }
        map_app' := fun ⟨x, f, m⟩ => by
          simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply,
            QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ, Units.smul_def,
            smul_eq_mul, Fin.cons_zero, Fin.cons_succ]
          ring }
    let eAssoc2 :
        ((QuadraticMap.weightedSumSquares K w).prod Q₂).IsometryEquiv
        (((w 0 : K) • QuadraticMap.sq).prod
          ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₂)) :=
      { toLinearEquiv :=
          { toFun := fun ⟨g, m⟩ => (g 0, fun (i : Fin n) => g i.succ, m)
            invFun := fun ⟨x, f, m⟩ => (Fin.cons x f, m)
            left_inv := fun ⟨g, m⟩ => by
              refine Prod.ext (funext fun i => ?_) rfl
              refine Fin.cases ?_ ?_ i <;> simp
            right_inv := fun ⟨_, _, _⟩ => by ext <;> simp [Fin.cons_zero, Fin.cons_succ]
            map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
            map_smul' := fun _ ⟨_, _⟩ => rfl }
        map_app' := fun ⟨g, m⟩ => by
          simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply,
            QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ, Units.smul_def,
            smul_eq_mul]
          ring }
    have hA1 : (((w 0 : K) • QuadraticMap.sq).prod
        ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₁)).Equivalent
        ((QuadraticMap.weightedSumSquares K w).prod Q₁) := ⟨eAssoc1⟩
    have hA2 : ((QuadraticMap.weightedSumSquares K w).prod Q₂).Equivalent
        (((w 0 : K) • QuadraticMap.sq).prod
          ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₂)) := ⟨eAssoc2⟩
    have hmid :
        ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₁).Equivalent
          ((QuadraticMap.weightedSumSquares K (fun (i : Fin n) => (w i.succ : K))).prod Q₂) :=
      witt_cancellation_one_dim (w 0).ne_zero _ _ (hA1.trans (he.trans hA2))
    exact witt_cancellation_weighted (fun (i : Fin n) => w i.succ) Q₁ Q₂ hmid

/-- `S2-13` (Witt 1937 Satz 4, p. 34): **Witt Cancellation Theorem**: For any finite-dimensional
nondegenerate quadratic form `Q : QuadraticForm K V` over `[Field K] [Invertible (2 : K)]`,
`(Q ⊥ Q₁) ≃_q (Q ⊥ Q₂) → Q₁ ≃_q Q₂` (`R3.2`). -/
theorem witt_cancellation {K V M₁ M₂ : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂)
    (he : (Q.prod Q₁).Equivalent (Q.prod Q₂)) :
    Q₁.Equivalent Q₂ := by
  have hsep : (Q.associated (R := K)).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff).mpr hQ).1
  obtain ⟨w, ⟨eW⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hsep
  have h1 : ((QuadraticMap.weightedSumSquares K w).prod Q₁).Equivalent (Q.prod Q₁) :=
    ⟨QuadraticMap.IsometryEquiv.prod eW.symm (QuadraticMap.IsometryEquiv.refl Q₁)⟩
  have h2 : (Q.prod Q₂).Equivalent ((QuadraticMap.weightedSumSquares K w).prod Q₂) :=
    ⟨QuadraticMap.IsometryEquiv.prod eW (QuadraticMap.IsometryEquiv.refl Q₂)⟩
  exact witt_cancellation_weighted w Q₁ Q₂ (h1.trans (he.trans h2))

/-- `S2-13` (Witt 1937 Satz 4 Anmerkung, p. 34): **Witt Extension for Nondegenerate Subspaces**:
Every isometry `e : (Q.restrict S).IsometryEquiv (Q.restrict T)` between nondegenerate
subspaces `S, T ≤ V` of a finite-dimensional nondegenerate quadratic space `(V, Q)` over
`[Field K] [Invertible (2 : K)]` extends to a global isometry `F : Q.IsometryEquiv Q` (`R3.2`). -/
theorem witt_extension_nondegenerate {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V)
    {S T : Subspace K V}
    (hS : (Q.restrict S).Nondegenerate) (hT : (Q.restrict T).Nondegenerate)
    (e : (Q.restrict S).IsometryEquiv (Q.restrict T)) :
    ∃ F : Q.IsometryEquiv Q, ∀ s : S, F s.1 = (e s).1 := by
  have hBS : (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) S).Nondegenerate := by
    have h1 : LinearMap.BilinForm.restrict (QuadraticMap.associated Q) S =
        QuadraticMap.associated (Q.restrict S) := rfl
    change LinearMap.Nondegenerate (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) S)
    rw [h1]
    exact (QuadraticMap.nondegenerate_associated_iff (Q := Q.restrict S)).mpr hS
  have hBT : (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) T).Nondegenerate := by
    have h1 : LinearMap.BilinForm.restrict (QuadraticMap.associated Q) T =
        QuadraticMap.associated (Q.restrict T) := rfl
    change LinearMap.Nondegenerate (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) T)
    rw [h1]
    exact (QuadraticMap.nondegenerate_associated_iff (Q := Q.restrict T)).mpr hT
  have hB_refl : (QuadraticMap.associated (R := K) Q).IsRefl := fun x y h => by
    have hs := QuadraticMap.associated_isSymm K Q y x
    dsimp only [QuadraticMap.associated] at hs h ⊢
    rwa [hs]
  have hcomplS := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB_refl hBS
  have hcomplT := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB_refl hBT
  let eS := isometryEquivProdOfIsCompl Q hcomplS (fun _ hs _ ht => ht _ hs)
  let eT := isometryEquivProdOfIsCompl Q hcomplT (fun _ hs _ ht => ht _ hs)
  have heProd : ((Q.restrict S).prod (Q.restrict (LinearMap.BilinForm.orthogonal Q.associated S))).Equivalent
      ((Q.restrict S).prod (Q.restrict (LinearMap.BilinForm.orthogonal Q.associated T))) :=
    ⟨eS.symm.trans (eT.trans (QuadraticMap.IsometryEquiv.prod e.symm (QuadraticMap.IsometryEquiv.refl _)))⟩
  obtain ⟨ePerp⟩ := witt_cancellation (Q.restrict S) hS _ _ heProd
  let F : Q.IsometryEquiv Q :=
    eS.trans ((QuadraticMap.IsometryEquiv.prod e ePerp).trans eT.symm)
  refine ⟨F, fun s => ?_⟩
  have hs_map : eS s.1 = (s, 0) := by
    apply (Submodule.prodEquivOfIsCompl S (LinearMap.BilinForm.orthogonal Q.associated S) hcomplS).injective
    change (Submodule.prodEquivOfIsCompl S (LinearMap.BilinForm.orthogonal Q.associated S) hcomplS)
        ((Submodule.prodEquivOfIsCompl S (LinearMap.BilinForm.orthogonal Q.associated S) hcomplS).symm s.1) =
      (s.1 : V) + 0
    rw [LinearEquiv.apply_symm_apply, add_zero]
  have heT_map : eT (e s).1 = (e s, 0) := by
    apply (Submodule.prodEquivOfIsCompl T (LinearMap.BilinForm.orthogonal Q.associated T) hcomplT).injective
    change (Submodule.prodEquivOfIsCompl T (LinearMap.BilinForm.orthogonal Q.associated T) hcomplT)
        ((Submodule.prodEquivOfIsCompl T (LinearMap.BilinForm.orthogonal Q.associated T) hcomplT).symm (e s).1) =
      ((e s).1 : V) + 0
    rw [LinearEquiv.apply_symm_apply, add_zero]
  change eT.symm ((QuadraticMap.IsometryEquiv.prod e ePerp) (eS s.1)) = (e s).1
  rw [hs_map]
  change eT.symm (e s, ePerp 0) = (e s).1
  rw [map_zero, ← heT_map, eT.symm_apply_apply]

end WittCancellationAndExtension

section WittCliffordGradedTensor

open scoped TensorProduct

/-- `S2-13` (Witt 1937 §II p. 36; Atiyah–Bott–Shapiro 1964 §1 Prop. (1.6) p. 5):
Coordinate-free Koszul `ℤ/2`-graded tensor decomposition
`Cl(Q₁ ⊥ Q₂) ≃ₐ[R] Cl(Q₁) ᵍ⊗[R] Cl(Q₂)` via `CliffordAlgebra.prodEquiv` (`R3.3`). -/
def witt_clifford_graded_tensor_law {R M₁ M₂ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R]
      (CliffordAlgebra.evenOdd Q₁ ᵍ⊗[R] CliffordAlgebra.evenOdd Q₂) :=
  CliffordAlgebra.prodEquiv Q₁ Q₂

/-- `S2-13` (Witt 1937 Satz 8 p. 37; ABS 1964 §1 Prop. (1.6)): Any Witt orthogonal
decomposition `Q ≃_q Q_aniso ⊥ ℍ^m` induces an algebra equivalence
`CliffordAlgebra Q ≃ₐ[K] (evenOdd Q_aniso ᵍ⊗[K] evenOdd (hyperbolicSumQuad K m))` (`R3.3`). -/
def witt_decomposition_clifford_equiv {K V W : Type*} [CommRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K V} {QW : QuadraticForm K W} {m : ℕ}
    (e : Q.IsometryEquiv (QW.prod (hyperbolicSumQuad K m))) :
    CliffordAlgebra Q ≃ₐ[K]
      (CliffordAlgebra.evenOdd QW ᵍ⊗[K] CliffordAlgebra.evenOdd (hyperbolicSumQuad K m)) :=
  (CliffordAlgebra.equivOfIsometry e).trans (CliffordAlgebra.prodEquiv QW (hyperbolicSumQuad K m))

end WittCliffordGradedTensor

end WittPrimary

/-!
## Section 4 (`S2-14`): Riesz (1946/1958) Grade Split, Involutions, Conjugation, & Minimal Left Ideals
-/

section RieszPrimary

section RieszGradesAndInvolutions

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem exteriorPower_mul_ι_comm (k : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ⋀[R]^k M) (m : M) :
    x * ExteriorAlgebra.ι R m = (-1 : R) ^ k • (ExteriorAlgebra.ι R m * x) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp only [pow_zero, one_smul, Algebra.commutes]
  | add x₁ x₂ _ _ _ ih1 ih2 =>
    rw [add_mul, mul_add, ih1, ih2, smul_add]
  | mem_mul a ha i x_i _ ih =>
    rcases LinearMap.mem_range.mp ha with ⟨v, rfl⟩
    calc
      (ExteriorAlgebra.ι R v * x_i) * ExteriorAlgebra.ι R m
          = ExteriorAlgebra.ι R v * (x_i * ExteriorAlgebra.ι R m) := _root_.mul_assoc _ _ _
      _ = ExteriorAlgebra.ι R v * ((-1 : R) ^ i • (ExteriorAlgebra.ι R m * x_i)) := by rw [ih]
      _ = (-1 : R) ^ i • ((ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R m) * x_i) := by
          rw [mul_smul_comm, ← _root_.mul_assoc]
      _ = (-1 : R) ^ i • ((-(ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R v)) * x_i) := by
          rw [show ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R m =
            -(ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R v) from
            eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v m)]
      _ = (-1 : R) ^ i.succ • (ExteriorAlgebra.ι R m * (ExteriorAlgebra.ι R v * x_i)) := by
          rw [neg_mul, _root_.mul_assoc, smul_neg, ← neg_smul, pow_succ', neg_one_mul]

private theorem exteriorPower_involute (k : ℕ) (y : ExteriorAlgebra R M)
    (hy : y ∈ ⋀[R]^k M) :
    CliffordAlgebra.involute y = (-1 : R) ^ k • y := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp [CliffordAlgebra.involute.commutes]
  | add y₁ y₂ _ _ _ ih1 ih2 =>
    rw [map_add, ih1, ih2, smul_add]
  | mem_mul a ha j x _ ih =>
    rcases LinearMap.mem_range.mp ha with ⟨m, rfl⟩
    rw [map_mul, CliffordAlgebra.involute_ι, ih, neg_mul, mul_smul_comm]
    change -((-1 : R) ^ j • (ExteriorAlgebra.ι R m * x)) = (-1 : R) ^ j.succ • (ExteriorAlgebra.ι R m * x)
    rw [← neg_smul, pow_succ', neg_one_mul]

/-- `S2-14` (Riesz 1958 Ch. I §1.4 pp. 13–14): General-`k` reversion sign law on exterior
powers: for any `y ∈ ⋀[R]^k M`, `CliffordAlgebra.reverse y = (-1)^(k*(k-1)/2) • y`
(`+y` for `k ≡ 0, 1 (mod 4)`, `-y` for `k ≡ 2, 3 (mod 4)`). -/
theorem exteriorPower_reverse (k : ℕ) (y : ExteriorAlgebra R M)
    (hy : y ∈ ⋀[R]^k M) :
    CliffordAlgebra.reverse y = (-1 : R) ^ (k * (k - 1) / 2) • y := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp [CliffordAlgebra.reverse.commutes]
  | add y₁ y₂ _ _ _ ih1 ih2 =>
    rw [map_add, ih1, ih2, smul_add]
  | mem_mul a ha j x hx ih =>
    rcases LinearMap.mem_range.mp ha with ⟨m, rfl⟩
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, ih, smul_mul_assoc,
      exteriorPower_mul_ι_comm j x hx m, smul_smul, ← pow_add]
    congr 1
    have hpow : j * (j - 1) / 2 + j = (j + 1) * j / 2 := by
      have hmul : (j + 1) * j = j * (j - 1) + 2 * j := by
        cases j with
        | zero => simp
        | succ n => simp only [Nat.add_sub_cancel]; ring
      rw [hmul, Nat.add_mul_div_left _ _ (by norm_num), add_comm]
    have hpow2 : (j + 1) * j / 2 = j.succ * (j.succ - 1) / 2 := by
      simp [Nat.succ_eq_add_one]
    rw [hpow, hpow2]

section InvertibleTwoRiesz

variable [Invertible (2 : R)]

/-- `S2-14` (Riesz 1958 Ch. I §1.4 pp. 10–14): Grade resolution of `CliffordAlgebra Q` via
`equivExterior` and `cliffordGradeProj` (`idem`, `orthog`, and finite-dim resolution of
identity over `ℝ`). -/
theorem riesz_grade_resolution {M_real : Type*} [AddCommGroup M_real] [Module ℝ M_real]
    [Module.Finite ℝ M_real] (Q : QuadraticForm ℝ M_real) :
    (∀ k x, cliffordGradeProj Q k (cliffordGradeProj Q k x) = cliffordGradeProj Q k x) ∧
      (∀ j k x, j ≠ k → cliffordGradeProj Q j (cliffordGradeProj Q k x) = 0) ∧
      (∀ x : CliffordAlgebra Q,
        (∑ k ∈ Finset.range (Module.finrank ℝ M_real + 1), cliffordGradeProj Q k x) = x) := by
  exact ⟨cliffordGradeProj_idem Q, fun j k x hjk => cliffordGradeProj_orthog Q hjk x,
    cliffordGradeProj_sum_range_apply Q⟩

/-- `S2-14` (Riesz 1958 Ch. I §1.4 pp. 13–14): General-`k` reversion law in `CliffordAlgebra Q`:
`reverse (cliffordGradeProj Q k x) = (-1)^(k*(k-1)/2) • cliffordGradeProj Q k x`. Note that
Riesz §1.4 writes `ū` for this reversion antiautomorphism, whereas ABS §1 Def. (1.8)
writes `x^t` for reversion and `x̄` for Clifford conjugation (`star`). -/
theorem cliffordGradeProj_reverse (Q : QuadraticForm R M) (k : ℕ) (x : CliffordAlgebra Q) :
    CliffordAlgebra.reverse (cliffordGradeProj Q k x) =
      (-1 : R) ^ (k * (k - 1) / 2) • cliffordGradeProj Q k x := by
  apply (CliffordAlgebra.equivExterior Q).injective
  rw [equivExterior_reverse, map_smul]
  change CliffordAlgebra.reverse
      (CliffordAlgebra.equivExterior Q
        ((CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x)))) =
    (-1 : R) ^ (k * (k - 1) / 2) •
      (CliffordAlgebra.equivExterior Q
        ((CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x))))
  rw [LinearEquiv.apply_symm_apply]
  exact exteriorPower_reverse k _ (exteriorGradeProj_mem R M k _)

/-- Reversion commutes with homogeneous-grade projection up to the standard
grade sign. This is the input-side counterpart of
`cliffordGradeProj_reverse`. -/
theorem cliffordGradeProj_reverse_input (Q : QuadraticForm R M) (k : ℕ)
    (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (CliffordAlgebra.reverse x) =
      (-1 : R) ^ (k * (k - 1) / 2) • cliffordGradeProj Q k x := by
  let y : ExteriorAlgebra R M := CliffordAlgebra.equivExterior Q x
  have hExt : exteriorGradeProj R M k (CliffordAlgebra.reverse y) =
      (-1 : R) ^ (k * (k - 1) / 2) • exteriorGradeProj R M k y := by
    induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
    | zero => simp
    | add a b ha hb => simp [ha, hb, smul_add]
    | homogeneous hm =>
        rename_i i
        rcases hm with ⟨a, ha⟩
        by_cases hik : i = k
        · subst i
          rw [exteriorPower_reverse k a ha, map_smul,
            exteriorGradeProj_of_mem ha]
        · rw [exteriorPower_reverse i a ha, map_smul,
            exteriorGradeProj_of_mem_ne hik ha]
          simp
  change (CliffordAlgebra.equivExterior Q).symm
      (exteriorGradeProj R M k
        (CliffordAlgebra.equivExterior Q (CliffordAlgebra.reverse x))) =
    (-1 : R) ^ (k * (k - 1) / 2) •
      (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x))
  rw [equivExterior_reverse]
  calc
    (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R M k (CliffordAlgebra.reverse y)) =
        (CliffordAlgebra.equivExterior Q).symm
          ((-1 : R) ^ (k * (k - 1) / 2) • exteriorGradeProj R M k y) :=
      congrArg (CliffordAlgebra.equivExterior Q).symm hExt
    _ = (-1 : R) ^ (k * (k - 1) / 2) •
        (CliffordAlgebra.equivExterior Q).symm (exteriorGradeProj R M k y) := by
      exact map_smul _ _ _

/-- Grade projection commutes with grade involution up to its homogeneous
grade sign. This is the input-side form of the exterior-power involution law. -/
theorem cliffordGradeProj_involute_input (Q : QuadraticForm R M) (k : ℕ)
    (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (CliffordAlgebra.involute x) =
      (-1 : R) ^ k • cliffordGradeProj Q k x := by
  change (CliffordAlgebra.equivExterior Q).symm
      (exteriorGradeProj R M k
        (CliffordAlgebra.equivExterior Q (CliffordAlgebra.involute x))) =
    (-1 : R) ^ k •
      (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x))
  rw [equivExterior_involute]
  calc
    (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R M k
          (CliffordAlgebra.involute (CliffordAlgebra.equivExterior Q x))) =
        (CliffordAlgebra.equivExterior Q).symm
          ((-1 : R) ^ k • exteriorGradeProj R M k
            (CliffordAlgebra.equivExterior Q x)) :=
      congrArg (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj_involute k _)
    _ = (-1 : R) ^ k •
        (CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x)) := by
      exact map_smul _ _ _

/-- Clifford conjugation acts on the input of homogeneous-grade projection
with the standard sign `(-1)^(k(k+1)/2)`. -/
theorem cliffordGradeProj_star_input (Q : QuadraticForm R M) (k : ℕ)
    (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (star x) =
      (-1 : R) ^ (k * (k + 1) / 2) • cliffordGradeProj Q k x := by
  rw [CliffordAlgebra.star_def, cliffordGradeProj_reverse_input,
    cliffordGradeProj_involute_input, smul_smul, ← pow_add]
  congr 1
  have hpow : k * (k - 1) / 2 + k = (k + 1) * k / 2 := by
    have hmul : (k + 1) * k = k * (k - 1) + 2 * k := by
      cases k with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel]; ring
    rw [hmul, Nat.add_mul_div_left _ _ (by norm_num), add_comm]
  have hpow' : (k + 1) * k / 2 = k * (k + 1) / 2 := by
    rw [Nat.mul_comm]
  rw [hpow, hpow']

/-- `S2-14` (Riesz 1958 Ch. I §1.4; ABS §1 Def. (1.8)): General-`k` Clifford conjugation
(`star x = reverse (involute x)`) law:
`star (cliffordGradeProj Q k x) = (-1)^(k*(k+1)/2) • cliffordGradeProj Q k x`. -/
theorem cliffordGradeProj_star (Q : QuadraticForm R M) (k : ℕ) (x : CliffordAlgebra Q) :
    star (cliffordGradeProj Q k x) =
      (-1 : R) ^ (k * (k + 1) / 2) • cliffordGradeProj Q k x := by
  have h_inv : CliffordAlgebra.involute (cliffordGradeProj Q k x) =
      (-1 : R) ^ k • cliffordGradeProj Q k x := by
    apply (CliffordAlgebra.equivExterior Q).injective
    rw [equivExterior_involute, map_smul]
    change CliffordAlgebra.involute (CliffordAlgebra.equivExterior Q
        ((CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x)))) =
      (-1 : R) ^ k • (CliffordAlgebra.equivExterior Q
        ((CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x))))
    rw [LinearEquiv.apply_symm_apply]
    exact exteriorPower_involute k _ (exteriorGradeProj_mem R M k _)
  rw [CliffordAlgebra.star_def, h_inv, map_smul, cliffordGradeProj_reverse, smul_smul, ← pow_add]
  congr 1
  have hpow : k + k * (k - 1) / 2 = k * (k + 1) / 2 := by
    have hmul : k * (k + 1) = 2 * k + k * (k - 1) := by
      cases k with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel]; ring
    rw [hmul, Nat.mul_add_div (by norm_num)]
  rw [hpow]

end InvertibleTwoRiesz

/-- `S2-14` (Riesz 1958 Ch. I §1.4 pp. 13–14): Klein-4 involution relations for
`involute`, `reverse`, and `star`, together with their `O(Q)` equivariance under
`CliffordAlgebra.equivOfIsometry` (`R3.2`). -/
theorem riesz_involutions_klein_four_and_equivariance
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (e : Q₁.IsometryEquiv Q₂) :
    (∀ x : CliffordAlgebra Q₁, CliffordAlgebra.involute (CliffordAlgebra.involute x) = x) ∧
      (∀ x : CliffordAlgebra Q₁, CliffordAlgebra.reverse (CliffordAlgebra.reverse x) = x) ∧
      (∀ x : CliffordAlgebra Q₁,
        star x = CliffordAlgebra.reverse (CliffordAlgebra.involute x) ∧
          star x = CliffordAlgebra.involute (CliffordAlgebra.reverse x) ∧
          star (star x) = x) ∧
      (∀ x : CliffordAlgebra Q₁,
        CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.involute x) =
          CliffordAlgebra.involute (CliffordAlgebra.equivOfIsometry e x)) ∧
      (∀ x : CliffordAlgebra Q₁,
        CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.reverse x) =
          CliffordAlgebra.reverse (CliffordAlgebra.equivOfIsometry e x)) ∧
      (∀ x : CliffordAlgebra Q₁,
        CliffordAlgebra.equivOfIsometry e (star x) =
          star (CliffordAlgebra.equivOfIsometry e x)) := by
  refine ⟨CliffordAlgebra.involute_involute, CliffordAlgebra.reverse_reverse,
    fun x => ⟨CliffordAlgebra.star_def x, CliffordAlgebra.star_def' x, star_star x⟩,
    fun x => (involute_equivOfIsometry e x).symm,
    fun x => (reverse_equivOfIsometry e x).symm,
    fun x => (star_equivOfIsometry e x).symm⟩

end RieszGradesAndInvolutions

section RieszCentralIdempotentsAndSpinorIdeals

/-- `S2-14` (Riesz 1958 Ch. I §1.5 pp. 16–18): Odd-dimension central idempotents
`E± := (1/2) • (1 ± P)` constructed from a central element `P` satisfying `P * P = 1`. -/
theorem riesz1958_odd_central_idempotents {A : Type*} [Ring A] [Algebra ℝ A]
    (P : A) (hPsq : P * P = 1) (hPcent : ∀ a : A, P * a = a * P) :
    let Eplus : A := (1 / 2 : ℝ) • (1 + P)
    let Eminus : A := (1 / 2 : ℝ) • (1 - P)
    Eplus * Eplus = Eplus ∧ Eminus * Eminus = Eminus ∧
      Eplus * Eminus = 0 ∧ Eplus + Eminus = 1 ∧
      (∀ a : A, Eplus * a = a * Eplus ∧ Eminus * a = a * Eminus) := by
  intro Eplus Eminus
  have hp_sq : (1 + P) * (1 + P) = (2 : ℝ) • (1 + P) := by
    calc
      (1 + P) * (1 + P) = 1 + P + P + P * P := by noncomm_ring
      _ = 1 + P + P + 1 := by rw [hPsq]
      _ = (2 : ℝ) • (1 + P) := by rw [two_smul]; abel
  have hm_sq : (1 - P) * (1 - P) = (2 : ℝ) • (1 - P) := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + 1 := by rw [hPsq]
      _ = (2 : ℝ) • (1 - P) := by rw [two_smul]; abel
  have hEp : Eplus * Eplus = Eplus := by
    dsimp [Eplus]
    rw [smul_mul_smul_comm, hp_sq, smul_smul]
    norm_num
  have hEm : Eminus * Eminus = Eminus := by
    dsimp [Eminus]
    rw [smul_mul_smul_comm, hm_sq, smul_smul]
    norm_num
  have horth : Eplus * Eminus = 0 := by
    dsimp [Eplus, Eminus]
    rw [smul_mul_smul_comm]
    have h0 : (1 + P) * (1 - P) = 0 := by
      calc
        (1 + P) * (1 - P) = 1 - P + P - P * P := by noncomm_ring
        _ = 1 - P + P - 1 := by rw [hPsq]
        _ = 0 := by abel
    rw [h0, smul_zero]
  have hsum : Eplus + Eminus = 1 := by
    dsimp [Eplus, Eminus]
    rw [← smul_add, show (1 + P) + (1 - P) = (2 : ℝ) • (1 : A) by rw [two_smul]; abel,
      smul_smul]
    norm_num
  refine ⟨hEp, hEm, horth, hsum, fun a => ⟨?_, ?_⟩⟩
  · dsimp [Eplus]
    rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, _root_.one_mul, _root_.mul_one, hPcent a]
  · dsimp [Eminus]
    rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, _root_.one_mul, _root_.mul_one, hPcent a]

/-- `S2-14` (Riesz 1958 Preface / 1993 Ch. VI; Sushch 2015 eqs. (21)–(24)): Spinor carrier
realized as the left ideal `A · f` generated by an element `f : A` (specifically `{x | x * f = x}`
when `IsIdempotentElem f`). -/
def RieszLeftIdeal (A : Type*) [Ring A] (f : A) : Submodule A A :=
  Submodule.span A {f}

/-- `S2-14` (Riesz 1958 Preface / 1993 Ch. VI): Predicate asserting that a left ideal
`I : Submodule A A` is genuinely minimal (`I ≠ ⊥` and every sub-ideal `J ≤ I` is `⊥` or `I`). -/
def IsMinimalLeftIdeal {A : Type*} [Ring A] (I : Submodule A A) : Prop :=
  I ≠ ⊥ ∧ ∀ J : Submodule A A, J ≤ I → J = ⊥ ∨ J = I

/-- `S2-14` (Riesz 1958 Preface / 1993 Ch. VI): Characterization of membership in
`RieszLeftIdeal A f` for an idempotent `f` as `x * f = x`. -/
theorem mem_rieszLeftIdeal_iff_mul_eq {A : Type*} [Ring A] {f : A}
    (hf : IsIdempotentElem f) (x : A) :
    x ∈ RieszLeftIdeal A f ↔ x * f = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hf
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul, hy, hz]
    | smul a y _ hy =>
      change (a * y) * f = a * y
      rw [_root_.mul_assoc, hy]
  · intro hx
    rw [← hx]
    exact Submodule.smul_mem _ x (Submodule.subset_span (Set.mem_singleton f))

/-- `S2-14` (Riesz 1958 Preface / 1993 Ch. VI; Sushch 2015 eqs. (21)–(24); ABS Table 1):
In split `Cl(1,1)`, the primitive idempotent `f₁₁ := (1/2 : ℝ) • (1 + ι q11 (1, 0))` generates
a 2-dimensional **genuinely minimal left ideal** `RieszLeftIdeal (CliffordAlgebra q11) f₁₁`
(`IsMinimalLeftIdeal`), certified via `Cl11Matrix.cl11EquivMat : Cl(1,1) ≃ₐ M₂(ℝ)`. -/
theorem cl11_riesz_minimal_left_ideal_witness :
    let f₁₁ : CliffordAlgebra q11 := (1 / 2 : ℝ) • (1 + CliffordAlgebra.ι q11 (1, 0))
    let I := RieszLeftIdeal (CliffordAlgebra q11) f₁₁
    IsIdempotentElem f₁₁ ∧ f₁₁ ≠ 0 ∧ IsMinimalLeftIdeal I ∧
      Module.finrank ℝ (I.restrictScalars ℝ) = 2 := by
  intro f₁₁ I
  have he1sq : CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (1, 0) = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, show q11 (1, 0) = 1 by simp [q11], map_one]
  have hf_idem : IsIdempotentElem f₁₁ := by
    change f₁₁ * f₁₁ = f₁₁
    dsimp [f₁₁]
    rw [smul_mul_smul_comm]
    have hsq : (1 + CliffordAlgebra.ι q11 (1, 0)) * (1 + CliffordAlgebra.ι q11 (1, 0)) =
        (2 : ℝ) • (1 + CliffordAlgebra.ι q11 (1, 0)) := by
      calc
        _ = 1 + CliffordAlgebra.ι q11 (1, 0) + CliffordAlgebra.ι q11 (1, 0) +
              CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (1, 0) := by noncomm_ring
        _ = 1 + CliffordAlgebra.ι q11 (1, 0) + CliffordAlgebra.ι q11 (1, 0) + 1 := by rw [he1sq]
        _ = (2 : ℝ) • (1 + CliffordAlgebra.ι q11 (1, 0)) := by rw [two_smul]; abel
    rw [hsq, smul_smul]
    norm_num
  have hf_mat : cl11EquivMat f₁₁ = !![(1 : ℝ), 0; 0, 0] := by
    dsimp [f₁₁]
    rw [map_smul, map_add, map_one, cl11EquivMat_iota_pos]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Eplus]; try norm_num)
  have hf_ne : f₁₁ ≠ 0 := by
    intro h0
    have hm := congrArg cl11EquivMat h0
    rw [hf_mat, map_zero] at hm
    have h00 := congrArg (fun M : Mat2 => M 0 0) hm
    norm_num at h00
  have hI_min : IsMinimalLeftIdeal I := by
    refine ⟨?_, fun J hJI => ?_⟩
    · intro hbot
      have hmem : f₁₁ ∈ (⊥ : Submodule (CliffordAlgebra q11) (CliffordAlgebra q11)) := by
        rw [← hbot]
        exact Submodule.subset_span (Set.mem_singleton f₁₁)
      rw [Submodule.mem_bot] at hmem
      exact hf_ne hmem
    · by_cases hJ : J = ⊥
      · left; exact hJ
      · right
        apply le_antisymm hJI
        change Submodule.span (CliffordAlgebra q11) {f₁₁} ≤ J
        rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨x, hxJ, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
        have hxI : x ∈ I := hJI hxJ
        have hxf : x * f₁₁ = x := (mem_rieszLeftIdeal_iff_mul_eq hf_idem x).mp hxI
        let M := cl11EquivMat x
        have hMf : M * !![(1 : ℝ), 0; 0, 0] = M := by
          rw [← hf_mat, ← map_mul, hxf]
        have hMcol1 : M 0 1 = 0 ∧ M 1 1 = 0 := by
          have h01 := congrArg (fun A : Mat2 => A 0 1) hMf
          have h11 := congrArg (fun A : Mat2 => A 1 1) hMf
          simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h11
          exact ⟨h01.symm, h11.symm⟩
        have hMne : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
          by_contra hzero
          push Not at hzero
          have hM0 : M = 0 := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [hzero.1, hzero.2, hMcol1.1, hMcol1.2]
          exact hxne (cl11EquivMat.injective (hM0.trans (map_zero cl11EquivMat).symm))
        by_cases h00 : M 0 0 ≠ 0
        · let A : Mat2 := !![(M 0 0)⁻¹, 0; 0, 0]
          have hAM : A * M = !![(1 : ℝ), 0; 0, 0] := by
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [A, Matrix.mul_apply, Fin.sum_univ_two, hMcol1.1, hMcol1.2, inv_mul_cancel₀ h00]
          have ha : cl11EquivMat.symm A * x = f₁₁ := by
            apply cl11EquivMat.injective
            rw [map_mul, AlgEquiv.apply_symm_apply, hf_mat]
            exact hAM
          rw [← ha]
          exact Submodule.smul_mem J (cl11EquivMat.symm A) hxJ
        · have h10 : M 1 0 ≠ 0 := hMne.resolve_left h00
          let A : Mat2 := !![0, (M 1 0)⁻¹; 0, 0]
          have hAM : A * M = !![(1 : ℝ), 0; 0, 0] := by
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [A, Matrix.mul_apply, Fin.sum_univ_two, hMcol1.1, hMcol1.2, inv_mul_cancel₀ h10]
          have ha : cl11EquivMat.symm A * x = f₁₁ := by
            apply cl11EquivMat.injective
            rw [map_mul, AlgEquiv.apply_symm_apply, hf_mat]
            exact hAM
          rw [← ha]
          exact Submodule.smul_mem J (cl11EquivMat.symm A) hxJ
  have hfin : Module.finrank ℝ (I.restrictScalars ℝ) = 2 := by
    let g : (ℝ × ℝ) →ₗ[ℝ] (I.restrictScalars ℝ) :=
      { toFun := fun p => ⟨cl11EquivMat.symm !![p.1, 0; p.2, 0], by
          change cl11EquivMat.symm !![p.1, 0; p.2, 0] ∈ I
          rw [mem_rieszLeftIdeal_iff_mul_eq hf_idem]
          apply cl11EquivMat.injective
          rw [map_mul, AlgEquiv.apply_symm_apply, hf_mat]
          ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
        map_add' := fun p q => by
          apply Subtype.ext
          change cl11EquivMat.symm _ = cl11EquivMat.symm _ + cl11EquivMat.symm _
          rw [← map_add]
          congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
        map_smul' := fun r p => by
          apply Subtype.ext
          change cl11EquivMat.symm _ = r • cl11EquivMat.symm _
          rw [← map_smul]
          congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp }
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      have hp' := congrArg (fun z : I.restrictScalars ℝ => cl11EquivMat z.1) hp
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk, AlgEquiv.apply_symm_apply, ZeroMemClass.coe_zero,
        map_zero] at hp'
      have h00 := congrArg (fun M : Mat2 => M 0 0) hp'
      have h10 := congrArg (fun M : Mat2 => M 1 0) hp'
      ext
      · simpa using h00
      · simpa using h10
    have hgsurj : Function.Surjective g := by
      intro ⟨x, hx⟩
      have hxf : x * f₁₁ = x := (mem_rieszLeftIdeal_iff_mul_eq hf_idem x).mp hx
      let M := cl11EquivMat x
      have hMf : M * !![(1 : ℝ), 0; 0, 0] = M := by
        rw [← hf_mat, ← map_mul, hxf]
      have hMcol1 : M 0 1 = 0 ∧ M 1 1 = 0 := by
        have h01 := congrArg (fun A : Mat2 => A 0 1) hMf
        have h11 := congrArg (fun A : Mat2 => A 1 1) hMf
        simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h11
        exact ⟨h01.symm, h11.symm⟩
      refine ⟨(M 0 0, M 1 0), Subtype.ext ?_⟩
      apply cl11EquivMat.injective
      change cl11EquivMat (cl11EquivMat.symm !![M 0 0, 0; M 1 0, 0]) = M
      rw [AlgEquiv.apply_symm_apply]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M, hMcol1.1, hMcol1.2]
    let e : (ℝ × ℝ) ≃ₗ[ℝ] (I.restrictScalars ℝ) := LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩
    rw [← LinearEquiv.finrank_eq e, Module.finrank_prod, Module.finrank_self]
  exact ⟨hf_idem, hf_ne, hI_min, hfin⟩

/-- `S2-14` (Riesz 1958 Ch. I §1.6 p. 22; ABS Table 1): Quaternionic division-algebra
contrast in `Cl(0,2)`: `CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)) ≃ₐ[ℝ]
ℍ[ℝ, -1, 0, -1]`, a 4-dimensional division ring where the only minimal left ideal is `⊤`
(no nontrivial idempotent split `Cl · f`), contrasting with split `Cl(1,1) ≃ₐ M₂(ℝ)`. -/
theorem cl02_quaternion_division_spinor_contrast :
    let q02 := CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)
    Nonempty (CliffordAlgebra q02 ≃ₐ[ℝ] QuaternionAlgebra ℝ (-1 : ℝ) 0 (-1 : ℝ)) ∧
      IsMinimalLeftIdeal (⊤ : Submodule (CliffordAlgebra q02) (CliffordAlgebra q02)) ∧
      (∀ f : CliffordAlgebra q02, IsIdempotentElem f → f = 0 ∨ f = 1) := by
  intro q02
  let e : CliffordAlgebra q02 ≃ₐ[ℝ] QuaternionAlgebra ℝ (-1 : ℝ) 0 (-1 : ℝ) :=
    CliffordAlgebraQuaternion.equiv
  have hunit : ∀ q : CliffordAlgebra q02, q ≠ 0 → IsUnit q := by
    intro q hq
    have heq : e q ≠ 0 := fun h0 => hq (e.injective (h0.trans (map_zero e).symm))
    let qh := e q
    let norm := qh.re ^ 2 + qh.imI ^ 2 + qh.imJ ^ 2 + qh.imK ^ 2
    have hns : norm ≠ 0 := by
      intro h0
      have hre : qh.re = 0 ∧ qh.imI = 0 ∧ qh.imJ = 0 ∧ qh.imK = 0 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          nlinarith [sq_nonneg qh.re, sq_nonneg qh.imI, sq_nonneg qh.imJ, sq_nonneg qh.imK]
      apply heq
      dsimp only [qh] at hre
      ext <;> simp [hre.1, hre.2.1, hre.2.2.1, hre.2.2.2]
    let qinv : QuaternionAlgebra ℝ (-1 : ℝ) 0 (-1 : ℝ) := norm⁻¹ • star qh
    have hns' : qh.re ^ 2 + qh.imI ^ 2 + qh.imJ ^ 2 + qh.imK ^ 2 ≠ 0 := hns
    have hL : qinv * qh = 1 := by
      ext
      · simp [qinv, norm]; field_simp [hns']
      · simp [qinv, norm]; exact Or.inr (by ring)
      · simp [qinv, norm]; exact Or.inr (by ring)
      · simp [qinv, norm]; exact Or.inr (by ring)
    have hR : qh * qinv = 1 := by
      ext
      · simp [qinv, norm]; field_simp [hns']
      · simp [qinv, norm]; exact Or.inr (by ring)
      · simp [qinv, norm]; exact Or.inr (by ring)
      · simp [qinv, norm]; exact Or.inr (by ring)
    exact ⟨⟨q, e.symm qinv,
      by apply e.injective; rw [map_mul, map_one, AlgEquiv.apply_symm_apply]; exact hR,
      by apply e.injective; rw [map_mul, map_one, AlgEquiv.apply_symm_apply]; exact hL⟩, rfl⟩
  refine ⟨⟨e⟩, ⟨top_ne_bot, fun J _ => ?_⟩, fun f hf => ?_⟩
  · by_cases hJ : J = ⊥
    · left; exact hJ
    · right
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hyJ, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      obtain ⟨u, rfl⟩ := hunit y hyne
      have h1 : (1 : CliffordAlgebra q02) ∈ J := by
        have := Submodule.smul_mem J (↑u⁻¹ : CliffordAlgebra q02) hyJ
        simpa using this
      simpa using Submodule.smul_mem J x h1
  · by_cases hf0 : f = 0
    · left; exact hf0
    · right
      obtain ⟨u, rfl⟩ := hunit f hf0
      have hmul : (u : CliffordAlgebra q02) * (u : CliffordAlgebra q02) = u := hf
      have h1 := congrArg (fun z => (↑u⁻¹ : CliffordAlgebra q02) * z) hmul
      simpa [← mul_assoc] using h1

end RieszCentralIdempotentsAndSpinorIdeals

end RieszPrimary

end InfoGeometry.Clifford.LipschitzWittRieszPrimary



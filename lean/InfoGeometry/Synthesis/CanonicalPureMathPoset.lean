/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# De-Confabulated 5-Stage Pure Mathematical Archetypes & Krein Space Self-Adjointness

This module formalizes five finite algebraic archetypes with Mathlib APIs. It also imports
the repo-owned `Cl11JordanWignerCARBridge` to reuse its finite Clifford/Jordan–Wigner result;
it is not a zero-custom-import Mathlib-only module:

1. **Archetype I (`ArchetypeI_SimplexRieszAndPetz`)**:
   - `fisherWeightedInner`, `rieszNaturalGradient`, `rieszNaturalGradient_sum_zero`,
     `scaled_fisher_riesz_representation`, `markovPush`, `petzAdjointMap`, and
     `petzAdjointMap_fisher_adjoint`.
2. **Archetype II (`ArchetypeII_Cl11NilpotentCell`)**:
   - `wittPlus`, `wittMinus`, `vacProj`, `occProj`, `chiralGrading`,
     `wittPlus_mul_wittMinus_ne_comm`, and `cl11_witt_peircian_algebra`.
3. **Archetype III (`ArchetypeIII_ParaKahlerAndCorrection`)**:
   - `ParaKahlerData` (possibly degenerate bilinear-form data), `projPlus`, `projMinus`, `paraKahler_isotropic_and_offDiagonal`,
     `IsometricSheetSwap`, `inducedJ`, the `C`-twisted bilinear form `trueHermitianMetric`,
     `norden_vs_true_hermitian_under_J`, `sheetSwap_krein_selfAdjoint`,
     `trueHermitianMetric_symm`, `paraComplex_krein_skewAdjoint`,
     `paraComplex_trueHermitianMetric_selfAdjoint`, `inducedJ_krein_selfAdjoint`,
     `inducedJ_trueHermitianMetric_skewAdjoint`,
     `krein_adjoint_of_trueHermitianMetric_adjoint`, `mobiusOrbitSetoid`, and
     `quotientQuadratic`.
4. **Archetype IV (`ArchetypeIV_ZornLeftAlternativeCl33`)**:
   - `ZornOct`, `dot3`, `cross3`, `zMul`, `zAdd`, `zSmul`, `pureVec`, and
     `zorn_leftMul_cl33_clifford_identity`.
5. **Archetype V (`ArchetypeV_ColimitKMSAndDispersion`)**:
   - `uhfStep`, `kms_trace_cycling_and_uhfStep`, and `quadratic_dispersion_nonneg_of_toomre`.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace InfoGeometry.Synthesis.CanonicalPureMathPoset

/-!
## Archetype I: Simplex Riesz Duality & Reversible Markov/Petz Adjoint
-/

section ArchetypeI_SimplexRieszAndPetz

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The inverse-weighted bilinear form `∑ i, (u_i * v_i) / ρ_i`. It is positive definite
only under additional positivity assumptions on `ρ`. -/
def fisherWeightedInner (ρ u v : n → ℝ) : ℝ :=
  ∑ i : n, (u i * v i) / ρ i

/-- The centered Riesz natural gradient `∇_ρ^{nat} ℓ_i = ρ_i * (ℓ_i - ∑ j, ρ_j * ℓ_j)`. -/
def rieszNaturalGradient (ρ ℓ : n → ℝ) (i : n) : ℝ :=
  ρ i * (ℓ i - ∑ j : n, ρ j * ℓ j)

/-- **Lemma 1.1 (Zero-Sum Tangent Space Membership of the Riesz Natural Gradient):**
If `∑ i, ρ_i = 1`, then `∑ i, (∇_ρ^{nat} ℓ)_i = 0`. -/
theorem rieszNaturalGradient_sum_zero (ρ ℓ : n → ℝ) (hρ_sum : ∑ i : n, ρ i = 1) :
    ∑ i : n, rieszNaturalGradient ρ ℓ i = 0 := by
  unfold rieszNaturalGradient
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hρ_sum, one_mul, sub_self]

private theorem scaled_riesz_term_eq (c r l avg w : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) :
    c * (c⁻¹ * (r * (l - avg)) * w / r) = l * w - avg * w := by
  field_simp [hc, hr]

/-- **Theorem 1.2 (Exact Scaled Weighted-Bilinear Representation):**
For any nonzero `ρ_i`, nonzero scale `c ≠ 0`, and vector `w`
satisfying `∑ i, w_i = 0`, the `c`-scaled Fisher pairing of `c⁻¹ • rieszNaturalGradient ρ ℓ`
with `w` equals the canonical dual pairing `∑ i, ℓ_i * w_i`. -/
theorem scaled_fisher_riesz_representation
    (ρ ℓ w : n → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hρ : ∀ i : n, ρ i ≠ 0) (hw : ∑ i : n, w i = 0) :
    c * fisherWeightedInner ρ (fun i => c⁻¹ * rieszNaturalGradient ρ ℓ i) w =
      ∑ i : n, ℓ i * w i := by
  unfold fisherWeightedInner rieszNaturalGradient
  rw [Finset.mul_sum]
  have h_term : ∀ i : n,
      c * (c⁻¹ * (ρ i * (ℓ i - ∑ j : n, ρ j * ℓ j)) * w i / ρ i) =
        ℓ i * w i - (∑ j : n, ρ j * ℓ j) * w i :=
    fun i => scaled_riesz_term_eq c (ρ i) (ℓ i) (∑ j : n, ρ j * ℓ j) (w i) hc (hρ i)
  simp_rw [h_term, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_zero, sub_zero]

/-- Forward linear operator `T(x)_j = ∑ i, T_{j,i} * x_i`. -/
def markovPush (T : Matrix m n ℝ) (x : n → ℝ) (j : m) : ℝ :=
  ∑ i : n, T j i * x i

/-- The Petz recovery transpose `R_{ρ,T}(y)_i = ρ_i * ∑ j, T_{j,i} * (y_j / (Tρ)_j)`. -/
def petzAdjointMap (ρ : n → ℝ) (T : Matrix m n ℝ) (y : m → ℝ) (i : n) : ℝ :=
  ρ i * ∑ j : m, T j i * (y j / markovPush T ρ j)

private theorem petz_term_rearrange (a b c d : ℝ) :
    a * (b / c) * d = (b * (a * d)) / c := by
  ring

/-- **Theorem 1.3 (Algebraic Weighted-Bilinear Adjoint Identity):**
Whenever each `ρ_i ≠ 0`, the displayed identity holds for the totalized real divisions in
`petzAdjointMap` and `fisherWeightedInner`. To interpret it as a conventional Petz/Fisher
adjoint with an inverse-weight pairing on the output, one must also assume every `(Tρ)_j ≠ 0`;
that support hypothesis is not part of this algebraic identity. The identity is
`fisherWeightedInner ρ (petzAdjointMap ρ T y) x =
  fisherWeightedInner (markovPush T ρ) y (markovPush T x)`. -/
theorem petzAdjointMap_fisher_adjoint
    (ρ x : n → ℝ) (T : Matrix m n ℝ) (y : m → ℝ)
    (hρ : ∀ i : n, ρ i ≠ 0) :
    fisherWeightedInner ρ (petzAdjointMap ρ T y) x =
      fisherWeightedInner (markovPush T ρ) y (markovPush T x) := by
  unfold fisherWeightedInner petzAdjointMap
  calc
    ∑ i : n, (ρ i * (∑ j : m, T j i * (y j / markovPush T ρ j)) * x i) / ρ i
      = ∑ i : n, ((∑ j : m, T j i * (y j / markovPush T ρ j)) * x i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_assoc, mul_div_cancel_left₀ _ (hρ i)]
    _ = ∑ i : n, ∑ j : m, (T j i * (y j / markovPush T ρ j) * x i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ j : m, ∑ i : n, (T j i * (y j / markovPush T ρ j) * x i) := by
          rw [Finset.sum_comm]
    _ = ∑ j : m, (y j * markovPush T x j) / markovPush T ρ j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have h_push : markovPush T x j = ∑ i : n, T j i * x i := rfl
          rw [h_push, Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact petz_term_rearrange (T j i) (y j) (markovPush T ρ j) (x i)

end ArchetypeI_SimplexRieszAndPetz

/-!
## Archetype II: Split Cell `Cl(1,1) ≅ M₂(ℝ)`, Witt Nilpotents & Peircian Idempotents
-/

section ArchetypeII_Cl11NilpotentCell

/-- Positive Witt null ladder generator `n₊ = E₀₁` in `M₂(ℝ) ≅ Cl(1,1)`. -/
def wittPlus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Negative Witt null ladder generator `n₋ = E₁₀` in `M₂(ℝ) ≅ Cl(1,1)`. -/
def wittMinus : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- Vacuum Peircian projector `P_vac = n₊ * n₋ = diag(1, 0)`. -/
def vacProj : Matrix (Fin 2) (Fin 2) ℝ := wittPlus * wittMinus

/-- Occupied Peircian projector `P_occ = n₋ * n₊ = diag(0, 1)`. -/
def occProj : Matrix (Fin 2) (Fin 2) ℝ := wittMinus * wittPlus

/-- Chiral grading operator `ω = P_occ - P_vac = diag(-1, 1)`. -/
def chiralGrading : Matrix (Fin 2) (Fin 2) ℝ := occProj - vacProj

/-- Non-commutativity witness for the Witt ladder generators `wittPlus` and `wittMinus`
(Gate 2.5 / Trap T12). -/
theorem wittPlus_mul_wittMinus_ne_comm :
    wittPlus * wittMinus ≠ wittMinus * wittPlus := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [wittPlus, wittMinus, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- **Theorem 2.1 (Complete Nilpotent CAR & Peircian Idempotent Algebra in `M₂(ℝ)`):**
1. `n₊² = 0` and `n₋² = 0`,
2. `n₊ n₋ + n₋ n₊ = I₂` (`P_vac + P_occ = I₂`),
3. `P_vac² = P_vac`, `P_occ² = P_occ`, and `P_vac P_occ = 0`,
4. `{ω, n₊} = 0` and `{ω, n₋} = 0`. -/
theorem cl11_witt_peircian_algebra :
    wittPlus * wittPlus = 0 ∧
    wittMinus * wittMinus = 0 ∧
    vacProj + occProj = 1 ∧
    vacProj * vacProj = vacProj ∧
    occProj * occProj = occProj ∧
    vacProj * occProj = 0 ∧
    chiralGrading * wittPlus + wittPlus * chiralGrading = 0 ∧
    chiralGrading * wittMinus + wittMinus * chiralGrading = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [wittPlus, wittMinus, vacProj, occProj, chiralGrading,
            Matrix.mul_apply, Fin.sum_univ_two])

end ArchetypeII_Cl11NilpotentCell

/-!
## Archetype III: Para-Kähler-Type Bilinear Identities, Norden Symmetry, Krein Self-Adjointness & `ℤ₂` Quotient
-/

section ArchetypeIII_ParaKahlerAndCorrection

/-- Algebraic para-Kähler-type data over `ℝ`: `K² = id`, a symmetric bilinear form `g` with
`g(Ku, Kv) = -g(u,v)`, and `ω(u,v) = g(Ku, v)`. The form is not assumed nondegenerate,
so this structure alone does not assert a pseudo-Riemannian or para-Kähler metric. -/
structure ParaKahlerData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  K : V →ₗ[ℝ] V
  K_sq : ∀ v, K (K v) = v
  g_symm : ∀ u v, g u v = g v u
  g_anti : ∀ u v, g (K u) (K v) = -g u v
  omega_def : ∀ u v, omega u v = g (K u) v

instance instInhabitedParaKahlerData (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Inhabited (ParaKahlerData V) :=
  ⟨{ g := 0
     omega := 0
     K := LinearMap.id
     K_sq := fun _ => rfl
     g_symm := fun _ _ => rfl
     g_anti := fun _ _ => by simp
     omega_def := fun _ _ => rfl }⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The form induced by `D` is skew-symmetric. This uses only the displayed
para-Kähler-type laws; it does not require `g` to be nondegenerate. -/
theorem paraKahler_omega_skew (D : ParaKahlerData V) (u v : V) :
    D.omega u v = -D.omega v u := by
  rw [D.omega_def, D.omega_def]
  have h := D.g_anti u (D.K v)
  rw [D.K_sq] at h
  calc
    D.g (D.K u) v = -D.g u (D.K v) := h
    _ = -D.g (D.K v) u := by rw [D.g_symm]

/-- Spectral projector `P⁺(v) = (1/2) • (v + K v)` onto `T⁺ = ker(K - id)`. -/
def projPlus (D : ParaKahlerData V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + D.K)

/-- Spectral projector `P⁻(v) = (1/2) • (v - K v)` onto `T⁻ = ker(K + id)`. -/
def projMinus (D : ParaKahlerData V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - D.K)

theorem K_projPlus (D : ParaKahlerData V) (v : V) :
    D.K (projPlus D v) = projPlus D v := by
  unfold projPlus
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
             map_smul, map_add, D.K_sq, add_comm]

theorem K_projMinus (D : ParaKahlerData V) (v : V) :
    D.K (projMinus D v) = -projMinus D v := by
  unfold projMinus
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
             map_smul, map_sub, D.K_sq]
  rw [← smul_neg, neg_sub]

theorem projPlus_add_projMinus (D : ParaKahlerData V) (u : V) :
    projPlus D u + projMinus D u = u := by
  unfold projPlus projMinus
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [← smul_add]
  have h_add : (u + D.K u) + (u - D.K u) = (2 : ℝ) • u := by
    calc
      (u + D.K u) + (u - D.K u) = (u + u) + (D.K u - D.K u) := by abel
      _                         = (u + u) + 0               := by rw [sub_self]
      _                         = u + u                     := add_zero _
      _                         = (2 : ℝ) • u               := (two_smul ℝ u).symm
  rw [h_add, smul_smul]
  norm_num

private theorem real_eq_zero_of_eq_neg {x : ℝ} (h : x = -x) : x = 0 := by
  linarith [h]

/-- **Theorem 3.1 (Isotropic Sheet Nullity & Off-Diagonal Metric Reduction):**
Both spectral eigen-sheets `T⁺` and `T⁻` are totally isotropic (`g(P⁺v, P⁺w) = 0` and
`g(P⁻v, P⁻w) = 0`), and `g(v, w) = g(P⁺v, P⁻w) + g(P⁻v, P⁺w)`. -/
theorem paraKahler_isotropic_and_offDiagonal (D : ParaKahlerData V) (v w : V) :
    D.g (projPlus D v) (projPlus D w) = 0 ∧
    D.g (projMinus D v) (projMinus D w) = 0 ∧
    D.g v w = D.g (projPlus D v) (projMinus D w) + D.g (projMinus D v) (projPlus D w) := by
  have h_plus : D.g (projPlus D v) (projPlus D w) = 0 := by
    have h1 := D.g_anti (projPlus D v) (projPlus D w)
    rw [K_projPlus, K_projPlus] at h1
    exact real_eq_zero_of_eq_neg h1
  have h_minus : D.g (projMinus D v) (projMinus D w) = 0 := by
    have h1 := D.g_anti (projMinus D v) (projMinus D w)
    rw [K_projMinus, K_projMinus, map_neg, map_neg, LinearMap.neg_apply, neg_neg] at h1
    exact real_eq_zero_of_eq_neg h1
  refine ⟨h_plus, h_minus, ?_⟩
  conv_lhs => rw [← projPlus_add_projMinus D v, ← projPlus_add_projMinus D w]
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
    h_plus, h_minus, zero_add, add_zero, add_comm]

/-- A `g`-preserving sheet-swapping involution `C`: `C² = id`, `C(K v) = -K(C v)`,
and `g(Cu, Cv) = g(u, v)`. Since `g` may be degenerate, this does not assert a
pseudo-Riemannian isometry. -/
structure IsometricSheetSwap (D : ParaKahlerData V) where
  C : V →ₗ[ℝ] V
  C_sq : ∀ v, C (C v) = v
  C_anticomm_K : ∀ v, C (D.K v) = -D.K (C v)
  C_isometric : ∀ u v, D.g (C u) (C v) = D.g u v

instance instInhabitedIsometricSheetSwap :
    Inhabited (IsometricSheetSwap (default : ParaKahlerData PUnit)) :=
  ⟨{ C := 0
     C_sq := fun _ => Subsingleton.elim _ _
     C_anticomm_K := fun _ => Subsingleton.elim _ _
     C_isometric := fun _ _ => rfl }⟩


/-- Induced complex structure `J = C ∘ K`. -/
def inducedJ {D : ParaKahlerData V} (S : IsometricSheetSwap D) : V →ₗ[ℝ] V :=
  S.C.comp D.K

/-- `C`-twisted symmetric bilinear form `g_C(u, v) = g(u, C v)`. Its `J`-invariance is
proved below; nondegeneracy is not asserted by these hypotheses. -/
def trueHermitianMetric {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) : ℝ :=
  D.g u (S.C v)

theorem K_comp_C {D : ParaKahlerData V} (S : IsometricSheetSwap D) (w : V) :
    D.K (S.C w) = -S.C (D.K w) := by
  have h := S.C_anticomm_K w
  calc
    D.K (S.C w) = - (- D.K (S.C w)) := (neg_neg _).symm
    _           = - (S.C (D.K w))   := by rw [← h]

/-- **Theorem 3.2 (Norden Anti-Invariance of `g` and `J`-Invariance of the Twisted Form):**
For `J = C ∘ K`:
1. `J (J v) = -v` (`J² = -id`),
2. `g(J u, J v) = -g(u, v)` (`g` is Norden anti-Hermitian),
3. `ω(J u, J v) = +ω(u, v)` (`ω` is `J`-invariant),
4. `g_C(J u, J v) = +g_C(u, v)` for the defined `C`-twisted bilinear form. -/
theorem norden_vs_true_hermitian_under_J {D : ParaKahlerData V} (S : IsometricSheetSwap D)
    (u v : V) :
    inducedJ S (inducedJ S v) = -v ∧
    D.g (inducedJ S u) (inducedJ S v) = -D.g u v ∧
    D.omega (inducedJ S u) (inducedJ S v) = D.omega u v ∧
    trueHermitianMetric S (inducedJ S u) (inducedJ S v) = trueHermitianMetric S u v := by
  have hJ_sq : ∀ w, inducedJ S (inducedJ S w) = -w := by
    intro w
    unfold inducedJ
    simp only [LinearMap.comp_apply, S.C_anticomm_K, map_neg, D.K_sq, S.C_sq]
  refine ⟨hJ_sq v, ?_, ?_, ?_⟩
  · unfold inducedJ
    simp only [LinearMap.comp_apply, S.C_isometric, D.g_anti]
  · unfold inducedJ
    simp only [D.omega_def, LinearMap.comp_apply]
    have hKC := K_comp_C S (D.K u)
    rw [hKC, D.K_sq u, map_neg, LinearMap.neg_apply, S.C_isometric]
    calc
      -D.g u (D.K v) = -(-D.g (D.K u) (D.K (D.K v))) := by rw [← D.g_anti u (D.K v), neg_neg]
      _ = D.g (D.K u) v := by rw [neg_neg, D.K_sq v]
  · unfold trueHermitianMetric inducedJ
    simp only [LinearMap.comp_apply]
    rw [S.C_isometric (D.K u) (S.C (D.K v)), S.C_anticomm_K v, map_neg,
      D.g_anti u (S.C v), neg_neg]

/-- **Krein Self-Adjointness of the Fundamental Symmetry `C`**:
`g (C u) v = g u (C v) = trueHermitianMetric S u v`. -/
theorem sheetSwap_krein_selfAdjoint {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) :
    D.g (S.C u) v = D.g u (S.C v) := by
  calc
    D.g (S.C u) v = D.g (S.C (S.C u)) (S.C v) := (S.C_isometric (S.C u) v).symm
    _ = D.g u (S.C v) := by rw [S.C_sq u]

/-- Symmetry of the `C`-twisted bilinear form `trueHermitianMetric S`:
`trueHermitianMetric S u v = trueHermitianMetric S v u`. -/
theorem trueHermitianMetric_symm {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) :
    trueHermitianMetric S u v = trueHermitianMetric S v u := by
  dsimp [trueHermitianMetric]
  calc
    D.g u (S.C v) = D.g (S.C u) v := (sheetSwap_krein_selfAdjoint S u v).symm
    _ = D.g v (S.C u) := D.g_symm (S.C u) v

/-- **Krein Skew-Adjointness of the Paracomplex Operator `K`**:
With respect to the indefinite Krein metric `g`, `K` is skew-adjoint (`g(Ku, v) = -g(u, Kv)`). -/
theorem paraComplex_krein_skewAdjoint (D : ParaKahlerData V) (u v : V) :
    D.g (D.K u) v = -D.g u (D.K v) := by
  calc
    D.g (D.K u) v = D.g (D.K u) (D.K (D.K v)) := by rw [D.K_sq v]
    _ = -D.g u (D.K v) := D.g_anti u (D.K v)

/-- **Symmetry of `K` for the `C`-Twisted Bilinear Form**:
With respect to `trueHermitianMetric S`, `K` is self-adjoint (`g_C(Ku, v) = g_C(u, Kv)`). -/
theorem paraComplex_trueHermitianMetric_selfAdjoint
    {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) :
    trueHermitianMetric S (D.K u) v = trueHermitianMetric S u (D.K v) := by
  dsimp [trueHermitianMetric]
  calc
    D.g (D.K u) (S.C v) = -D.g u (D.K (S.C v)) :=
      paraComplex_krein_skewAdjoint D u (S.C v)
    _ = -D.g u (-S.C (D.K v)) := by rw [K_comp_C S v]
    _ = D.g u (S.C (D.K v)) := by rw [map_neg, neg_neg]

/-- **Krein Self-Adjointness of the Induced Complex Structure `J = C ∘ K`**:
With respect to the indefinite Krein metric `g`, `J = inducedJ S` is **Krein self-adjoint**
(`g(Ju, v) = +g(u, Jv)`). -/
theorem inducedJ_krein_selfAdjoint {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) :
    D.g (inducedJ S u) v = D.g u (inducedJ S v) := by
  dsimp [inducedJ]
  calc
    D.g (S.C (D.K u)) v = D.g (D.K u) (S.C v) :=
      sheetSwap_krein_selfAdjoint S (D.K u) v
    _ = D.g u (S.C (D.K v)) :=
      paraComplex_trueHermitianMetric_selfAdjoint S u v

/-- **Skew-Adjointness of `J = C ∘ K` under `trueHermitianMetric S`**:
`g_C(Ju, v) = -g_C(u, Jv)`. -/
theorem inducedJ_trueHermitianMetric_skewAdjoint
    {D : ParaKahlerData V} (S : IsometricSheetSwap D) (u v : V) :
    trueHermitianMetric S (inducedJ S u) v = -trueHermitianMetric S u (inducedJ S v) := by
  have hJ := (norden_vs_true_hermitian_under_J S u (inducedJ S v)).2.2.2
  have hJ_sq := (norden_vs_true_hermitian_under_J S u v).1
  calc
    trueHermitianMetric S (inducedJ S u) v
      = -trueHermitianMetric S (inducedJ S u) (inducedJ S (inducedJ S v)) := by
          dsimp [trueHermitianMetric]
          rw [hJ_sq, map_neg, map_neg, neg_neg]
    _ = -trueHermitianMetric S u (inducedJ S v) := by rw [hJ]

/-- **General Krein Adjoint Formula ($A^{[*]_g} = C \circ A^{*_{g_C}} \circ C$)**:
If `A_adj` is the adjoint of `A` with respect to `trueHermitianMetric S`, then
`C ∘ A_adj ∘ C` is the Krein adjoint of `A` with respect to `g`. -/
theorem krein_adjoint_of_trueHermitianMetric_adjoint
    {D : ParaKahlerData V} (S : IsometricSheetSwap D)
    (A A_adj : V →ₗ[ℝ] V)
    (h_adj : ∀ x y : V, trueHermitianMetric S (A x) y = trueHermitianMetric S x (A_adj y))
    (u v : V) :
    D.g (A u) v = D.g u (S.C (A_adj (S.C v))) := by
  calc
    D.g (A u) v = D.g (A u) (S.C (S.C v)) := by rw [S.C_sq v]
    _ = trueHermitianMetric S (A u) (S.C v) := rfl
    _ = trueHermitianMetric S u (A_adj (S.C v)) := h_adj u (S.C v)
    _ = D.g u (S.C (A_adj (S.C v))) := rfl

/-- The `ℤ₂`-orbit equivalence relation `u ~_C v ↔ u = v ∨ u = C v`. -/
def mobiusOrbitSetoid {D : ParaKahlerData V} (S : IsometricSheetSwap D) : Setoid V where
  r u v := u = v ∨ u = S.C v
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro u v (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (S.C_sq v).symm
    trans := by
      rintro u v w (rfl | rfl) (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (S.C_sq w)
  }

/-- Well-defined descent of the Krein quadratic form `Q(v) = g(v, v)` to the `ℤ₂`-orbit space
`V / ~_C`. -/
def quotientQuadratic {D : ParaKahlerData V} (S : IsometricSheetSwap D) :
    Quotient (mobiusOrbitSetoid S) → ℝ :=
  Quotient.lift (fun v => D.g v v) (by
    rintro u v (rfl | rfl)
    · rfl
    · exact S.C_isometric v v)

/-- Weighted inner product $\langle u, v \rangle_\pi = \sum_i \pi_i u_i v_i$ on a finite index type. -/
def innerPi {ι : Type*} [Fintype ι] (π u v : ι → ℝ) : ℝ :=
  ∑ i : ι, π i * u i * v i

/-- Off-diagonal neutral Krein pairing
$g_\pi((u_+, u_-), (v_+, v_-)) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi$
on the Double Real Krein Space $\mathcal{K}_\iota = (\iota \to \mathbb{R}) \times (\iota \to \mathbb{R})$. -/
def gPi {ι : Type*} [Fintype ι] (π : ι → ℝ) (u v : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  innerPi π u.1 v.2 + innerPi π u.2 v.1

/-- Symmetry of the neutral Krein pairing: $g_\pi(u, v) = g_\pi(v, u)$. -/
theorem gPi_symm {ι : Type*} [Fintype ι] (π : ι → ℝ) (u v : (ι → ℝ) × (ι → ℝ)) :
    gPi π u v = gPi π v u := by
  unfold gPi innerPi
  have h1 : ∀ a b : ι → ℝ, ∑ i : ι, π i * a i * b i = ∑ i : ι, π i * b i * a i := by
    intro a b
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h1 u.1 v.2, h1 u.2 v.1, add_comm]

/-- The primal null sheet $T^+ = \{(u_+, 0)\}$ is totally isotropic:
$g_\pi((u_+, 0), (v_+, 0)) = 0$. -/
theorem primal_sheet_isotropic {ι : Type*} [Fintype ι] (π u v : ι → ℝ) :
    gPi π (u, 0) (v, 0) = 0 := by
  simp [gPi, innerPi]

/-- The dual null sheet $T^- = \{(0, u_-)\}$ is totally isotropic:
$g_\pi((0, u_-), (0, v_-)) = 0$. -/
theorem dual_sheet_isotropic {ι : Type*} [Fintype ι] (π u v : ι → ℝ) :
    gPi π (0, u) (0, v) = 0 := by
  simp [gPi, innerPi]

/-- Matrix-vector action $(P v)_i = \sum_j P_{ij} v_j$. -/
def matMul {ι : Type*} [Fintype ι] (P : ι → ι → ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j : ι, P i j * v j

/-- The $\pi$-dual operator $(P^{\#_\pi})_{ij} = (\pi_j / \pi_i) P_{ji}$ acting on the dual null sheet $T^-$. -/
noncomputable def markovDual {ι : Type*} (π : ι → ℝ) (P : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => (π j / π i) * P j i

/-- Cross-sheet $\pi$-adjoint duality $\langle P u, v \rangle_\pi = \langle u, P^{\#_\pi} v \rangle_\pi$. -/
theorem matMul_markovDual_adjoint {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i : ι, π i ≠ 0) (P : ι → ι → ℝ) (u v : ι → ℝ) :
    innerPi π (matMul P u) v = innerPi π u (matMul (markovDual π P) v) := by
  unfold innerPi matMul markovDual
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  have hπi : π i ≠ 0 := hπ i
  have hπj : π j ≠ 0 := hπ j
  calc
    π i * (P i j * u j) * v i = π i * P i j * u j * v i := by ring
    _ = π j * ((π i / π j) * P i j) * u j * v i := by
        field_simp [hπi, hπj]
    _ = π j * u j * (((π i / π j) * P i j) * v i) := by ring

/-- The block-diagonal Double Real Krein Operator $\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$. -/
noncomputable def kreinOp {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : ι → ι → ℝ) (w : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (matMul P w.1, matMul (markovDual π P) w.2)

/-- **Universal Double Real Krein Self-Adjointness**:
For EVERY matrix $P$ (causal or non-causal), $\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$
is strictly self-adjoint with respect to the neutral Krein pairing $g_\pi$:
$g_\pi(\mathcal{T}_P u, v) = g_\pi(u, \mathcal{T}_P v)$. -/
theorem kreinOp_self_adjoint {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i : ι, π i ≠ 0)
    (P : ι → ι → ℝ) (u v : (ι → ℝ) × (ι → ℝ)) :
    gPi π (kreinOp π P u) v = gPi π u (kreinOp π P v) := by
  unfold gPi kreinOp
  dsimp
  rw [matMul_markovDual_adjoint π hπ P u.1 v.2]
  have h2 : innerPi π (matMul (markovDual π P) u.2) v.1 = innerPi π u.2 (matMul P v.1) := by
    have h_symm := matMul_markovDual_adjoint π hπ (markovDual π P) u.2 v.1
    have h_inv : markovDual π (markovDual π P) = P := by
      unfold markovDual
      ext i j
      have hπi : π i ≠ 0 := hπ i
      have hπj : π j ≠ 0 := hπ j
      field_simp [hπi, hπj]
    rw [h_inv] at h_symm
    exact h_symm
  rw [h2]

/-- Strictly causal (lower-triangular) predicate: $P_{ij} = 0$ whenever $i < j$. -/
def IsCausal {ι : Type*} [LinearOrder ι] (P : ι → ι → ℝ) : Prop :=
  ∀ i j : ι, i < j → P i j = 0

/-- Anti-causal (upper-triangular) predicate: $Q_{ij} = 0$ whenever $j < i$. -/
def IsAntiCausal {ι : Type*} [LinearOrder ι] (Q : ι → ι → ℝ) : Prop :=
  ∀ i j : ι, j < i → Q i j = 0

/-- **Causal-to-Anti-Causal Dualization**:
If $P$ is causal (lower-triangular) on $T^+$, then its $\pi$-dual $P^{\#_\pi}$ is strictly
anti-causal (upper-triangular) on $T^-$. -/
theorem causal_dual_is_antiCausal {ι : Type*} [LinearOrder ι]
    (π : ι → ℝ) (P : ι → ι → ℝ) (h_causal : IsCausal P) :
    IsAntiCausal (markovDual π P) := by
  intro i j hji
  dsimp [markovDual]
  rw [h_causal j i hji, mul_zero]

/-- **Resolution of the Causal Triviality Paradox on $\mathcal{K}_2$**:
There exists a strictly non-trivial causal operator ($P \neq I$) on `Fin 2` that is
Krein self-adjoint on $\mathcal{K}_2 = (\operatorname{Fin} 2 \to \mathbb{R}) \times (\operatorname{Fin} 2 \to \mathbb{R})$. -/
theorem exists_nontrivial_causal_krein_operator :
    ∃ (π : Fin 2 → ℝ) (P : Fin 2 → Fin 2 → ℝ),
      (∀ i : Fin 2, 0 < π i) ∧
      IsCausal P ∧
      P ≠ (fun i j => if i = j then 1 else 0) ∧
      (∀ u v : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        gPi π (kreinOp π P u) v = gPi π u (kreinOp π P v)) := by
  let π : Fin 2 → ℝ := fun _ => 1
  let P : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then 1
    else 0
  have hπ_pos : ∀ i : Fin 2, 0 < π i := fun _ => one_pos
  have hπ_ne : ∀ i : Fin 2, π i ≠ 0 := fun i => ne_of_gt (hπ_pos i)
  have h_causal : IsCausal P := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl 0 hij)
    · rfl
    · exact False.elim (not_lt_of_gt Fin.zero_lt_one hij)
    · exact False.elim (lt_irrefl 1 hij)
  have h_ne_id : P ≠ (fun i j => if i = j then 1 else 0) := by
    intro h_eq
    have h_entry := congr_fun (congr_fun h_eq 1) 0
    dsimp [P] at h_entry
    norm_num at h_entry
  exact ⟨π, P, hπ_pos, h_causal, h_ne_id, kreinOp_self_adjoint π hπ_ne P⟩

end ArchetypeIII_ParaKahlerAndCorrection

/-!
## Archetype IV: Zorn Split-Octonion Left-Alternativity & Direct `Cl(3,3)` Representation on `ℝ⁸`
-/

section ArchetypeIV_ZornLeftAlternativeCl33

/-- An element of Zorn's split-octonion vector-matrix algebra over `R`. -/
@[ext]
structure ZornOct (R : Type*) where
  a : R
  u : Fin 3 → R
  v : Fin 3 → R
  b : R

instance instInhabitedZornOct {R : Type*} [Zero R] : Inhabited (ZornOct R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

/-- Concrete non-zero integer witness for `ZornOct` (Gate 2.5 / Trap T17). -/
def canonicalZornOct : ZornOct ℤ :=
  ⟨1, ![1, 0, 0], ![0, 1, 0], 1⟩

/-- The canonical Zorn split-octonion witness has non-zero scalar component `a`. -/
theorem canonicalZornOct_a_ne_zero :
    canonicalZornOct.a ≠ 0 := by
  decide

variable {R : Type*} [CommRing R]

/-- Standard 3-vector dot product `⟨x, y⟩ = x₀ y₀ + x₁ y₁ + x₂ y₂`. -/
def dot3 (x y : Fin 3 → R) : R :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- Standard 3-vector cross product `x × y`. -/
def cross3 (x y : Fin 3 → R) : Fin 3 → R :=
  ![ x 1 * y 2 - x 2 * y 1,
     x 2 * y 0 - x 0 * y 2,
     x 0 * y 1 - x 1 * y 0 ]

/-- Zorn vector-matrix product on `ZornOct R`. -/
def zMul (x y : ZornOct R) : ZornOct R where
  a := x.a * y.a + dot3 x.u y.v
  u := fun k => x.a * y.u k + y.b * x.u k - cross3 x.v y.v k
  v := fun k => y.a * x.v k + x.b * y.v k + cross3 x.u y.u k
  b := x.b * y.b + dot3 x.v y.u

/-- Componentwise addition on `ZornOct R`. -/
def zAdd (x y : ZornOct R) : ZornOct R :=
  ⟨x.a + y.a, fun k => x.u k + y.u k, fun k => x.v k + y.v k, x.b + y.b⟩

/-- Componentwise scalar multiplication on `ZornOct R`. -/
def zSmul (c : R) (x : ZornOct R) : ZornOct R :=
  ⟨c * x.a, fun k => c * x.u k, fun k => c * x.v k, c * x.b⟩

/-- Pure para-Kähler vector embedding `ι(u, v) = (0, u, v, 0) ∈ 𝕆_s`. -/
def pureVec (u v : Fin 3 → R) : ZornOct R :=
  ⟨0, u, v, 0⟩

/-- **Theorem 4.1 (Direct `Cl(3,3)` Representation on `𝕆_s ≅ ℝ⁸` via Polarized Left-Alternativity):**
For ALL pure vectors `z₁ = (u₁, v₁)`, `z₂ = (u₂, v₂)` and EVERY state `w ∈ ZornOct R`,
raw left multiplication satisfies the exact associative `Cl(3,3)` Clifford law:
`ι(z₁) ⋆ (ι(z₂) ⋆ w) + ι(z₂) ⋆ (ι(z₁) ⋆ w) = (⟨u₁, v₂⟩ + ⟨u₂, v₁⟩) • w`. -/
theorem zorn_leftMul_cl33_clifford_identity
    (u₁ v₁ u₂ v₂ : Fin 3 → R) (w : ZornOct R) :
    zAdd (zMul (pureVec u₁ v₁) (zMul (pureVec u₂ v₂) w))
         (zMul (pureVec u₂ v₂) (zMul (pureVec u₁ v₁) w)) =
      zSmul (dot3 u₁ v₂ + dot3 u₂ v₁) w := by
  refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_
  · unfold zAdd zMul pureVec zSmul dot3 cross3; dsimp; ring
  · fin_cases k <;> (unfold zAdd zMul pureVec zSmul dot3 cross3; dsimp; ring)
  · fin_cases k <;> (unfold zAdd zMul pureVec zSmul dot3 cross3; dsimp; ring)
  · unfold zAdd zMul pureVec zSmul dot3 cross3; dsimp; ring

/-- Zero element of `ZornOct R`. -/
def zZero : ZornOct R :=
  ⟨0, fun _ => 0, fun _ => 0, 0⟩

/-- Componentwise subtraction on `ZornOct R`. -/
def zSub (x y : ZornOct R) : ZornOct R :=
  ⟨x.a - y.a, fun k => x.u k - y.u k, fun k => x.v k - y.v k, x.b - y.b⟩

/-- Componentwise negation on `ZornOct R`. -/
def zNeg (w : ZornOct R) : ZornOct R :=
  ⟨-w.a, fun k => -w.u k, fun k => -w.v k, -w.b⟩

/-- Site 0 parity operator $Z_0$ on `ZornOct R`: multiplies states with bit $0 = 1$ by $-1$. -/
def zSiteParity0 (w : ZornOct R) : ZornOct R :=
  ⟨w.a, ![-w.u 0, w.u 1, w.u 2], ![w.v 0, -w.v 1, -w.v 2], -w.b⟩

/-- Site 1 parity operator $Z_1$ on `ZornOct R`: multiplies states with bit $1 = 1$ by $-1$. -/
def zSiteParity1 (w : ZornOct R) : ZornOct R :=
  ⟨w.a, ![w.u 0, -w.u 1, w.u 2], ![-w.v 0, w.v 1, -w.v 2], -w.b⟩

/-- Site 2 parity operator $Z_2$ on `ZornOct R`: multiplies states with bit $2 = 1$ by $-1$. -/
def zSiteParity2 (w : ZornOct R) : ZornOct R :=
  ⟨w.a, ![w.u 0, w.u 1, -w.u 2], ![-w.v 0, -w.v 1, w.v 2], -w.b⟩

/-- Parity operators are involutive: $Z_k^2 = \mathrm{id}$. -/
theorem zSiteParity_involutive (w : ZornOct R) :
    zSiteParity0 (zSiteParity0 w) = w ∧
    zSiteParity1 (zSiteParity1 w) = w ∧
    zSiteParity2 (zSiteParity2 w) = w := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;> dsimp [zSiteParity0, zSiteParity1, zSiteParity2] <;> ring)

/-- Parity operators commute pairwise: $[Z_j, Z_k] = 0$. -/
theorem zSiteParity_commute (w : ZornOct R) :
    zSiteParity0 (zSiteParity1 w) = zSiteParity1 (zSiteParity0 w) ∧
    zSiteParity0 (zSiteParity2 w) = zSiteParity2 (zSiteParity0 w) ∧
    zSiteParity1 (zSiteParity2 w) = zSiteParity2 (zSiteParity1 w) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;> dsimp [zSiteParity0, zSiteParity1, zSiteParity2])

/-- Jordan–Wigner string for site 0: $S_0 = \mathrm{id}$. -/
def jwString0 (w : ZornOct R) : ZornOct R := w

/-- Jordan–Wigner string for site 1: $S_1 = Z_0$. -/
def jwString1 (w : ZornOct R) : ZornOct R := zSiteParity0 w

/-- Jordan–Wigner string for site 2: $S_2 = Z_0 \circ Z_1$. -/
def jwString2 (w : ZornOct R) : ZornOct R := zSiteParity0 (zSiteParity1 w)

/-- Jordan–Wigner strings are involutive: $S_j^2 = \mathrm{id}$. -/
theorem jwString_involutive (w : ZornOct R) :
    jwString0 (jwString0 w) = w ∧
    jwString1 (jwString1 w) = w ∧
    jwString2 (jwString2 w) = w := by
  refine ⟨rfl, (zSiteParity_involutive w).1, ?_⟩
  unfold jwString2
  rw [← (zSiteParity_commute (zSiteParity1 w)).1,
    (zSiteParity_involutive (zSiteParity1 (zSiteParity1 w))).1,
    (zSiteParity_involutive w).2.1]

/-- Unstringed local lowering operator $\sigma_0^-$ on `ZornOct R`. -/
def localLower0 (w : ZornOct R) : ZornOct R :=
  ⟨w.u 0, ![0, w.v 2, w.v 1], ![w.b, 0, 0], 0⟩

/-- Unstringed local raising operator $\sigma_0^+$ on `ZornOct R`. -/
def localRaise0 (w : ZornOct R) : ZornOct R :=
  ⟨0, ![w.a, 0, 0], ![0, w.u 2, w.u 1], w.v 0⟩

/-- Unstringed local lowering operator $\sigma_1^-$ on `ZornOct R`. -/
def localLower1 (w : ZornOct R) : ZornOct R :=
  ⟨w.u 1, ![w.v 2, 0, w.v 0], ![0, w.b, 0], 0⟩

/-- Unstringed local raising operator $\sigma_1^+$ on `ZornOct R`. -/
def localRaise1 (w : ZornOct R) : ZornOct R :=
  ⟨0, ![0, w.a, 0], ![w.u 2, 0, w.u 0], w.v 1⟩

/-- Unstringed local lowering operator $\sigma_2^-$ on `ZornOct R`. -/
def localLower2 (w : ZornOct R) : ZornOct R :=
  ⟨w.u 2, ![w.v 1, w.v 0, 0], ![0, 0, w.b], 0⟩

/-- Unstringed local raising operator $\sigma_2^+$ on `ZornOct R`. -/
def localRaise2 (w : ZornOct R) : ZornOct R :=
  ⟨0, ![0, 0, w.a], ![w.u 1, w.u 0, 0], w.v 2⟩

/-- **Theorem 4.2 (Failure of CAR for Unstringed Local Operators — Cross-Site Commutation):**
For distinct sites $j \neq k$, unstringed local ladder operators COMMUTE, failing the
fermionic CAR. -/
theorem local_ladder_commute_all (w : ZornOct R) :
    localRaise0 (localRaise1 w) = localRaise1 (localRaise0 w) ∧
    localRaise0 (localRaise2 w) = localRaise2 (localRaise0 w) ∧
    localRaise1 (localRaise2 w) = localRaise2 (localRaise1 w) ∧
    localLower0 (localLower1 w) = localLower1 (localLower0 w) ∧
    localLower0 (localLower2 w) = localLower2 (localLower0 w) ∧
    localLower1 (localLower2 w) = localLower2 (localLower1 w) ∧
    localLower0 (localRaise1 w) = localRaise1 (localLower0 w) ∧
    localLower0 (localRaise2 w) = localRaise2 (localLower0 w) ∧
    localLower1 (localRaise2 w) = localRaise2 (localLower1 w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [localRaise0, localRaise1, localRaise2, localLower0, localLower1, localLower2])

/-- Fermionic annihilation operator $c_0 = S_0 \circ \sigma_0^-$. -/
def jwAnnihilate0 (w : ZornOct R) : ZornOct R := jwString0 (localLower0 w)

/-- Fermionic creation operator $c_0^\dagger = S_0 \circ \sigma_0^+$. -/
def jwCreate0 (w : ZornOct R) : ZornOct R := jwString0 (localRaise0 w)

/-- Fermionic annihilation operator $c_1 = S_1 \circ \sigma_1^- = Z_0 \circ \sigma_1^-$. -/
def jwAnnihilate1 (w : ZornOct R) : ZornOct R := jwString1 (localLower1 w)

/-- Fermionic creation operator $c_1^\dagger = S_1 \circ \sigma_1^+ = Z_0 \circ \sigma_1^+$. -/
def jwCreate1 (w : ZornOct R) : ZornOct R := jwString1 (localRaise1 w)

/-- Fermionic annihilation operator $c_2 = S_2 \circ \sigma_2^- = (Z_0 \circ Z_1) \circ \sigma_2^-$. -/
def jwAnnihilate2 (w : ZornOct R) : ZornOct R := jwString2 (localLower2 w)

/-- Fermionic creation operator $c_2^\dagger = S_2 \circ \sigma_2^+ = (Z_0 \circ Z_1) \circ \sigma_2^+$. -/
def jwCreate2 (w : ZornOct R) : ZornOct R := jwString2 (localRaise2 w)

/-- **Theorem 4.3 (Fermionic Nilpotency on `ZornOct R`):**
All creation and annihilation operators square to zero: $(c_k^\dagger)^2 = 0$, $c_k^2 = 0$. -/
theorem jw_nilpotent (w : ZornOct R) :
    jwCreate0 (jwCreate0 w) = zZero ∧
    jwAnnihilate0 (jwAnnihilate0 w) = zZero ∧
    jwCreate1 (jwCreate1 w) = zZero ∧
    jwAnnihilate1 (jwAnnihilate1 w) = zZero ∧
    jwCreate2 (jwCreate2 w) = zZero ∧
    jwAnnihilate2 (jwAnnihilate2 w) = zZero := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [jwCreate0, jwAnnihilate0, jwCreate1, jwAnnihilate1, jwCreate2, jwAnnihilate2,
             jwString0, jwString1, jwString2, zSiteParity0, zSiteParity1,
             localRaise0, localLower0, localRaise1, localLower1, localRaise2, localLower2, zZero] <;>
      ring)

/-- **Theorem 4.4 (Same-Site CAR Resolution of Identity on `ZornOct R`):**
$c_k c_k^\dagger + c_k^\dagger c_k = \mathrm{id}$ for all sites $k \in \{0, 1, 2\}$. -/
theorem jw_same_site_car (w : ZornOct R) :
    zAdd (jwAnnihilate0 (jwCreate0 w)) (jwCreate0 (jwAnnihilate0 w)) = w ∧
    zAdd (jwAnnihilate1 (jwCreate1 w)) (jwCreate1 (jwAnnihilate1 w)) = w ∧
    zAdd (jwAnnihilate2 (jwCreate2 w)) (jwCreate2 (jwAnnihilate2 w)) = w := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [zAdd, jwCreate0, jwAnnihilate0, jwCreate1, jwAnnihilate1, jwCreate2, jwAnnihilate2,
             jwString0, jwString1, jwString2, zSiteParity0, zSiteParity1,
             localRaise0, localLower0, localRaise1, localLower1, localRaise2, localLower2] <;>
      ring)

/-- **Theorem 4.5 (Cross-Site CAR Anticommutation via Jordan–Wigner Strings on `ZornOct R`):**
For all $j \neq k$, $\{c_j^\dagger, c_k^\dagger\} = 0$, $\{c_j, c_k\} = 0$, and $\{c_j, c_k^\dagger\} = 0$. -/
theorem jw_cross_anticommute (w : ZornOct R) :
    zAdd (jwCreate0 (jwCreate1 w)) (jwCreate1 (jwCreate0 w)) = zZero ∧
    zAdd (jwCreate0 (jwCreate2 w)) (jwCreate2 (jwCreate0 w)) = zZero ∧
    zAdd (jwCreate1 (jwCreate2 w)) (jwCreate2 (jwCreate1 w)) = zZero ∧
    zAdd (jwAnnihilate0 (jwAnnihilate1 w)) (jwAnnihilate1 (jwAnnihilate0 w)) = zZero ∧
    zAdd (jwAnnihilate0 (jwAnnihilate2 w)) (jwAnnihilate2 (jwAnnihilate0 w)) = zZero ∧
    zAdd (jwAnnihilate1 (jwAnnihilate2 w)) (jwAnnihilate2 (jwAnnihilate1 w)) = zZero ∧
    zAdd (jwAnnihilate0 (jwCreate1 w)) (jwCreate1 (jwAnnihilate0 w)) = zZero ∧
    zAdd (jwAnnihilate0 (jwCreate2 w)) (jwCreate2 (jwAnnihilate0 w)) = zZero ∧
    zAdd (jwAnnihilate1 (jwCreate2 w)) (jwCreate2 (jwAnnihilate1 w)) = zZero := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [zAdd, jwCreate0, jwAnnihilate0, jwCreate1, jwAnnihilate1, jwCreate2, jwAnnihilate2,
             jwString0, jwString1, jwString2, zSiteParity0, zSiteParity1,
             localRaise0, localLower0, localRaise1, localLower1, localRaise2, localLower2, zZero] <;>
      ring)

/-- Fermionic number operator on site 0: $N_0 = c_0^\dagger c_0$. -/
def jwNumber0 (w : ZornOct R) : ZornOct R := jwCreate0 (jwAnnihilate0 w)

/-- Fermionic number operator on site 1: $N_1 = c_1^\dagger c_1$. -/
def jwNumber1 (w : ZornOct R) : ZornOct R := jwCreate1 (jwAnnihilate1 w)

/-- Fermionic number operator on site 2: $N_2 = c_2^\dagger c_2$. -/
def jwNumber2 (w : ZornOct R) : ZornOct R := jwCreate2 (jwAnnihilate2 w)

/-- **Theorem 4.6 (Parity–Number Duality on `ZornOct R`):**
The site parity operators satisfy $Z_k = \mathrm{id} - 2 N_k$. -/
theorem jw_parity_eq_id_sub_two_number (w : ZornOct R) :
    zSiteParity0 w = zSub w (zSmul 2 (jwNumber0 w)) ∧
    zSiteParity1 w = zSub w (zSmul 2 (jwNumber1 w)) ∧
    zSiteParity2 w = zSub w (zSmul 2 (jwNumber2 w)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [zSub, zSmul, jwNumber0, jwNumber1, jwNumber2,
             jwCreate0, jwAnnihilate0, jwCreate1, jwAnnihilate1, jwCreate2, jwAnnihilate2,
             jwString0, jwString1, jwString2, zSiteParity0, zSiteParity1, zSiteParity2,
             localRaise0, localLower0, localRaise1, localLower1, localRaise2, localLower2] <;>
      ring)

/-- Global chirality / parity operator $\Gamma = Z_0 \circ Z_1 \circ Z_2$ on `ZornOct R`. -/
def zGlobalChirality (w : ZornOct R) : ZornOct R :=
  zSiteParity0 (zSiteParity1 (zSiteParity2 w))

/-- **Theorem 4.7 (Global Chirality Grading Formula on `ZornOct R`):**
$\Gamma(a, u, v, b) = (a, -u, v, -b)$, acting as $(-1)^{\mathrm{degree}}$ on the exterior algebra. -/
theorem zGlobalChirality_eq (w : ZornOct R) :
    zGlobalChirality w = ⟨w.a, fun k => -w.u k, fun k => w.v k, -w.b⟩ := by
  refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
    (try fin_cases k) <;>
    dsimp [zGlobalChirality, zSiteParity0, zSiteParity1, zSiteParity2] <;>
    ring

/-- **Theorem 4.8 (Chirality Involution & Odd Grading Anticommutation on `ZornOct R`):**
$\Gamma^2 = \mathrm{id}$ and $\Gamma c_k^\dagger \Gamma = -c_k^\dagger$ for all sites $k$. -/
theorem zGlobalChirality_properties (w : ZornOct R) :
    zGlobalChirality (zGlobalChirality w) = w ∧
    zGlobalChirality (jwCreate0 (zGlobalChirality w)) = zNeg (jwCreate0 w) ∧
    zGlobalChirality (jwCreate1 (zGlobalChirality w)) = zNeg (jwCreate1 w) ∧
    zGlobalChirality (jwCreate2 (zGlobalChirality w)) = zNeg (jwCreate2 w) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (refine ZornOct.ext ?_ (funext fun k => ?_) (funext fun k => ?_) ?_ <;>
      (try fin_cases k) <;>
      dsimp [zNeg, zGlobalChirality, jwCreate0, jwCreate1, jwCreate2,
             jwString0, jwString1, jwString2, zSiteParity0, zSiteParity1, zSiteParity2,
             localRaise0, localLower0, localRaise1, localLower1, localRaise2, localLower2] <;>
      ring)

/-- **Theorem 4.9 (Archetype IV Jordan–Wigner CAR Master Extension on `ZornOct R`):**
Unifies the cross-site commutation of unstringed local operators, the exact CAR anticommutation
under the Jordan–Wigner strings, the resolution of identity, the parity–number duality,
and the global chirality grading into a single certified theorem. -/
theorem zorn_jordan_wigner_master (w : ZornOct R) :
    localRaise0 (localRaise1 w) = localRaise1 (localRaise0 w) ∧
    zAdd (jwCreate0 (jwCreate1 w)) (jwCreate1 (jwCreate0 w)) = zZero ∧
    zAdd (jwCreate0 (jwCreate2 w)) (jwCreate2 (jwCreate0 w)) = zZero ∧
    zAdd (jwCreate1 (jwCreate2 w)) (jwCreate2 (jwCreate1 w)) = zZero ∧
    zAdd (jwAnnihilate0 (jwCreate0 w)) (jwCreate0 (jwAnnihilate0 w)) = w ∧
    zSiteParity0 w = zSub w (zSmul 2 (jwNumber0 w)) ∧
    zGlobalChirality (jwCreate0 (zGlobalChirality w)) = zNeg (jwCreate0 w) := by
  refine ⟨(local_ladder_commute_all w).1,
          (jw_cross_anticommute w).1,
          (jw_cross_anticommute w).2.1,
          (jw_cross_anticommute w).2.2.1,
          (jw_same_site_car w).1,
          (jw_parity_eq_id_sub_two_number w).1,
          (zGlobalChirality_properties w).2.1⟩

end ArchetypeIV_ZornLeftAlternativeCl33

/-!
## Archetype V: UHF Colimit Step, KMS Trace-Cycling & Dispersion Stability
-/

section ArchetypeV_ColimitKMSAndDispersion

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Block-diagonal UHF colimit step `ι(A) = A ⊗ I₂ = fromBlocks A 0 0 A`. -/
def uhfStep (A : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks A 0 0 A

/-- **Theorem 5.1 (Exact KMS Boundary Trace-Cycling & UHF Step Trace Scaling):**
1. If `ρ_inv * ρ = 1`, then `Tr(ρ * (A * (ρ * B * ρ_inv))) = Tr(ρ * (B * A))`.
2. `Tr(uhfStep X) = 2 * Tr(X)` (the unnormalized trace scales by 2, preserving the state). -/
theorem kms_trace_cycling_and_uhfStep
    (ρ ρ_inv A B : Matrix m m ℝ) (hρ : ρ_inv * ρ = 1) :
    Matrix.trace (ρ * (A * (ρ * B * ρ_inv))) = Matrix.trace (ρ * (B * A)) ∧
    Matrix.trace (uhfStep (ρ * (B * A))) = 2 * Matrix.trace (ρ * (B * A)) := by
  constructor
  · calc
      Matrix.trace (ρ * (A * (ρ * B * ρ_inv)))
        = Matrix.trace ((ρ * A * ρ * B) * ρ_inv)     := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (ρ_inv * (ρ * A * ρ * B))     := Matrix.trace_mul_comm _ ρ_inv
      _ = Matrix.trace ((ρ_inv * ρ) * (A * ρ * B))   := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (1 * (A * ρ * B))             := by rw [hρ]
      _ = Matrix.trace ((A * ρ) * B)                 := by rw [Matrix.one_mul, Matrix.mul_assoc]
      _ = Matrix.trace (B * (A * ρ))                 := Matrix.trace_mul_comm (A * ρ) B
      _ = Matrix.trace ((B * A) * ρ)                 := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (ρ * (B * A))                 := Matrix.trace_mul_comm (B * A) ρ
  · unfold uhfStep
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, ← two_mul]

/-- **Theorem 5.2 (Completed-Square WKBJ Quadratic Non-Negativity for `Q ≥ 1`):**
For any real parameters `κ, b, c_s, k` with `c_s ≠ 0` and `b² ≤ c_s² * κ²` (`Q ≥ 1`),
`κ² - 2 * b * k + c_s² * k² = c_s² * (k - b / c_s²)² + (c_s² * κ² - b²) / c_s² ≥ 0`. -/
theorem quadratic_dispersion_nonneg_of_toomre
    (κ b c_s k : ℝ) (hcs : c_s ≠ 0) (hQ : b ^ 2 ≤ c_s ^ 2 * κ ^ 2) :
    0 ≤ κ ^ 2 - 2 * b * k + c_s ^ 2 * k ^ 2 := by
  have h_id : κ ^ 2 - 2 * b * k + c_s ^ 2 * k ^ 2 =
      c_s ^ 2 * (k - b / c_s ^ 2) ^ 2 + (c_s ^ 2 * κ ^ 2 - b ^ 2) / c_s ^ 2 := by
    field_simp [hcs]
    ring
  rw [h_id]
  have h_sq1 : 0 ≤ c_s ^ 2 * (k - b / c_s ^ 2) ^ 2 := by positivity
  have h_diff : 0 ≤ c_s ^ 2 * κ ^ 2 - b ^ 2 := sub_nonneg.mpr hQ
  have h_sq2 : 0 < c_s ^ 2 := sq_pos_of_ne_zero hcs
  have h_div : 0 ≤ (c_s ^ 2 * κ ^ 2 - b ^ 2) / c_s ^ 2 := div_nonneg h_diff (le_of_lt h_sq2)
  exact add_nonneg h_sq1 h_div

end ArchetypeV_ColimitKMSAndDispersion

end InfoGeometry.Synthesis.CanonicalPureMathPoset

end

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

/-!
# Exterior Algebra Chiral Hodge--Dirac Block Bridge

This module formalizes the exact off-diagonal chiral block decomposition of the
concrete Hodge--Dirac operator $D$:
$$D = D_+ + D_- = \begin{pmatrix} 0 & D_- \\ D_+ & 0 \end{pmatrix}$$
with respect to the chiral projectors $P_\pm = \frac{1}{2}(I \pm \Gamma)$ induced by
the chiral grading involution $\Gamma$ ($\Gamma^2 = I, \Gamma D = -D \Gamma$).

## Key Theorems:
1. **Projector Algebra:** $P_\pm^2 = P_\pm$, $P_+ P_- = P_- P_+ = 0$, $P_+ + P_- = I$.
2. **Intertwining:** $D P_+ = P_- D$ and $D P_- = P_+ D$.
3. **Chiral Arrows:** $D_+ = P_- D P_+ = D P_+ = P_- D$ and $D_- = P_+ D P_- = D P_- = P_+ D$.
4. **Diagonal Vanishing:** $P_+ D P_+ = 0$ and $P_- D P_- = 0$.
5. **Chiral Nilpotence:** $D_+^2 = 0$ and $D_-^2 = 0$ as endomorphisms.
6. **Laplacian Factorization:** $\Delta = D^2 = D_- D_+ + D_+ D_-$ with
   $\Delta_+ = P_+ \Delta P_+ = D_- D_+$ and $\Delta_- = P_- \Delta P_- = D_+ D_-$.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-! ## 1. Abstract Chiral Block Infrastructure -/

/-- Positive chiral projector P_+ = (1/2)(I + Γ) -/
def chiralProjectorPlus (Γ : Module.End ℝ M) : Module.End ℝ M :=
  (1 / 2 : ℝ) • ((1 : Module.End ℝ M) + Γ)

/-- Negative chiral projector P_- = (1/2)(I - Γ) -/
def chiralProjectorMinus (Γ : Module.End ℝ M) : Module.End ℝ M :=
  (1 / 2 : ℝ) • ((1 : Module.End ℝ M) - Γ)

theorem chiralProjectorPlus_apply (Γ : Module.End ℝ M) (x : M) :
    chiralProjectorPlus Γ x = (1 / 2 : ℝ) • (x + Γ x) := by
  simp [chiralProjectorPlus]

theorem chiralProjectorMinus_apply (Γ : Module.End ℝ M) (x : M) :
    chiralProjectorMinus Γ x = (1 / 2 : ℝ) • (x - Γ x) := by
  simp [chiralProjectorMinus]

theorem chiralProjectorPlus_sq {Γ : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorPlus Γ * chiralProjectorPlus Γ = chiralProjectorPlus Γ := by
  apply LinearMap.ext
  intro x
  have hΓ : Γ (Γ x) = x := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓ_sq
  simp only [chiralProjectorPlus_apply, Module.End.mul_apply, LinearMap.map_smul, LinearMap.map_add]
  rw [hΓ]
  module

theorem chiralProjectorMinus_sq {Γ : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorMinus Γ * chiralProjectorMinus Γ = chiralProjectorMinus Γ := by
  apply LinearMap.ext
  intro x
  have hΓ : Γ (Γ x) = x := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓ_sq
  simp only [chiralProjectorMinus_apply, Module.End.mul_apply, LinearMap.map_smul, LinearMap.map_sub]
  rw [hΓ]
  module

theorem chiralProjector_orthogonal_plus_minus {Γ : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorPlus Γ * chiralProjectorMinus Γ = 0 := by
  apply LinearMap.ext
  intro x
  have hΓ : Γ (Γ x) = x := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓ_sq
  simp only [chiralProjectorPlus_apply, chiralProjectorMinus_apply, Module.End.mul_apply,
    LinearMap.map_smul, LinearMap.map_sub, LinearMap.zero_apply]
  rw [hΓ]
  module

theorem chiralProjector_orthogonal_minus_plus {Γ : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorMinus Γ * chiralProjectorPlus Γ = 0 := by
  apply LinearMap.ext
  intro x
  have hΓ : Γ (Γ x) = x := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓ_sq
  simp only [chiralProjectorPlus_apply, chiralProjectorMinus_apply, Module.End.mul_apply,
    LinearMap.map_smul, LinearMap.map_add, LinearMap.zero_apply]
  rw [hΓ]
  module

theorem chiralProjector_sum (Γ : Module.End ℝ M) :
    chiralProjectorPlus Γ + chiralProjectorMinus Γ = 1 := by
  apply LinearMap.ext
  intro x
  simp only [chiralProjectorPlus_apply, chiralProjectorMinus_apply, LinearMap.add_apply,
    Module.End.one_apply]
  module

/-! ## 2. Intertwining and Commutation Identities -/

theorem dirac_comp_projectorPlus {Γ D : Module.End ℝ M} (hodd : Γ * D = -(D * Γ)) :
    D * chiralProjectorPlus Γ = chiralProjectorMinus Γ * D := by
  apply LinearMap.ext
  intro x
  have h : Γ (D x) = - D (Γ x) := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hodd
  simp only [chiralProjectorPlus_apply, chiralProjectorMinus_apply, Module.End.mul_apply,
    LinearMap.map_smul, LinearMap.map_add]
  rw [h]
  module

theorem dirac_comp_projectorMinus {Γ D : Module.End ℝ M} (hodd : Γ * D = -(D * Γ)) :
    D * chiralProjectorMinus Γ = chiralProjectorPlus Γ * D := by
  apply LinearMap.ext
  intro x
  have h : Γ (D x) = - D (Γ x) := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hodd
  simp only [chiralProjectorPlus_apply, chiralProjectorMinus_apply, Module.End.mul_apply,
    LinearMap.map_smul, LinearMap.map_sub]
  rw [h]
  module

/-! ## 3. Chiral Dirac Blocks -/

/-- Positive chiral Dirac block D_+ = P_- D P_+ : H_+ → H_- -/
def chiralDiracPlus (Γ D : Module.End ℝ M) : Module.End ℝ M :=
  chiralProjectorMinus Γ * D * chiralProjectorPlus Γ

/-- Negative chiral Dirac block D_- = P_+ D P_- : H_- → H_+ -/
def chiralDiracMinus (Γ D : Module.End ℝ M) : Module.End ℝ M :=
  chiralProjectorPlus Γ * D * chiralProjectorMinus Γ

theorem chiralDiracPlus_apply (Γ D : Module.End ℝ M) (x : M) :
    chiralDiracPlus Γ D x = chiralProjectorMinus Γ (D (chiralProjectorPlus Γ x)) := rfl

theorem chiralDiracMinus_apply (Γ D : Module.End ℝ M) (x : M) :
    chiralDiracMinus Γ D x = chiralProjectorPlus Γ (D (chiralProjectorMinus Γ x)) := rfl

theorem chiralDiracPlus_eq_dirac_projPlus {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracPlus Γ D = D * chiralProjectorPlus Γ := by
  apply LinearMap.ext
  intro x
  have hInter : chiralProjectorMinus Γ (D (chiralProjectorPlus Γ x)) =
      D (chiralProjectorPlus Γ (chiralProjectorPlus Γ x)) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T (chiralProjectorPlus Γ x)) (dirac_comp_projectorPlus hodd).symm
  have hP : chiralProjectorPlus Γ (chiralProjectorPlus Γ x) = chiralProjectorPlus Γ x := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T x) (chiralProjectorPlus_sq hΓ_sq)
  simp only [chiralDiracPlus_apply, Module.End.mul_apply, hInter, hP]

theorem chiralDiracPlus_eq_projMinus_dirac {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracPlus Γ D = chiralProjectorMinus Γ * D := by
  have h1 := chiralDiracPlus_eq_dirac_projPlus hΓ_sq hodd
  have h2 := dirac_comp_projectorPlus hodd
  rw [h1, h2]

theorem chiralDiracMinus_eq_dirac_projMinus {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracMinus Γ D = D * chiralProjectorMinus Γ := by
  apply LinearMap.ext
  intro x
  have hInter : chiralProjectorPlus Γ (D (chiralProjectorMinus Γ x)) =
      D (chiralProjectorMinus Γ (chiralProjectorMinus Γ x)) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T (chiralProjectorMinus Γ x)) (dirac_comp_projectorMinus hodd).symm
  have hP : chiralProjectorMinus Γ (chiralProjectorMinus Γ x) = chiralProjectorMinus Γ x := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T x) (chiralProjectorMinus_sq hΓ_sq)
  simp only [chiralDiracMinus_apply, Module.End.mul_apply, hInter, hP]

theorem chiralDiracMinus_eq_projPlus_dirac {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracMinus Γ D = chiralProjectorPlus Γ * D := by
  have h1 := chiralDiracMinus_eq_dirac_projMinus hΓ_sq hodd
  have h2 := dirac_comp_projectorMinus hodd
  rw [h1, h2]

/-! ## 4. Diagonal Vanishing -/

theorem chiralDirac_diagonal_plus_zero {Γ D : Module.End ℝ M} (hodd : Γ * D = -(D * Γ))
    (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorPlus Γ * D * chiralProjectorPlus Γ = 0 := by
  calc chiralProjectorPlus Γ * D * chiralProjectorPlus Γ
    _ = chiralProjectorPlus Γ * (D * chiralProjectorPlus Γ) := by noncomm_ring
    _ = chiralProjectorPlus Γ * (chiralProjectorMinus Γ * D) := by rw [dirac_comp_projectorPlus hodd]
    _ = (chiralProjectorPlus Γ * chiralProjectorMinus Γ) * D := by noncomm_ring
    _ = 0 * D := by rw [chiralProjector_orthogonal_plus_minus hΓ_sq]
    _ = 0 := by rw [zero_mul]

theorem chiralDirac_diagonal_minus_zero {Γ D : Module.End ℝ M} (hodd : Γ * D = -(D * Γ))
    (hΓ_sq : Γ * Γ = 1) :
    chiralProjectorMinus Γ * D * chiralProjectorMinus Γ = 0 := by
  calc chiralProjectorMinus Γ * D * chiralProjectorMinus Γ
    _ = chiralProjectorMinus Γ * (D * chiralProjectorMinus Γ) := by noncomm_ring
    _ = chiralProjectorMinus Γ * (chiralProjectorPlus Γ * D) := by rw [dirac_comp_projectorMinus hodd]
    _ = (chiralProjectorMinus Γ * chiralProjectorPlus Γ) * D := by noncomm_ring
    _ = 0 * D := by rw [chiralProjector_orthogonal_minus_plus hΓ_sq]
    _ = 0 := by rw [zero_mul]

/-! ## 5. Exact Off-Diagonal Decomposition -/

theorem chiralDirac_decomposition {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    D = chiralDiracPlus Γ D + chiralDiracMinus Γ D := by
  rw [chiralDiracPlus_eq_dirac_projPlus hΓ_sq hodd,
    chiralDiracMinus_eq_dirac_projMinus hΓ_sq hodd]
  calc D = D * 1 := by rw [mul_one]
    _ = D * (chiralProjectorPlus Γ + chiralProjectorMinus Γ) := by rw [chiralProjector_sum]
    _ = D * chiralProjectorPlus Γ + D * chiralProjectorMinus Γ := by noncomm_ring

/-! ## 6. Chiral Block Nilpotence -/

theorem chiralDiracPlus_sq_zero {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracPlus Γ D * chiralDiracPlus Γ D = 0 := by
  have h1 := chiralDiracPlus_eq_projMinus_dirac hΓ_sq hodd
  have h2 := chiralDiracPlus_eq_dirac_projPlus hΓ_sq hodd
  have hProd : chiralDiracPlus Γ D * chiralDiracPlus Γ D =
      (chiralProjectorMinus Γ * D) * (D * chiralProjectorPlus Γ) := by
    have hA : chiralDiracPlus Γ D * chiralDiracPlus Γ D =
        (chiralProjectorMinus Γ * D) * chiralDiracPlus Γ D :=
      congrArg (fun T => T * chiralDiracPlus Γ D) h1
    have hB : (chiralProjectorMinus Γ * D) * chiralDiracPlus Γ D =
        (chiralProjectorMinus Γ * D) * (D * chiralProjectorPlus Γ) :=
      congrArg (fun T => (chiralProjectorMinus Γ * D) * T) h2
    exact hA.trans hB
  calc chiralDiracPlus Γ D * chiralDiracPlus Γ D
    _ = (chiralProjectorMinus Γ * D) * (D * chiralProjectorPlus Γ) := hProd
    _ = chiralProjectorMinus Γ * D * (D * chiralProjectorPlus Γ) := by noncomm_ring
    _ = chiralProjectorMinus Γ * (D * (D * chiralProjectorPlus Γ)) := by noncomm_ring
    _ = chiralProjectorMinus Γ * (D * (chiralProjectorMinus Γ * D)) := by rw [dirac_comp_projectorPlus hodd]
    _ = chiralProjectorMinus Γ * ((D * chiralProjectorMinus Γ) * D) := by noncomm_ring
    _ = chiralProjectorMinus Γ * ((chiralProjectorPlus Γ * D) * D) := by rw [dirac_comp_projectorMinus hodd]
    _ = (chiralProjectorMinus Γ * chiralProjectorPlus Γ) * (D * D) := by noncomm_ring
    _ = 0 * (D * D) := by rw [chiralProjector_orthogonal_minus_plus hΓ_sq]
    _ = 0 := by rw [zero_mul]

theorem chiralDiracMinus_sq_zero {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralDiracMinus Γ D * chiralDiracMinus Γ D = 0 := by
  have h1 := chiralDiracMinus_eq_projPlus_dirac hΓ_sq hodd
  have h2 := chiralDiracMinus_eq_dirac_projMinus hΓ_sq hodd
  have hProd : chiralDiracMinus Γ D * chiralDiracMinus Γ D =
      (chiralProjectorPlus Γ * D) * (D * chiralProjectorMinus Γ) := by
    have hA : chiralDiracMinus Γ D * chiralDiracMinus Γ D =
        (chiralProjectorPlus Γ * D) * chiralDiracMinus Γ D :=
      congrArg (fun T => T * chiralDiracMinus Γ D) h1
    have hB : (chiralProjectorPlus Γ * D) * chiralDiracMinus Γ D =
        (chiralProjectorPlus Γ * D) * (D * chiralProjectorMinus Γ) :=
      congrArg (fun T => (chiralProjectorPlus Γ * D) * T) h2
    exact hA.trans hB
  calc chiralDiracMinus Γ D * chiralDiracMinus Γ D
    _ = (chiralProjectorPlus Γ * D) * (D * chiralProjectorMinus Γ) := hProd
    _ = chiralProjectorPlus Γ * D * (D * chiralProjectorMinus Γ) := by noncomm_ring
    _ = chiralProjectorPlus Γ * (D * (D * chiralProjectorMinus Γ)) := by noncomm_ring
    _ = chiralProjectorPlus Γ * (D * (chiralProjectorPlus Γ * D)) := by rw [dirac_comp_projectorMinus hodd]
    _ = chiralProjectorPlus Γ * ((D * chiralProjectorPlus Γ) * D) := by noncomm_ring
    _ = chiralProjectorPlus Γ * ((chiralProjectorMinus Γ * D) * D) := by rw [dirac_comp_projectorPlus hodd]
    _ = (chiralProjectorPlus Γ * chiralProjectorMinus Γ) * (D * D) := by noncomm_ring
    _ = 0 * (D * D) := by rw [chiralProjector_orthogonal_plus_minus hΓ_sq]
    _ = 0 := by rw [zero_mul]

/-! ## 7. Chiral Laplacian Factorization -/

/-- Positive chiral Laplacian Δ_+ = P_+ Δ P_+ -/
def chiralLaplacianPlus (Γ Δ : Module.End ℝ M) : Module.End ℝ M :=
  chiralProjectorPlus Γ * Δ * chiralProjectorPlus Γ

/-- Negative chiral Laplacian Δ_- = P_- Δ P_- -/
def chiralLaplacianMinus (Γ Δ : Module.End ℝ M) : Module.End ℝ M :=
  chiralProjectorMinus Γ * Δ * chiralProjectorMinus Γ

theorem laplacian_plus_eq_minus_plus {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralLaplacianPlus Γ (D * D) = chiralDiracMinus Γ D * chiralDiracPlus Γ D := by
  dsimp [chiralLaplacianPlus]
  rw [chiralDiracMinus_eq_projPlus_dirac hΓ_sq hodd,
    chiralDiracPlus_eq_dirac_projPlus hΓ_sq hodd]
  noncomm_ring

theorem laplacian_minus_eq_plus_minus {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    chiralLaplacianMinus Γ (D * D) = chiralDiracPlus Γ D * chiralDiracMinus Γ D := by
  dsimp [chiralLaplacianMinus]
  rw [chiralDiracPlus_eq_projMinus_dirac hΓ_sq hodd,
    chiralDiracMinus_eq_dirac_projMinus hΓ_sq hodd]
  noncomm_ring

theorem dirac_sq_eq_chiral_sum {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    D * D = chiralDiracMinus Γ D * chiralDiracPlus Γ D +
            chiralDiracPlus Γ D * chiralDiracMinus Γ D := by
  have hdec := chiralDirac_decomposition hΓ_sq hodd
  calc D * D = (chiralDiracPlus Γ D + chiralDiracMinus Γ D) *
               (chiralDiracPlus Γ D + chiralDiracMinus Γ D) := by rw [← hdec]
    _ = chiralDiracPlus Γ D * chiralDiracPlus Γ D +
        chiralDiracPlus Γ D * chiralDiracMinus Γ D +
        chiralDiracMinus Γ D * chiralDiracPlus Γ D +
        chiralDiracMinus Γ D * chiralDiracMinus Γ D := by noncomm_ring
    _ = 0 + chiralDiracPlus Γ D * chiralDiracMinus Γ D +
        chiralDiracMinus Γ D * chiralDiracPlus Γ D + 0 := by
        rw [chiralDiracPlus_sq_zero hΓ_sq hodd, chiralDiracMinus_sq_zero hΓ_sq hodd]
    _ = chiralDiracMinus Γ D * chiralDiracPlus Γ D +
        chiralDiracPlus Γ D * chiralDiracMinus Γ D := by abel

theorem laplacian_chiral_block_decomposition {Γ D : Module.End ℝ M} (hΓ_sq : Γ * Γ = 1)
    (hodd : Γ * D = -(D * Γ)) :
    D * D = chiralLaplacianPlus Γ (D * D) + chiralLaplacianMinus Γ (D * D) := by
  have h1 := laplacian_plus_eq_minus_plus hΓ_sq hodd
  have h2 := laplacian_minus_eq_plus_minus hΓ_sq hodd
  have hSum := dirac_sq_eq_chiral_sum hΓ_sq hodd
  rw [h1, h2, hSum]

/-! ## 8. Concrete Doubled Exterior 3 Specialization -/

abbrev concreteProjectorPlus3 : DoubledExterior3End :=
  chiralProjectorPlus concreteChirality3

abbrev concreteProjectorMinus3 : DoubledExterior3End :=
  chiralProjectorMinus concreteChirality3

abbrev concreteChiralDiracPlus3 (v : V3) (φ : Module.Dual ℝ V3) : DoubledExterior3End :=
  chiralDiracPlus concreteChirality3 (concreteDirac3 v φ)

abbrev concreteChiralDiracMinus3 (v : V3) (φ : Module.Dual ℝ V3) : DoubledExterior3End :=
  chiralDiracMinus concreteChirality3 (concreteDirac3 v φ)

theorem concrete_chiralDirac_decomposition (v : V3) (φ : Module.Dual ℝ V3) :
    concreteDirac3 v φ =
      concreteChiralDiracPlus3 v φ + concreteChiralDiracMinus3 v φ :=
  chiralDirac_decomposition concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concrete_chiralDiracPlus_sq_zero (v : V3) (φ : Module.Dual ℝ V3) :
    concreteChiralDiracPlus3 v φ * concreteChiralDiracPlus3 v φ = 0 :=
  chiralDiracPlus_sq_zero concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concrete_chiralDiracMinus_sq_zero (v : V3) (φ : Module.Dual ℝ V3) :
    concreteChiralDiracMinus3 v φ * concreteChiralDiracMinus3 v φ = 0 :=
  chiralDiracMinus_sq_zero concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concrete_laplacian_chiral_block_decomposition (v : V3) (φ : Module.Dual ℝ V3) :
    concreteLaplacian3 v φ =
      chiralLaplacianPlus concreteChirality3 (concreteLaplacian3 v φ) +
      chiralLaplacianMinus concreteChirality3 (concreteLaplacian3 v φ) := by
  rw [← concreteDirac3_sq v φ]
  exact laplacian_chiral_block_decomposition concreteChirality3_sq (concreteChirality3_odd v φ)

end InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge

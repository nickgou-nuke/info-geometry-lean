import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks
import InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge

/-!
# Concrete Doubled Chiral Hodge Blocks and Hestenes Linear Intertwining

This module formalizes the exact 2x2 chiral decomposition of the doubled
Hodge-Dirac operator $D^{(2)} = D_+^{(2)} + D_-^{(2)}$ on $\mathrm{DoubledExterior3} = \mathrm{Exterior3} \times \mathrm{Exterior3}$,
proves that both chiral arrows are nilpotents:
$$(D_+^{(2)})^2 = 0, \qquad (D_-^{(2)})^2 = 0,$$
and verifies that each chiral arrow is strictly Hestenes-complex linear:
$$[K, D_\pm^{(2)}] = 0 \qquad \text{and} \qquad [\Phi_K(t), D_\pm^{(2)}] = 0.$$
-/

noncomputable section

namespace InfoGeometry.Canonical.DoubledChiralHodgeBlocksBridge

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks
open InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-- 🏆 THEOREM 1: Exact Chiral Splitting D^(2) = D_+^(2) + D_-^(2) -/
theorem doubledDirac_split (v : V3) (φ : Module.Dual ℝ V3) :
    concreteDirac3 v φ = concreteChiralDiracPlus3 v φ + concreteChiralDiracMinus3 v φ :=
  concrete_chiralDirac_decomposition v φ

/-- 🏆 THEOREM 2: Nilpotency of Chiral Arrows (D_+^(2))² = 0 and (D_-^(2))² = 0 -/
theorem doubledDiracPlus_sq_zero (v : V3) (φ : Module.Dual ℝ V3) :
    concreteChiralDiracPlus3 v φ * concreteChiralDiracPlus3 v φ = 0 :=
  concrete_chiralDiracPlus_sq_zero v φ

theorem doubledDiracMinus_sq_zero (v : V3) (φ : Module.Dual ℝ V3) :
    concreteChiralDiracMinus3 v φ * concreteChiralDiracMinus3 v φ = 0 :=
  concrete_chiralDiracMinus_sq_zero v φ

/-- 🏆 THEOREM 3: Hestenes Phase Linearity of Chiral Arrows [K, D_±^(2)] = 0 -/
theorem hestenesPhase_commutes_doubledDiracPlus (v : V3) (φ : Module.Dual ℝ V3) :
    hestenesPhase3 * concreteChiralDiracPlus3 v φ =
      concreteChiralDiracPlus3 v φ * hestenesPhase3 :=
  concrete_hestenes_commutes_chiralDiracPlus v φ

theorem hestenesPhase_commutes_doubledDiracMinus (v : V3) (φ : Module.Dual ℝ V3) :
    hestenesPhase3 * concreteChiralDiracMinus3 v φ =
      concreteChiralDiracMinus3 v φ * hestenesPhase3 :=
  concrete_hestenes_commutes_chiralDiracMinus v φ

/-- 🏆 THEOREM 4: Chiral Laplacians Δ_±^(2) = D_∓^(2) D_±^(2) -/
def doubledChiralLaplacianPlus (v : V3) (φ : Module.Dual ℝ V3) : DoubledExterior3End :=
  concreteChiralDiracMinus3 v φ * concreteChiralDiracPlus3 v φ

def doubledChiralLaplacianMinus (v : V3) (φ : Module.Dual ℝ V3) : DoubledExterior3End :=
  concreteChiralDiracPlus3 v φ * concreteChiralDiracMinus3 v φ

theorem doubledChiralLaplacian_sum (v : V3) (φ : Module.Dual ℝ V3) :
    concreteLaplacian3 v φ =
      doubledChiralLaplacianPlus v φ + doubledChiralLaplacianMinus v φ := by
  have hdec := concrete_laplacian_chiral_block_decomposition v φ
  have hsq := (concreteDirac3_sq v φ).symm
  dsimp [doubledChiralLaplacianPlus, doubledChiralLaplacianMinus]
  rw [hsq] at hdec ⊢
  have hPlus := laplacian_plus_eq_minus_plus concreteChirality3_sq (concreteChirality3_odd v φ)
  have hMinus := laplacian_minus_eq_plus_minus concreteChirality3_sq (concreteChirality3_odd v φ)
  rw [hdec]
  dsimp [concreteChiralDiracPlus3, concreteChiralDiracMinus3]
  rw [hPlus, hMinus]

/-- 🏆 THEOREM 5: Hestenes Flow Intertwines Chiral Arrows [Φ_K(t), D_±^(2)] = 0 -/
theorem hestenesFlow_intertwines_doubledDiracPlus (v : V3) (φ : Module.Dual ℝ V3) (t : ℝ) :
    hestenesPhaseFlow hestenesPhase3 t * concreteChiralDiracPlus3 v φ =
      concreteChiralDiracPlus3 v φ * hestenesPhaseFlow hestenesPhase3 t := by
  dsimp [hestenesPhaseFlow]
  calc ((Real.cos t) • (1 : DoubledExterior3End) + (Real.sin t) • hestenesPhase3) *
       concreteChiralDiracPlus3 v φ
    _ = (Real.cos t) • concreteChiralDiracPlus3 v φ +
        (Real.sin t) • (hestenesPhase3 * concreteChiralDiracPlus3 v φ) := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = (Real.cos t) • concreteChiralDiracPlus3 v φ +
        (Real.sin t) • (concreteChiralDiracPlus3 v φ * hestenesPhase3) := by
      rw [hestenesPhase_commutes_doubledDiracPlus]
    _ = concreteChiralDiracPlus3 v φ *
        ((Real.cos t) • (1 : DoubledExterior3End) + (Real.sin t) • hestenesPhase3) := by
      rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

theorem hestenesFlow_intertwines_doubledDiracMinus (v : V3) (φ : Module.Dual ℝ V3) (t : ℝ) :
    hestenesPhaseFlow hestenesPhase3 t * concreteChiralDiracMinus3 v φ =
      concreteChiralDiracMinus3 v φ * hestenesPhaseFlow hestenesPhase3 t := by
  dsimp [hestenesPhaseFlow]
  calc ((Real.cos t) • (1 : DoubledExterior3End) + (Real.sin t) • hestenesPhase3) *
       concreteChiralDiracMinus3 v φ
    _ = (Real.cos t) • concreteChiralDiracMinus3 v φ +
        (Real.sin t) • (hestenesPhase3 * concreteChiralDiracMinus3 v φ) := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = (Real.cos t) • concreteChiralDiracMinus3 v φ +
        (Real.sin t) • (concreteChiralDiracMinus3 v φ * hestenesPhase3) := by
      rw [hestenesPhase_commutes_doubledDiracMinus]
    _ = concreteChiralDiracMinus3 v φ *
        ((Real.cos t) • (1 : DoubledExterior3End) + (Real.sin t) • hestenesPhase3) := by
      rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

/-! ## The composite chiral-complex operator

The commuting relations `K² = -I`, `Γ² = I`, and `[K, Γ] = 0` do not
present a pair of Clifford generators for `Cl(1,1)`.  Their product is the
canonical second complex structure `Jχ = KΓ`; it commutes with chirality,
while it anticommutes with the odd Hodge--Dirac operator.
-/

def hestenesChiralComplex3 : DoubledExterior3End :=
  chiralComplexStructure hestenesPhase3 concreteChirality3

theorem hestenesChiralComplex3_sq :
    hestenesChiralComplex3 * hestenesChiralComplex3 =
      -(1 : DoubledExterior3End) := by
  exact concrete_chiralComplexStructure_sq

theorem hestenesChiralComplex3_commutes_chirality :
    hestenesChiralComplex3 * concreteChirality3 =
      concreteChirality3 * hestenesChiralComplex3 := by
  dsimp [hestenesChiralComplex3, chiralComplexStructure]
  rw [mul_assoc, concreteChirality3_sq, mul_one]
  rw [← concrete_chirality3_commutes_hestenesPhase3, ← mul_assoc,
    concreteChirality3_sq, one_mul]

theorem hestenesChiralComplex3_anticommutes_dirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    hestenesChiralComplex3 * concreteDirac3 v φ =
      -(concreteDirac3 v φ * hestenesChiralComplex3) := by
  exact concrete_chiralComplexStructure_anticomm_dirac v φ

end InfoGeometry.Canonical.DoubledChiralHodgeBlocksBridge

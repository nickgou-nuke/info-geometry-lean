import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55ThreeColorChiralSums
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Algebra.GellMannBridge
import InfoGeometry.Lie.SplitOctonionGellMannCartan
import InfoGeometry.Lie.SplitOctonionEllCircularCAR
import InfoGeometry.Physics.ColorCARStandardModel
import InfoGeometry.Physics.FureyCharges
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Canonical.ZornOctonionAnyonGellMannBridge
import InfoGeometry.Canonical.FractionalAnyonTopologicalSpin
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Native SU(3) / colour-CAR / anyon structural bridge for the QCD lane

This module exposes theorem owners that already existed in the main
`InfoGeometry` library and promotes the theorem-safe Furey generation/charge
readout formerly available only in the downstream `proofs` package.

Closed here:

* concrete Gell-Mann `3 × 3` commutator identities and their bridge to the
  anti-Hermitian `su (Fin 3)` basis;
* exact Gell-Mann Cartan weights on the split-octonion circular root channels;
* native three-colour `Cl(5,5)` CAR closure and the matching circular Zorn CAR;
* the finite eight-generator Furey-style generation span;
* the finite one-third occupation spectrum `{0, 1/3, 2/3, 1}`;
* the finite `A₂/S₃` colour Weyl braid relation;
* the finite parafermion-style Artin braid relation;
* Zorn null-boundary colour-pairing trace identities and gauge-conjugation
  trace invariance;
* generic unitary anyon double-braid monodromy.

These are algebraic/representation-theoretic statements. They do not identify
these carriers with physical QCD quark fields, prove confinement, prove that
`fureyGeneration` is a minimal left ideal, or identify `fureyOccupationCharge`
with physical electric charge.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDColorCARAnyonBridge

open Matrix
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Algebra.Bridge
open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Physics.ColorCARStandardModel
open InfoGeometry.Physics.FureyCharges
open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Topology.Parafermion

/-- A concrete `su(3)`/Gell-Mann packet already owned by the repository. -/
theorem gellMann_su3_packet :
    gl1 * gl2 - gl2 * gl1 = (2 * Complex.I) • gl3 ∧
      gl3 * gl8 = gl8 * gl3 ∧
      (((InfoGeometry.Algebra.GellMann.gellMann1 :
          InfoGeometry.Algebra.su (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ) =
        Complex.I • gl1) :=
  ⟨gl1_comm_gl2, gl3_comm_gl8, gellMann1_eq_gl1⟩

/-- The split-octonion circular root channels carry the exact Gell-Mann Cartan
weights `±k_i`. -/
theorem split_octonion_gellMann_weight_packet
    (K1 K2 : ℝ) (i : Fin 3) :
    InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd
        (gellMannCartan K1 K2).1
        (cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i)) =
      (gellMannCartan K1 K2).1 i •
        cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus i) ∧
    InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd
        (gellMannCartan K1 K2).1
        (cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i)) =
      -((gellMannCartan K1 K2).1 i) •
        cartesianZornLinearEquiv
          (InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus i) :=
  ⟨axialCartanEnd_gellMann_rootPlus K1 K2 i,
    axialCartanEnd_gellMann_rootMinus K1 K2 i⟩

/-- Circular Zorn CAR and native `Cl(5,5)` three-colour CAR coexist with the
same three-valued colour index. -/
theorem circular_and_cl55_color_car_packet (a b : Fin 3) :
    cartesianZornLinearEquiv (rootPlus a) * cartesianZornLinearEquiv (rootPlus a) = 0 ∧
    cartesianZornLinearEquiv (rootMinus a) * cartesianZornLinearEquiv (rootMinus a) = 0 ∧
    cartesianZornLinearEquiv (rootPlus a) * cartesianZornLinearEquiv (rootMinus b) +
        cartesianZornLinearEquiv (rootMinus b) * cartesianZornLinearEquiv (rootPlus a) =
      (if a = b then 1 else 0) ∧
    (InfoGeometry.Clifford.Clifford55.chiralPlusSum *
          InfoGeometry.Clifford.Clifford55.chiralPlusSum = 0 ∧
      InfoGeometry.Clifford.Clifford55.chiralMinusSum *
          InfoGeometry.Clifford.Clifford55.chiralMinusSum = 0) := by
  refine ⟨cartesianZorn_rootPlus_sq a, cartesianZorn_rootMinus_sq a,
    cartesianZorn_root_anticommutator_if a b, ?_⟩
  exact ⟨InfoGeometry.Clifford.Clifford55.chiralPlusSum_sq,
    InfoGeometry.Clifford.Clifford55.chiralMinusSum_sq⟩

/-- The promoted finite Furey-style generation contains the vacuum and all
three one-creation colour states. This is a span-membership packet, not a
minimal-left-ideal theorem. -/
theorem furey_generation_packet :
    vacuum ∈ fureyGeneration ∧
      carCre0 ∈ fureyGeneration ∧
      carCre1 ∈ fureyGeneration ∧
      carCre2 ∈ fureyGeneration := by
  constructor
  · apply Submodule.subset_span
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl trivial
  constructor
  · apply Submodule.subset_span
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl trivial)
  constructor
  · apply Submodule.subset_span
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inl trivial))
  · apply Submodule.subset_span
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inr (Or.inl trivial)))

/-- The finite Furey occupation readout has projector number operators and the
exact scalar spectrum `{0, 1/3, 2/3, 1}`. -/
theorem furey_charge_packet :
    (∀ i : Fin 3, fureyNumber i * fureyNumber i = fureyNumber i) ∧
    (∀ w : Occupation3,
      fureyOccupationCharge w = 0 ∨
      fureyOccupationCharge w = (1 / 3 : ℚ) ∨
      fureyOccupationCharge w = (2 / 3 : ℚ) ∨
      fureyOccupationCharge w = 1) :=
  furey_charge_algebraic_spine

/-- The finite colour Weyl model and the explicit parafermion-style matrices
both satisfy an Artin braid relation. -/
theorem color_weyl_and_parafermion_braid_packet (t : ℂ) :
    swapRGPerm * swapGBPerm * swapRGPerm =
        swapGBPerm * swapRGPerm * swapGBPerm ∧
    sigma_1 t * sigma_2 t * sigma_1 t =
        sigma_2 t * sigma_1 t * sigma_2 t :=
  ⟨SU3ColorWeyl_braid_relation, su3_parafermion_braiding t⟩

/-- The Zorn `Q_k = E_k + F_k` generators square to the Zorn identity and the
associated unnormalised braid elements have explicit two-sided inverses. -/
theorem zorn_majorana_braid_packet (k : Fin 3) :
    zornMul (Q_k k) (Q_k k) = I_zorn ∧
      zornMul (unnormalizedR_k k) (unnormalizedR_k_inv k) = I_zorn ∧
      zornMul (unnormalizedR_k_inv k) (unnormalizedR_k k) = I_zorn :=
  ⟨Q_k_sq k,
    unnormalizedR_k_mul_unnormalizedR_k_inv k,
    unnormalizedR_k_inv_mul_unnormalizedR_k k⟩

/-- Null-boundary colour pairing and gauge-conjugation trace invariance from the
existing Zorn/anyon owner. -/
theorem zorn_null_color_gauge_packet
    (U : ZornOctonionAnyon.ZornCell.ColorGauge)
    (v w : Fin 3 → ℂ)
    (hnull : ZornOctonionAnyon.ZornCell.colorDot v w = 0) :
    Matrix.trace (ZornOctonionAnyon.ZornCell.colorTensorMatrix v w) =
        ZornOctonionAnyon.ZornCell.colorDot v w ∧
    Matrix.trace (ZornOctonionAnyon.ZornCell.colorTensorMatrix v w) = 0 ∧
    Matrix.trace
        ((U : Matrix (Fin 3) (Fin 3) ℂ) *
          ZornOctonionAnyon.ZornCell.colorTensorMatrix v w *
          ((U⁻¹ : ZornOctonionAnyon.ZornCell.ColorGauge) :
            Matrix (Fin 3) (Fin 3) ℂ)) =
      Matrix.trace (ZornOctonionAnyon.ZornCell.colorTensorMatrix v w) :=
  ⟨ZornOctonionAnyon.ZornCell.color_tensor_trace_eq_dot v w,
    ZornOctonionAnyon.ZornCell.null_boundary_color_pairing_zero v w hnull,
    ZornOctonionAnyon.ZornCell.gellmann_su3_gauge_trace_invariant U v w⟩

/-- Generic unitary anyon monodromy packet, kept independent of any physical
identification of the colour/Zorn braid carriers. -/
theorem anyon_double_braid_packet
    {n : ℕ} [DecidableEq (Fin n)]
    (sys : FractionalAnyonSpin.AnyonBraidSystem n) :
    sys.doubleBraidingOperator * sys.doubleBraidingOperator.conjTranspose = 1 ∧
      Matrix.trace
          (sys.doubleBraidingOperator *
            sys.doubleBraidingOperator.conjTranspose) = (n : ℂ) :=
  ⟨sys.double_braiding_unitary, sys.double_braiding_trace_normalized⟩

end InfoGeometry.Physics.QCDColorCARAnyonBridge

end noncomputable section

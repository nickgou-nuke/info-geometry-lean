import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Canonical.HodgeFockEmbeddingBridge
import InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge

/-!
# Concrete Hestenes carrier inside the Cl(5,5) master carrier

This owner records the honest carrier-level part of the proposed vertical wire.
The doubled three-mode exterior carrier has real dimension `16`, whereas the
five-mode master spinor carrier has real dimension `32`; consequently the
canonical map here is an injective linear embedding, not an equivalence.

The second, analytic/operator-level identification with the master CAR
operators is deliberately not claimed here.  The first-slot Dirac transport
uses the already verified tensor-factor intertwiner from
`HodgeFockEmbeddingBridge`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.HodgeFockEmbeddingBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge

abbrev Spinor8 := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev Spinor32 := InfoGeometry.Algebra.FiniteSpin.Vec32R
abbrev DoubledSpinor8 := Spinor8 × Spinor8

noncomputable def exteriorToSpinor8 : Exterior3 ≃ₗ[ℝ] Spinor8 :=
  exterior3SplitOctonionCoordinateEquiv

def transportExteriorEnd (T : Exterior3End) : Module.End ℝ Spinor8 :=
  exteriorToSpinor8.toLinearMap.comp (T.comp exteriorToSpinor8.symm.toLinearMap)

def transportedConcreteDirac3 (v : V3) (φ : Module.Dual ℝ V3) :
    Module.End ℝ Spinor8 :=
  transportExteriorEnd (exteriorHodgeDirac3 v φ)

def transportedConcreteDiracMatrix (v : V3) (φ : Module.Dual ℝ V3) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix' (transportedConcreteDirac3 v φ)

theorem transportedConcreteDirac3_apply
    (v : V3) (φ : Module.Dual ℝ V3) (x : Exterior3) :
    transportedConcreteDirac3 v φ (exteriorToSpinor8 x) =
      exteriorToSpinor8 (exteriorHodgeDirac3 v φ x) := by
  simp [transportedConcreteDirac3, transportExteriorEnd]

theorem transportedConcreteDiracMatrix_mulVec
    (v : V3) (φ : Module.Dual ℝ V3) (x : Spinor8) :
    Matrix.mulVec (transportedConcreteDiracMatrix v φ) x =
      transportedConcreteDirac3 v φ x := by
  simpa [transportedConcreteDiracMatrix] using
    (LinearMap.toMatrix'_mulVec (transportedConcreteDirac3 v φ) x).symm

def fockEmbeddingAt (a : Fin 4) (v : Spinor8) : Spinor32 :=
  fun i =>
    let p := fin32Equiv i
    if p.2 = a then v p.1 else 0

def fockEmbeddingAtLinear (a : Fin 4) : Spinor8 →ₗ[ℝ] Spinor32 where
  toFun := fockEmbeddingAt a
  map_add' v w := by
    ext i
    by_cases h : (fin32Equiv i).2 = a <;> simp [fockEmbeddingAt, h]
  map_smul' c v := by
    ext i
    simp [fockEmbeddingAt]

def doubledFockEmbedding : DoubledSpinor8 →ₗ[ℝ] Spinor32 :=
  (fockEmbeddingAtLinear 0).comp (LinearMap.fst ℝ Spinor8 Spinor8)
    + (fockEmbeddingAtLinear 1).comp (LinearMap.snd ℝ Spinor8 Spinor8)

theorem fockEmbeddingAt_zero_eq_fockEmbedding (v : Spinor8) :
    fockEmbeddingAt 0 v = fockEmbedding v := by
  funext i
  simp [fockEmbeddingAt, fockEmbedding]

theorem doubledFockEmbedding_apply (x : DoubledSpinor8) :
    doubledFockEmbedding x = fockEmbeddingAt 0 x.1 + fockEmbeddingAt 1 x.2 := by
  simp [doubledFockEmbedding, fockEmbeddingAtLinear, LinearMap.add_apply,
    LinearMap.comp_apply]

theorem doubledFockEmbedding_injective :
    Function.Injective doubledFockEmbedding := by
  intro x y hxy
  apply Prod.ext
  · funext i
    have hi := congrArg (fun z : Spinor32 => z (fin32Equiv.symm (i, 0))) hxy
    simpa [doubledFockEmbedding_apply, fockEmbeddingAt] using hi
  · funext i
    have hi := congrArg (fun z : Spinor32 => z (fin32Equiv.symm (i, 1))) hxy
    simpa [doubledFockEmbedding_apply, fockEmbeddingAt] using hi

theorem exteriorToSpinor8_injective :
    Function.Injective exteriorToSpinor8 :=
  exteriorToSpinor8.injective

theorem fockEmbeddingAt_one_dirac_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (v : Spinor8) :
    Matrix.mulVec (dirac32 D) (fockEmbeddingAt 1 v) =
      fockEmbeddingAt 1 (dirac8 D v) := by
  ext i
  dsimp [fockEmbeddingAt, dirac8, dirac32, Matrix.mulVec, dotProduct]
  have hequiv :
      ∑ j : Fin 32,
          (if (fin32Equiv i).2 = (fin32Equiv j).2 then
              D (fin32Equiv i).1 (fin32Equiv j).1 else 0) *
            (if (fin32Equiv j).2 = (1 : Fin 4) then
              v (fin32Equiv j).1 else 0) =
        ∑ p : Fin 8 × Fin 4,
          (if (fin32Equiv i).2 = (fin32Equiv (fin32Equiv.symm p)).2 then
              D (fin32Equiv i).1 (fin32Equiv (fin32Equiv.symm p)).1 else 0) *
            (if (fin32Equiv (fin32Equiv.symm p)).2 = (1 : Fin 4) then
              v (fin32Equiv (fin32Equiv.symm p)).1 else 0) := by
    exact ((fin32Equiv).symm.sum_comp _).symm
  rw [hequiv]
  simp_rw [fin32Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  have hinner (m : Fin 8) :
      ∑ b : Fin 4,
          (if (fin32Equiv i).2 = b then D (fin32Equiv i).1 m else 0) *
            (if b = (1 : Fin 4) then v m else 0) =
        (if (fin32Equiv i).2 = (1 : Fin 4) then
            D (fin32Equiv i).1 m * v m else 0) := by
    have hb0 :
        (if (fin32Equiv i).2 = (0 : Fin 4) then D (fin32Equiv i).1 m else 0) *
            (if (0 : Fin 4) = (1 : Fin 4) then v m else 0) = 0 := by
      norm_num
    have hb1 :
        (if (fin32Equiv i).2 = (1 : Fin 4) then D (fin32Equiv i).1 m else 0) *
            (if (1 : Fin 4) = (1 : Fin 4) then v m else 0) =
          (if (fin32Equiv i).2 = (1 : Fin 4) then
              D (fin32Equiv i).1 m * v m else 0) := by
      simp
    have hb2 :
        (if (fin32Equiv i).2 = (2 : Fin 4) then D (fin32Equiv i).1 m else 0) *
            (if (2 : Fin 4) = (1 : Fin 4) then v m else 0) = 0 := by
      simp
    have hb3 :
        (if (fin32Equiv i).2 = (3 : Fin 4) then D (fin32Equiv i).1 m else 0) *
            (if (3 : Fin 4) = (1 : Fin 4) then v m else 0) = 0 := by
      simp
    rw [Fin.sum_univ_four, hb0, hb1, hb2, hb3]
    ring
  simp_rw [hinner]
  split_ifs with h
  · rfl
  · simp

def doubledDirac8 (D : Matrix (Fin 8) (Fin 8) ℝ) :
    DoubledSpinor8 →ₗ[ℝ] DoubledSpinor8 where
  toFun x := (dirac8 D x.1, dirac8 D x.2)
  map_add' x y := by
    ext <;>
      simp [dirac8, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    · dsimp [dirac8, Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · dsimp [dirac8, Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem doubledFockEmbedding_dirac_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (x : DoubledSpinor8) :
    Matrix.mulVec (dirac32 D) (doubledFockEmbedding x) =
      doubledFockEmbedding (doubledDirac8 D x) := by
  change Matrix.mulVec (dirac32 D)
      (fockEmbeddingAt 0 x.1 + fockEmbeddingAt 1 x.2) =
    fockEmbeddingAt 0 (dirac8 D x.1) + fockEmbeddingAt 1 (dirac8 D x.2)
  rw [Matrix.mulVec_add]
  calc
    Matrix.mulVec (dirac32 D) (fockEmbeddingAt 0 x.1) +
        Matrix.mulVec (dirac32 D) (fockEmbeddingAt 1 x.2) =
      fockEmbedding (dirac8 D x.1) +
        Matrix.mulVec (dirac32 D) (fockEmbeddingAt 1 x.2) := by
          rw [fockEmbeddingAt_zero_eq_fockEmbedding]
          rw [fockEmbedding_dirac_intertwine]
    _ = fockEmbedding (dirac8 D x.1) +
        fockEmbeddingAt 1 (dirac8 D x.2) := by
          rw [fockEmbeddingAt_one_dirac_intertwine]
    _ = fockEmbeddingAt 0 (dirac8 D x.1) +
        fockEmbeddingAt 1 (dirac8 D x.2) := by
          rw [fockEmbeddingAt_zero_eq_fockEmbedding]

theorem doubledFockEmbedding_laplacian_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (x : DoubledSpinor8) :
    Matrix.mulVec (dirac32 D * dirac32 D) (doubledFockEmbedding x) =
      doubledFockEmbedding (doubledDirac8 D (doubledDirac8 D x)) := by
  rw [← Matrix.mulVec_mulVec]
  rw [doubledFockEmbedding_dirac_intertwine]
  rw [doubledFockEmbedding_dirac_intertwine]

theorem doubledFockEmbedding_exterior_dirac_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (x : DoubledExterior3) :
    Matrix.mulVec (dirac32 D) (doubledFockEmbedding
      (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding (doubledDirac8 D
        (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) :=
  doubledFockEmbedding_dirac_intertwine D
    (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)

theorem concreteDoubledDirac_to_master_intertwine
    (v : V3) (φ : Module.Dual ℝ V3) (x : DoubledExterior3) :
    Matrix.mulVec (dirac32 (transportedConcreteDiracMatrix v φ))
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
    doubledFockEmbedding
        (exteriorToSpinor8 (concreteDirac3 v φ x).1,
          exteriorToSpinor8 (concreteDirac3 v φ x).2) := by
  have h := doubledFockEmbedding_dirac_intertwine
    (transportedConcreteDiracMatrix v φ)
    (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)
  simpa [doubledDirac8, dirac8, transportedConcreteDiracMatrix,
    transportedConcreteDirac3, transportExteriorEnd, concreteDirac3,
    doubledDiagonal] using h

/-! The fixed master Hodge matrix uses its own canonical five-mode Fock basis.
The carrier embedding above is defined through the independent finite-dimensional
equivalence `exteriorToSpinor8`, so equality with that fixed matrix requires an
explicit basis-compatibility hypothesis.  This theorem packages exactly the
remaining comparison without silently treating the two bases as definitionally
identical. -/
theorem concreteDoubledDirac_to_fixed_master_hodge_intertwine
    (v : V3) (φ : Module.Dual ℝ V3)
    (hD : dirac32 (transportedConcreteDiracMatrix v φ) =
      masterHodgeDiracFin32) (x : DoubledExterior3) :
    Matrix.mulVec masterHodgeDiracFin32
        (doubledFockEmbedding
          (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) =
      doubledFockEmbedding
        (exteriorToSpinor8 (concreteDirac3 v φ x).1,
          exteriorToSpinor8 (concreteDirac3 v φ x).2) := by
  rw [← hD]
  exact concreteDoubledDirac_to_master_intertwine v φ x

theorem first_slot_dirac_intertwine (D : Matrix (Fin 8) (Fin 8) ℝ)
    (v : Exterior3) :
    Matrix.mulVec (dirac32 D) (fockEmbeddingAt 0 (exteriorToSpinor8 v)) =
      fockEmbeddingAt 0
        (dirac8 D (exteriorToSpinor8 v)) := by
  simpa only [fockEmbeddingAt_zero_eq_fockEmbedding] using
    (fockEmbedding_dirac_intertwine D (exteriorToSpinor8 v)).symm

end InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge

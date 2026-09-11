import InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hestenes phase transport on the embedded master carrier

The carrier embedding places the doubled three-mode packet in slots `0` and
`1` of the five-mode master spinor.  This owner defines the corresponding
phase only on those two slots and proves the exact intertwining relation with
the concrete doubled Hestenes phase.  The phase is deliberately not promoted
to the global Clifford chirality or to a full `Cl(5,5)` representation claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55ConcreteHestenesPhaseEmbeddingBridge

open Matrix
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.Cl55ConcreteHestenesCarrierEmbeddingBridge

def hestenesPhase8 : DoubledSpinor8 →ₗ[ℝ] DoubledSpinor8 where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

theorem hestenesPhase8_sq_apply (x : DoubledSpinor8) :
    hestenesPhase8 (hestenesPhase8 x) = -x := by
  rcases x with ⟨a, b⟩
  rfl

def fockProjectionAtLinear (a : Fin 4) : Spinor32 →ₗ[ℝ] Spinor8 where
  toFun z i := z (HodgeFockEmbeddingBridge.fin32Equiv.symm (i, a))
  map_add' z w := by
    ext i
    simp
  map_smul' c z := by
    ext i
    simp

@[simp] theorem fockProjectionAtLinear_apply
    (a : Fin 4) (z : Spinor32) (i : Fin 8) :
    fockProjectionAtLinear a z i =
      z (HodgeFockEmbeddingBridge.fin32Equiv.symm (i, a)) := rfl

theorem fockProjectionAt_embeddingAt
    (a b : Fin 4) (v : Spinor8) :
    fockProjectionAtLinear a (fockEmbeddingAt b v) =
      if a = b then v else 0 := by
  ext i
  by_cases hab : a = b
  · subst b
    simp [fockProjectionAtLinear, fockEmbeddingAt]
  · simp [fockProjectionAtLinear, fockEmbeddingAt, hab]

def embeddedHestenesPhase32 : Module.End ℝ Spinor32 :=
  -((fockEmbeddingAtLinear 0).comp (fockProjectionAtLinear 1)) +
    (fockEmbeddingAtLinear 1).comp (fockProjectionAtLinear 0)

theorem embeddedHestenesPhase32_on_doubledEmbedding
    (x : DoubledSpinor8) :
    embeddedHestenesPhase32 (doubledFockEmbedding x) =
      doubledFockEmbedding (hestenesPhase8 x) := by
  rw [doubledFockEmbedding_apply]
  simp only [embeddedHestenesPhase32, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply]
  simp only [map_add]
  rw [fockProjectionAt_embeddingAt, fockProjectionAt_embeddingAt,
    fockProjectionAt_embeddingAt, fockProjectionAt_embeddingAt]
  simp
  rw [doubledFockEmbedding_apply]
  simp [hestenesPhase8]
  change -fockEmbeddingAt 0 x.2 + fockEmbeddingAt 1 x.1 = _
  have hnegembed : fockEmbeddingAt 0 (-x.2) =
      -fockEmbeddingAt 0 x.2 := by
    ext i
    by_cases h : (HodgeFockEmbeddingBridge.fin32Equiv i).2 = (0 : Fin 4)
    · simp [fockEmbeddingAt, h]
    · simp [fockEmbeddingAt, h]
  rw [hnegembed]

theorem hestenesPhase8_doubledDirac8_commute
    (D : Matrix (Fin 8) (Fin 8) ℝ) (x : DoubledSpinor8) :
    hestenesPhase8 (doubledDirac8 D x) =
      doubledDirac8 D (hestenesPhase8 x) := by
  have hneg (v : Spinor8) :
      HodgeFockEmbeddingBridge.dirac8 D (-v) =
        -HodgeFockEmbeddingBridge.dirac8 D v := by
    ext i
    simp [HodgeFockEmbeddingBridge.dirac8, Matrix.mulVec,
      dotProduct, Finset.sum_neg_distrib]
  apply Prod.ext
  · dsimp [hestenesPhase8, doubledDirac8]
    exact hneg x.2 |>.symm
  · rfl

theorem embeddedHestenesPhase32_sq_on_doubledEmbedding
    (x : DoubledSpinor8) :
    embeddedHestenesPhase32
        (embeddedHestenesPhase32 (doubledFockEmbedding x)) =
      -(doubledFockEmbedding x) := by
  rw [embeddedHestenesPhase32_on_doubledEmbedding,
    embeddedHestenesPhase32_on_doubledEmbedding,
    hestenesPhase8_sq_apply]
  exact map_neg doubledFockEmbedding x

theorem concreteHestenesPhase32_sq
    (x : DoubledExterior3) :
    embeddedHestenesPhase32
        (embeddedHestenesPhase32
          (doubledFockEmbedding
            (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2))) =
      -(doubledFockEmbedding
        (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)) := by
  exact embeddedHestenesPhase32_sq_on_doubledEmbedding
    (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)

theorem embeddedHestenesPhase32_dirac_intertwine_on_doubledEmbedding
    (D : Matrix (Fin 8) (Fin 8) ℝ) (x : DoubledSpinor8) :
    embeddedHestenesPhase32
        (Matrix.mulVec (HodgeFockEmbeddingBridge.dirac32 D)
          (doubledFockEmbedding x)) =
      Matrix.mulVec (HodgeFockEmbeddingBridge.dirac32 D)
        (embeddedHestenesPhase32 (doubledFockEmbedding x)) := by
  calc
    embeddedHestenesPhase32
        (Matrix.mulVec (HodgeFockEmbeddingBridge.dirac32 D)
          (doubledFockEmbedding x)) =
        embeddedHestenesPhase32
          (doubledFockEmbedding (doubledDirac8 D x)) := by
            rw [doubledFockEmbedding_dirac_intertwine]
    _ = doubledFockEmbedding (hestenesPhase8 (doubledDirac8 D x)) := by
          rw [embeddedHestenesPhase32_on_doubledEmbedding]
    _ = doubledFockEmbedding (doubledDirac8 D (hestenesPhase8 x)) := by
          rw [hestenesPhase8_doubledDirac8_commute]
    _ = Matrix.mulVec (HodgeFockEmbeddingBridge.dirac32 D)
          (doubledFockEmbedding (hestenesPhase8 x)) := by
          rw [doubledFockEmbedding_dirac_intertwine]
    _ = Matrix.mulVec (HodgeFockEmbeddingBridge.dirac32 D)
          (embeddedHestenesPhase32 (doubledFockEmbedding x)) := by
          rw [embeddedHestenesPhase32_on_doubledEmbedding]

theorem concreteHestenesPhase32_dirac_intertwine
    (v : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3)
    (φ : Module.Dual ℝ
      InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3)
    (x : DoubledExterior3) :
    embeddedHestenesPhase32
        (Matrix.mulVec
          (HodgeFockEmbeddingBridge.dirac32
            (transportedConcreteDiracMatrix v φ))
          (doubledFockEmbedding
            (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2))) =
      Matrix.mulVec
        (HodgeFockEmbeddingBridge.dirac32
          (transportedConcreteDiracMatrix v φ))
        (embeddedHestenesPhase32
          (doubledFockEmbedding
            (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2))) := by
  exact embeddedHestenesPhase32_dirac_intertwine_on_doubledEmbedding
    (transportedConcreteDiracMatrix v φ)
    (exteriorToSpinor8 x.1, exteriorToSpinor8 x.2)

end InfoGeometry.Canonical.Cl55ConcreteHestenesPhaseEmbeddingBridge

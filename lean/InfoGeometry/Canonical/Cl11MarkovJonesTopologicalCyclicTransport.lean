import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TopologicalColimitBraidAction

/-!
# Cyclic readout transport for the finite `Cl(1,1)` Markov tower

This owner supplies genuine stagewise multiplication actions for a compatible
family in the existing matrix tower.  The normalized trace cocone is then
shown cyclic on the native `TopCat` colimit by the generic categorical
readout theorem.  The colimit remains a topological object; no multiplication
is imposed on its quotient carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11MarkovJonesTopologicalCyclicTransport

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Canonical.TopologicalColimitBraidAction

abbrev StageFamily := ∀ n : ℕ, MatStage n

def leftMultiplicationNatTrans
    (a : StageFamily)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (a m) = a n) :
    topologicalDiagram ⟶ topologicalDiagram where
  app n := TopCat.ofHom (ContinuousMap.mulLeft (a n))
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change MatStage m at x
    change a n * stageEmbedMap (leOfHom f) x =
      stageEmbedMap (leOfHom f) (a m * x)
    rw [map_mul, ha (leOfHom f)]

def rightMultiplicationNatTrans
    (a : StageFamily)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (a m) = a n) :
    topologicalDiagram ⟶ topologicalDiagram where
  app n := TopCat.ofHom (ContinuousMap.mulRight (a n))
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change MatStage m at x
    change stageEmbedMap (leOfHom f) x * a n =
      stageEmbedMap (leOfHom f) (x * a m)
    rw [map_mul, ha (leOfHom f)]

def conjugationNatTrans
    (u uInv : StageFamily)
    (hu : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (u m) = u n)
    (huInv : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (uInv m) = uInv n) :
    topologicalDiagram ⟶ topologicalDiagram where
  app n := TopCat.ofHom
    ({ toFun := fun x => u n * x * uInv n
       continuous_toFun := by fun_prop } :
      ContinuousMap (MatStage n) (MatStage n))
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change MatStage m at x
    change u n * stageEmbedMap (leOfHom f) x * uInv n =
      stageEmbedMap (leOfHom f) (u m * x * uInv m)
    rw [map_mul, map_mul, hu (leOfHom f), huInv (leOfHom f)]

theorem traceColimit_conjugation_invariant
    (u uInv : StageFamily)
    (hu : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (u m) = u n)
    (huInv : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (uInv m) = uInv n)
    (hunit : ∀ n, uInv n * u n = 1) :
    colim.map (conjugationNatTrans u uInv hu huInv) ≫
        traceTopologicalColimitMap =
      traceTopologicalColimitMap := by
  apply colimit_readout_invariant
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change MatStage n at x
  dsimp [conjugationNatTrans, traceTopologicalCocone]
  change normalizedTraceTopCatHom n (u n * x * uInv n) =
    normalizedTraceTopCatHom n x
  change normalizedTrace n (u n * x * uInv n) = normalizedTrace n x
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm, ← mul_assoc, hunit]
  simp

theorem traceColimit_leftRight_compatible_family
    (a : StageFamily)
    (ha : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (a m) = a n)
    (b : StageFamily)
    (hb : ∀ {m n : ℕ} (h : m ≤ n), stageEmbedMap h (b m) = b n) :
    colim.map (leftMultiplicationNatTrans a ha) ≫
        colim.map (rightMultiplicationNatTrans b hb) ≫
        traceTopologicalColimitMap =
      colim.map (rightMultiplicationNatTrans b hb) ≫
        colim.map (leftMultiplicationNatTrans a ha) ≫
        traceTopologicalColimitMap := by
  apply colimit_readout_cyclic
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change MatStage n at x
  dsimp [leftMultiplicationNatTrans, rightMultiplicationNatTrans,
    traceTopologicalCocone]
  change normalizedTraceTopCatHom n ((a n * x) * b n) =
    normalizedTraceTopCatHom n (a n * (x * b n))
  rw [mul_assoc]

end InfoGeometry.Canonical.Cl11MarkovJonesTopologicalCyclicTransport

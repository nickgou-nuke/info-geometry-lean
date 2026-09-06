import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

/-!
# Native three-dimensional exterior Hodge--Dirac bridge

This owner is the literal Mathlib exterior-algebra realization of the
three-dimensional `1 + 3 + 3 + 1` exterior carrier. Wedge and contraction are
creation and annihilation operators; their sum is the Hodge--Dirac operator on
the finite exterior carrier.

The exterior carrier is identified explicitly, basis-by-basis, with the
repository's circular Peirce coordinates and canonical Zorn split-octonion
carrier. The bridge is linear: no multiplicative algebra equivalence or split
norm intertwining is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

abbrev V3 := Fin 3 → ℝ
abbrev Exterior3 := ExteriorAlgebra ℝ V3
abbrev Exterior3End := Module.End ℝ Exterior3
abbrev SplitOctonionCoordinateCarrier := Dim8 → ℝ
abbrev CanonicalSplitOctonion :=
  InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.CZ

noncomputable def vBasis3 : Module.Basis (Fin 3) ℝ V3 := Pi.basisFun ℝ (Fin 3)

noncomputable def degreeBasis3 (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin 3) k) ℝ (⋀[ℝ]^k V3) :=
  vBasis3.exteriorPower k

noncomputable def exterior3BasisSigma :
    Module.Basis (Σ k : ℕ, Set.powersetCard (Fin 3) k) ℝ Exterior3 :=
  (DirectSum.Decomposition.isInternal
      (ℳ := fun k : ℕ => ⋀[ℝ]^k V3)).collectedBasis
    (fun k => degreeBasis3 k)

noncomputable def exterior3BasisFinset :
    Module.Basis (Finset (Fin 3)) ℝ Exterior3 :=
  exterior3BasisSigma.reindex (Equiv.sigmaFiberEquiv Finset.card)

/-!
The circular Peirce ordering used throughout the split-octonion owners is

* `0` : degree `0` / scalar-plus,
* `1,2,3` : degree `1` / root-plus,
* `4` : degree `3` / scalar-minus,
* `5,6,7` : degree `2` / root-minus.

The degree-two order is the Hodge-dual order `e₁₂, e₀₂, e₀₁` relative to the
three degree-one coordinate directions.
-/
def peirceSubset : Fin 8 → Finset (Fin 3) :=
  ![∅, {0}, {1}, {2}, {0, 1, 2}, {1, 2}, {0, 2}, {0, 1}]

theorem peirceSubset_bijective : Function.Bijective peirceSubset := by
  native_decide

noncomputable def peirceSubsetEquiv : Fin 8 ≃ Finset (Fin 3) :=
  Equiv.ofBijective peirceSubset peirceSubset_bijective

/-- The literal exterior basis reindexed by the established circular Peirce order. -/
noncomputable def exterior3PeirceBasis : Module.Basis (Fin 8) ℝ Exterior3 :=
  exterior3BasisFinset.reindex peirceSubsetEquiv.symm

@[simp] theorem peirceSubset_scalarPlus : peirceSubset 0 = ∅ := rfl

@[simp] theorem peirceSubset_rootPlus (i : Fin 3) :
    peirceSubset ⟨i.val + 1, by omega⟩ = {i} := by
  fin_cases i <;> rfl

@[simp] theorem peirceSubset_scalarMinus :
    peirceSubset 4 = (Finset.univ : Finset (Fin 3)) := by
  native_decide

@[simp] theorem peirceSubset_rootMinus (i : Fin 3) :
    peirceSubset ⟨i.val + 5, by omega⟩ =
      (Finset.univ : Finset (Fin 3)).erase i := by
  fin_cases i <;> native_decide

theorem exterior3_finrank : Module.finrank ℝ Exterior3 = 8 := by
  rw [Module.finrank_eq_card_basis exterior3PeirceBasis]
  exact Fintype.card_fin 8

theorem splitOctonionCoordinate_finrank :
    Module.finrank ℝ SplitOctonionCoordinateCarrier = 8 := by
  simp [SplitOctonionCoordinateCarrier]

instance exterior3_finiteDimensional : FiniteDimensional ℝ Exterior3 := by
  exact Module.Basis.finiteDimensional_of_finite exterior3PeirceBasis

/--
Explicit coordinate equivalence from the literal exterior algebra to the
established `Fin 8 → ℝ` circular Peirce coordinate carrier.
-/
noncomputable def exterior3SplitOctonionCoordinateEquiv :
    Exterior3 ≃ₗ[ℝ] SplitOctonionCoordinateCarrier :=
  exterior3PeirceBasis.equivFun

@[simp] theorem exterior3SplitOctonionCoordinateEquiv_basis (j : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv (exterior3PeirceBasis j) =
      Pi.single j 1 := by
  unfold exterior3SplitOctonionCoordinateEquiv
  rw [exterior3PeirceBasis.equivFun_apply]
  rw [exterior3PeirceBasis.repr_self]
  ext k
  by_cases h : j = k
  · subst k
    simp
  · simp [h]

/--
Basis-preserving linear equivalence from the literal exterior spinor carrier to
the canonical Zorn split-octonion carrier. This is deliberately not an algebra
equivalence: the split-octonion product is a separate nonassociative tensor.
-/
noncomputable def exterior3CircularPeirceEquiv :
    Exterior3 ≃ₗ[ℝ] CanonicalSplitOctonion :=
  exterior3SplitOctonionCoordinateEquiv.trans circularPeirceBasis.equivFun.symm

@[simp] theorem exterior3CircularPeirceEquiv_basis (j : Fin 8) :
    exterior3CircularPeirceEquiv (exterior3PeirceBasis j) =
      circularPeirceBasis j := by
  rw [exterior3CircularPeirceEquiv, LinearEquiv.trans_apply,
    exterior3SplitOctonionCoordinateEquiv_basis]
  apply circularPeirceBasis.equivFun.injective
  simp

/-! Native creation, annihilation, and CAR on the literal exterior algebra. -/

def exteriorWedge3 (v : V3) : Exterior3End :=
  Algebra.lmul ℝ Exterior3 (ExteriorAlgebra.ι ℝ v)

def exteriorContract3 (φ : Module.Dual ℝ V3) : Exterior3End :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V3)) φ

@[simp] theorem exteriorWedge3_apply (v : V3) (ψ : Exterior3) :
    exteriorWedge3 v ψ = ExteriorAlgebra.ι ℝ v * ψ := rfl

@[simp] theorem exteriorWedge3_sq (v : V3) :
    exteriorWedge3 v * exteriorWedge3 v = 0 := by
  apply LinearMap.ext
  intro ψ
  change ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ v * ψ) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

@[simp] theorem exteriorContract3_wedge3_apply
    (φ : Module.Dual ℝ V3) (v : V3) (ψ : Exterior3) :
    exteriorContract3 φ (exteriorWedge3 v ψ) =
      φ v • ψ - exteriorWedge3 v (exteriorContract3 φ ψ) := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V3)) φ
      (ExteriorAlgebra.ι ℝ v * ψ) = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  rfl

@[simp] theorem exteriorContract3_sq (φ : Module.Dual ℝ V3) :
    exteriorContract3 φ * exteriorContract3 φ = 0 := by
  apply LinearMap.ext
  intro ψ
  exact CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm ℝ V3)) φ ψ

theorem exteriorWedge3_add_swap (v u : V3) :
    exteriorWedge3 v * exteriorWedge3 u +
        exteriorWedge3 u * exteriorWedge3 v = 0 := by
  apply LinearMap.ext
  intro ψ
  change ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ u * ψ) +
      ExteriorAlgebra.ι ℝ u * (ExteriorAlgebra.ι ℝ v * ψ) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem exteriorContract3_add_swap
    (φ ψ : Module.Dual ℝ V3) :
    exteriorContract3 φ * exteriorContract3 ψ +
        exteriorContract3 ψ * exteriorContract3 φ = 0 := by
  apply LinearMap.ext
  intro ξ
  change CliffordAlgebra.contractLeft φ
      (CliffordAlgebra.contractLeft ψ ξ) +
      CliffordAlgebra.contractLeft ψ
        (CliffordAlgebra.contractLeft φ ξ) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  simp

theorem exteriorContract3_wedge3_CAR (φ : Module.Dual ℝ V3) (v : V3) :
    exteriorContract3 φ * exteriorWedge3 v + exteriorWedge3 v * exteriorContract3 φ =
      (φ v) • (1 : Exterior3End) := by
  apply LinearMap.ext
  intro ψ
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V3)) φ
      (ExteriorAlgebra.ι ℝ v * ψ) +
      ExteriorAlgebra.ι ℝ v * exteriorContract3 φ ψ =
        (φ v • (1 : Exterior3End)) ψ
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp only [exteriorContract3]
  abel

noncomputable def exteriorGrade3 : Exterior3 →ₐ[ℝ] Exterior3 :=
  gradeInvolution (R := ℝ) (V := V3)

theorem exteriorGrade3_involutive (ψ : Exterior3) :
    exteriorGrade3 (exteriorGrade3 ψ) = ψ :=
  gradeInvolution_involutive ψ

theorem exteriorGrade3_wedge (v : V3) (ψ : Exterior3) :
    exteriorGrade3 (exteriorWedge3 v ψ) =
      -(exteriorWedge3 v (exteriorGrade3 ψ)) := by
  change gradeInvolution (ExteriorAlgebra.ι ℝ v * ψ) =
    -(ExteriorAlgebra.ι ℝ v * gradeInvolution ψ)
  rw [map_mul, gradeInvolution_ι]
  simp only [neg_mul]

theorem exteriorGrade3_contract (φ : Module.Dual ℝ V3) (ψ : Exterior3) :
    exteriorGrade3 (exteriorContract3 φ ψ) =
      -(exteriorContract3 φ (exteriorGrade3 ψ)) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    simp [exteriorContract3, exteriorGrade3]
  · intro x y hx hy
    simp only [map_add, hx, hy, neg_add]
  · intro x a hx
    change gradeInvolution (exteriorContract3 φ (exteriorWedge3 a x)) =
      -(exteriorContract3 φ (exteriorGrade3 (exteriorWedge3 a x)))
    rw [exteriorContract3_wedge3_apply, map_sub, map_smul]
    rw [exteriorGrade3_wedge a x]
    simp only [map_neg, neg_neg]
    change φ a • exteriorGrade3 x -
      exteriorGrade3 (exteriorWedge3 a (exteriorContract3 φ x)) = _
    rw [exteriorGrade3_wedge a (exteriorContract3 φ x), hx,
      exteriorContract3_wedge3_apply]
    simp

def exteriorHodgeDirac3 (v : V3) (φ : Module.Dual ℝ V3) : Exterior3End :=
  exteriorWedge3 v + exteriorContract3 φ

abbrev exterior3NeutralSpace :=
  InfoGeometry.Clifford.NeutralPhaseSpaceCore.PhaseSpaceCarrier V3

def exterior3NeutralPairing
    (w z : exterior3NeutralSpace) : ℝ :=
  (w.2 z.1 + z.2 w.1) / 2

def exterior3NeutralAction (w : exterior3NeutralSpace) : Exterior3End :=
  exteriorWedge3 w.1 + exteriorContract3 w.2

noncomputable def exterior3NeutralActionMap :
    exterior3NeutralSpace →ₗ[ℝ] Exterior3End where
  toFun := exterior3NeutralAction
  map_add' w z := by
    rcases w with ⟨v, φ⟩
    rcases z with ⟨u, ψ⟩
    apply LinearMap.ext
    intro ξ
    change (ExteriorAlgebra.ι ℝ (v + u) * ξ +
        exteriorContract3 (φ + ψ) ξ) =
      (ExteriorAlgebra.ι ℝ v * ξ + exteriorContract3 φ ξ) +
        (ExteriorAlgebra.ι ℝ u * ξ + exteriorContract3 ψ ξ)
    rw [map_add, add_mul]
    simp only [exteriorContract3, map_add, LinearMap.add_apply]
    abel
  map_smul' c w := by
    rcases w with ⟨v, φ⟩
    apply LinearMap.ext
    intro ξ
    change (ExteriorAlgebra.ι ℝ (c • v) * ξ +
        exteriorContract3 (c • φ) ξ) =
      c • (ExteriorAlgebra.ι ℝ v * ξ + exteriorContract3 φ ξ)
    rw [map_smul, smul_mul_assoc]
    simp only [exteriorContract3, map_smul, smul_add, LinearMap.smul_apply]

theorem exterior3NeutralAction_anticommutator
    (w z : exterior3NeutralSpace) :
    exterior3NeutralAction w * exterior3NeutralAction z +
        exterior3NeutralAction z * exterior3NeutralAction w =
      (2 * exterior3NeutralPairing w z) • (1 : Exterior3End) := by
  rcases w with ⟨v, φ⟩
  rcases z with ⟨u, ψ⟩
  calc
    exterior3NeutralAction (v, φ) * exterior3NeutralAction (u, ψ) +
          exterior3NeutralAction (u, ψ) * exterior3NeutralAction (v, φ) =
        (exteriorWedge3 v * exteriorWedge3 u +
          exteriorWedge3 u * exteriorWedge3 v) +
        (exteriorContract3 φ * exteriorWedge3 u +
          exteriorWedge3 u * exteriorContract3 φ) +
        (exteriorContract3 ψ * exteriorWedge3 v +
          exteriorWedge3 v * exteriorContract3 ψ) +
        (exteriorContract3 φ * exteriorContract3 ψ +
          exteriorContract3 ψ * exteriorContract3 φ) := by
            simp only [exterior3NeutralAction, add_mul, mul_add]
            abel
    _ = (2 * exterior3NeutralPairing (v, φ) (u, ψ)) •
          (1 : Exterior3End) := by
      rw [exteriorWedge3_add_swap]
      rw [exteriorContract3_add_swap]
      rw [exteriorContract3_wedge3_CAR φ u]
      rw [exteriorContract3_wedge3_CAR ψ v]
      simp only [exterior3NeutralPairing, zero_add, add_zero]
      rw [← add_smul]
      congr 1
      ring_nf

def exteriorHodgeLaplacian3 (v : V3) (φ : Module.Dual ℝ V3) : Exterior3End :=
  exteriorContract3 φ * exteriorWedge3 v + exteriorWedge3 v * exteriorContract3 φ

theorem exteriorHodgeDirac3_sq (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorHodgeDirac3 v φ * exteriorHodgeDirac3 v φ =
      exteriorHodgeLaplacian3 v φ := by
  simp only [exteriorHodgeDirac3, exteriorHodgeLaplacian3, add_mul, mul_add,
    exteriorWedge3_sq, exteriorContract3_sq, zero_add, add_zero]

theorem exteriorHodgeLaplacian3_scalar (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorHodgeLaplacian3 v φ = (φ v) • (1 : Exterior3End) :=
  exteriorContract3_wedge3_CAR φ v

noncomputable def exterior3CliffordRep :
    CliffordAlgebra
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
          (E := V3)) →ₐ[ℝ] Exterior3End :=
  CliffordAlgebra.lift _
    ⟨exterior3NeutralActionMap, by
      intro w
      rcases w with ⟨v, φ⟩
      simpa [exterior3NeutralActionMap, exterior3NeutralAction,
        InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply]
        using (exteriorHodgeDirac3_sq v φ).trans
          (exteriorHodgeLaplacian3_scalar v φ)⟩

@[simp] theorem exterior3CliffordRep_ι
    (w : exterior3NeutralSpace) :
    exterior3CliffordRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V3)) w) =
      exterior3NeutralAction w := by
  exact CliffordAlgebra.lift_ι_apply _ _ w

theorem exteriorHodgeDirac3_odd (v : V3) (φ : Module.Dual ℝ V3) (ψ : Exterior3) :
    exteriorGrade3 (exteriorHodgeDirac3 v φ ψ) =
      -(exteriorHodgeDirac3 v φ (exteriorGrade3 ψ)) := by
  change exteriorGrade3
      (exteriorWedge3 v ψ + exteriorContract3 φ ψ) = _
  rw [map_add, exteriorGrade3_wedge, exteriorGrade3_contract]
  simp only [exteriorHodgeDirac3, LinearMap.add_apply, neg_add]

/-! Arithmetic readout: the finite logarithmic shift is the discrete analogue
of the scalar coefficient entering a weighted Hodge Laplacian. -/

def exteriorPrimeHodgeWeight (p : ℕ) : ℝ := Real.log p

theorem exteriorFiniteDirichlet_logarithmic_readout
    (N : ℕ) (s : ℂ) (t : ℝ) :
    finiteDirichletShift N (exponentialTest s) t =
      Finset.sum (Finset.range (N + 1))
        (fun n => Complex.exp (-s * (Real.log (Nat.succ n : ℕ) : ℂ))) *
        exponentialTest s t := by
  exact finiteDirichletShift_exponentialTest N s t

end InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
import InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

/-!
# Native three-dimensional exterior Hodge--Dirac bridge

This owner is the literal Mathlib exterior-algebra realization of the
three-dimensional `1 + 3 + 3 + 1` exterior carrier.  Wedge and contraction are the creation and
annihilation operators; their sum is the Hodge--Dirac operator on the finite
exterior carrier.  The split-octonion connection is only linear-carrier
level here: no multiplicative or algebra isomorphism is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
open InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

abbrev V3 := Fin 3 → ℝ
abbrev Exterior3 := ExteriorAlgebra ℝ V3
abbrev Exterior3End := Module.End ℝ Exterior3
abbrev SplitOctonionCoordinateCarrier := Dim8 → ℝ

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

theorem exterior3_finrank : Module.finrank ℝ Exterior3 = 8 := by
  rw [Module.finrank_eq_card_basis exterior3BasisFinset]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

theorem splitOctonionCoordinate_finrank :
    Module.finrank ℝ SplitOctonionCoordinateCarrier = 8 := by
  simp [SplitOctonionCoordinateCarrier]

instance exterior3_finiteDimensional : FiniteDimensional ℝ Exterior3 := by
  exact Module.Basis.finiteDimensional_of_finite exterior3BasisFinset

/-! This is deliberately only a finite-dimensional carrier equivalence.  The
current proof does not identify grades, multiplication, or the split norm. -/
noncomputable def exterior3SplitOctonionCoordinateEquiv :
    Exterior3 ≃ₗ[ℝ] SplitOctonionCoordinateCarrier :=
  LinearEquiv.ofFinrankEq Exterior3 SplitOctonionCoordinateCarrier
    (exterior3_finrank.trans splitOctonionCoordinate_finrank.symm)

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

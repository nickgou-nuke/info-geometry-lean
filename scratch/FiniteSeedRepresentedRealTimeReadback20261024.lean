/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentedKMS
import InfoGeometry.Canonical.FiniteMatrixGibbsParity
import InfoGeometry.Canonical.FilteredGNSBoundedGeneratorUnitaryFlow

/-!
# Real-time evolution of the actual finite-seed represented Gibbs state

The represented seed Hamiltonian generates the existing exponential unitary
flow. Its direct conjugation action uses the positive-time convention
`exp(i t H) A exp(-i t H)`. Gibbs invariance follows from the proved twisted
identity and commutation of the mapped density with this unitary. No flow or
invariance conclusion is supplied as an input. No analytic strip claim is made.
-/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.OperatorAlgebra

/-- Time continuity of the native exponential unitary, elaborated on an abstract
C⋆ algebra before specializing to a dependent represented closure. -/
theorem expUnitary_real_time_continuous {A : Type*} [CStarAlgebra A]
    (G : selfAdjoint A) :
    Continuous (fun t : ℝ => selfAdjoint.expUnitary (t • G)) := by
  exact selfAdjoint.continuous_expUnitary.comp (continuous_id.smul continuous_const)

/-- Positive-time conjugation composition for a single self-adjoint generator. -/
theorem expUnitary_conjugation_add {A : Type*} [CStarAlgebra A]
    (G : selfAdjoint A) (t s : ℝ) (a : A) :
    Unitary.conjStarAlgAut (S := ℂ) (R := A) (selfAdjoint.expUnitary ((t + s) • G)) a =
      Unitary.conjStarAlgAut (S := ℂ) (R := A) (selfAdjoint.expUnitary (t • G))
        (Unitary.conjStarAlgAut (S := ℂ) (R := A) (selfAdjoint.expUnitary (s • G)) a) := by
  rw [CStarStateColimit.Native.FilteredGNSBoundedGeneratorUnitaryFlow.cstar_selfAdjoint_expUnitary_add,
    Unitary.conjStarAlgAut_mul_apply]


/-- A twisted readout is invariant under conjugation by a commuting unitary. -/
theorem twisted_readout_unitary_invariant {A : Type*} [Ring A] [StarRing A]
    (φ : A → ℂ) (δ : Aˣ)
    (htwist : ∀ x y, φ (x * y) = φ (y * ((δ : A) * x * (↑δ⁻¹ : A))))
    (U : unitary A) (hcomm : Commute (δ : A) (U : A)) (a : A) :
    φ ((U : A) * a * star (U : A)) = φ a := by
  have hfix : (δ : A) * (U : A) * (↑δ⁻¹ : A) = (U : A) := by
    rw [hcomm.eq, mul_assoc, Units.mul_inv, mul_one]
  calc
    φ ((U : A) * a * star (U : A)) = φ ((U : A) * (a * star (U : A))) := by
      rw [mul_assoc]
    _ = φ ((a * star (U : A)) * ((δ : A) * (U : A) * (↑δ⁻¹ : A))) :=
      htwist (U : A) (a * star (U : A))
    _ = φ a := by rw [hfix, mul_assoc, Unitary.coe_star_mul_self, mul_one]

end InfoGeometry.OperatorAlgebra

namespace CStarStateColimit.Native.FilteredGNSRepresentedKMS

open FilteredStarAlgebraDirectLimit FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumReadback FilteredGNSVacuumState
universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
attribute [local instance] FilteredGNSVacuumState.representedSpectralOrder
  FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- Transparent invariance property of the actual constructed State. -/
def representedVacuumUnitaryInvariant (v : I)
    (U : unitary (representedCStarClosure Stage sys ω)) : Prop :=
  let ρ := representedVacuumState Stage sys ω v
  ∀ a : representedCStarClosure Stage sys ω,
    ρ.functional (Unitary.conjStarAlgAut (S := ℂ) (R := representedCStarClosure Stage sys ω) U a) = ρ.functional a

/-- Apply the algebraic invariance argument abstractly, before specializing
large dependent represented-state types. -/
theorem representedVacuumUnitaryInvariant_of_twisted (v : I)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ)
    (htwist : representedVacuumTwistedCyclic Stage sys ω v δraw)
    (U : unitary (representedCStarClosure Stage sys ω))
    (hcomm : Commute
      ((Units.map (algebraicColimitToRepresentedClosure Stage sys ω).toMonoidHom δraw :
        (representedCStarClosure Stage sys ω)ˣ) : representedCStarClosure Stage sys ω)
      (U : representedCStarClosure Stage sys ω)) :
    representedVacuumUnitaryInvariant Stage sys ω v U := by
  intro a
  exact InfoGeometry.OperatorAlgebra.twisted_readout_unitary_invariant
    (representedVacuumState Stage sys ω v).functional
    (Units.map (algebraicColimitToRepresentedClosure Stage sys ω).toMonoidHom δraw)
    htwist U hcomm a

end CStarStateColimit.Native.FilteredGNSRepresentedKMS

namespace CStarStateColimit.Native.FilteredGNSMatrixRealTime

open FilteredStarAlgebraDirectLimit FilteredGNSRepresentedCStarClosure
open FilteredGNSRepresentedKMS FilteredGNSBoundedGeneratorUnitaryFlow
open FilteredGNSRepresentedCStarModularAutomorphism
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
local notation "C" => representedCStarClosure Stage sys ω
variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Self-adjointness follows from the input Hermitian matrix and the actual map. -/
theorem matrixImage_selfAdjoint
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) : IsSelfAdjoint (f H : representedCStarClosure Stage sys ω) := by
  change star (f H : representedCStarClosure Stage sys ω) = f H
  rw [← map_star]
  exact congrArg f hH

def matrixGenerator
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) : selfAdjoint C :=
  ⟨f H, matrixImage_selfAdjoint Stage sys ω f H hH⟩

def matrixDensityUnit
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : Cˣ := Units.map f.toMonoidHom (gibbsDensityUnit H hH β)

theorem matrixDensity_commutes_generator
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Commute (matrixDensityUnit Stage sys ω f H hH β : C)
      (matrixGenerator Stage sys ω f H hH : C) := by
  exact (gibbsDensity_commutes_of_commute H H hH (Commute.refl H) β).map f

def matrixUnitary
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : unitary C :=
  boundedGeneratorUnitary Stage sys ω (matrixGenerator Stage sys ω f H hH) t

def matrixUnitaryFlow
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) : ClosureUnitaryFlowStd Stage sys ω :=
  boundedGeneratorClosureUnitaryFlow Stage sys ω (matrixGenerator Stage sys ω f H hH)

omit [Nonempty n] in
theorem matrixUnitary_continuous
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) : Continuous (matrixUnitary Stage sys ω f H hH) := by
  exact InfoGeometry.OperatorAlgebra.expUnitary_real_time_continuous
    (A := representedCStarClosure Stage sys ω) (matrixGenerator Stage sys ω f H hH)

theorem matrixDensity_commutes_unitary
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β t : ℝ) :
    Commute (matrixDensityUnit Stage sys ω f H hH β : C)
      (matrixUnitary Stage sys ω f H hH t : C) := by
  change Commute (matrixDensityUnit Stage sys ω f H hH β : C)
    (NormedSpace.exp (Complex.I • (t • (matrixGenerator Stage sys ω f H hH : C))))
  exact (((matrixDensity_commutes_generator Stage sys ω f H hH β).smul_right t).smul_right
    Complex.I).exp_right

def matrixRealTimeAut
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : C ≃⋆ₐ[ℂ] C :=
  Unitary.conjStarAlgAut (S := ℂ) (R := C) (matrixUnitary Stage sys ω f H hH t)

omit [Nonempty n] in
theorem matrixRealTimeAut_zero
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (a : C) : matrixRealTimeAut Stage sys ω f H hH 0 a = a := by
  simp [matrixRealTimeAut, matrixUnitary, boundedGeneratorUnitary_zero]

omit [Nonempty n] in
theorem matrixRealTimeAut_add
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (t s : ℝ) (a : C) :
    matrixRealTimeAut Stage sys ω f H hH (t + s) a =
      matrixRealTimeAut Stage sys ω f H hH t (matrixRealTimeAut Stage sys ω f H hH s a) := by
  exact InfoGeometry.OperatorAlgebra.expUnitary_conjugation_add
    (A := representedCStarClosure Stage sys ω) (matrixGenerator Stage sys ω f H hH) t s a

omit [Nonempty n] in
theorem matrixRealTimeAut_continuous
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (a : C) :
    Continuous (fun t : ℝ => matrixRealTimeAut Stage sys ω f H hH t a) := by
  have hu : Continuous (fun t : ℝ => (matrixUnitary Stage sys ω f H hH t : C)) :=
    continuous_subtype_val.comp (matrixUnitary_continuous Stage sys ω f H hH)
  exact (hu.mul continuous_const).mul hu.star

/-- The concrete stage map into the existing closure, defined before specializing
any dependent finite-seed state family. -/
def representedMatrixStageMap (i : I) (e : Matrix n n ℂ →⋆ₐ[ℂ] Stage i) :
    Matrix n n ℂ →⋆ₐ[ℂ] C :=
  (algebraicColimitToRepresentedClosure Stage sys ω).comp
    ((algebraicStarDirectLimitOf Stage sys i).comp e)

/-- Read back the concrete bounded operator before specializing a dependent state family. -/
theorem representedMatrixStageMap_coe (i : I)
    (e : Matrix n n ℂ →⋆ₐ[ℂ] Stage i) (a : Matrix n n ℂ) :
    (representedMatrixStageMap Stage sys ω i e a :
      FilteredGNSHilbertColimit.GNSHilbertColimit Stage sys ω →L[ℂ]
        FilteredGNSHilbertColimit.GNSHilbertColimit Stage sys ω) =
      FilteredGNSGlobalStageRepresentation.globalStageRepresentationStarAlgHom
        Stage sys ω i (e a) := by
  simp only [representedMatrixStageMap, StarAlgHom.comp_apply,
    algebraicColimitToRepresentedClosure_coe,
    FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation_of]

/-- For a matrix stage, density commutation supplies actual state invariance
from its established represented twisted identity. -/
theorem matrixStage_realTime_state_invariant
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (i v : I)
    (e : Matrix n n ℂ →⋆ₐ[ℂ] Stage i)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ)
    (hδ : δraw = Units.map ((algebraicStarDirectLimitOf Stage sys i).comp e).toMonoidHom
      (gibbsDensityUnit H hH β))
    (htwist : representedVacuumTwistedCyclic Stage sys ω v δraw) (t : ℝ) :
    representedVacuumUnitaryInvariant Stage sys ω v
      (matrixUnitary Stage sys ω (representedMatrixStageMap Stage sys ω i e) H hH t) := by
  cases hδ
  apply representedVacuumUnitaryInvariant_of_twisted Stage sys ω v _ htwist
  exact matrixDensity_commutes_unitary Stage sys ω
    (representedMatrixStageMap Stage sys ω i e) H hH β t

end CStarStateColimit.Native.FilteredGNSMatrixRealTime

namespace InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSMatrixRealTime
open CStarStateColimit.Native.FilteredGNSRepresentedKMS
open CuntzMatrixTowerInstantiation CantorBernoulliCStarMatrixTraceState
open FiniteMatrixGibbsFunctional AlgebraicKMSStateColimit FiniteSeedRepresentedKMS

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

/-- Raw colimit unit alignment, elaborated without a represented state family.
The finite type-copy equivalence and its domain are specified explicitly. -/
theorem seedDensityUnit_eq_stage_map {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    seedDensityUnit H hH β =
      Units.map
        (((CStarStateColimit.Native.FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf
          CStarMatrixStage cstarMatrixInductiveSystem k).comp
          (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom).toMonoidHom)
        (gibbsDensityUnit H hH β) := by
  rfl

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
local notation "ωseed" => finiteSeedCompatibleStageStates H hH β

/-- Actual seed stage map, obtained from the generic represented stage construction. -/
def seedStageHom : MatrixStage k →⋆ₐ[ℂ]
    FilteredGNSRepresentedCStarClosure.representedCStarClosure
      CStarMatrixStage cstarMatrixInductiveSystem ωseed :=
  representedMatrixStageMap CStarMatrixStage cstarMatrixInductiveSystem
    ωseed k CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom

/-- The native seed observable acts by the existing global stage representation. -/
theorem seedStageHom_coe_apply (a : MatrixStage k) :
    (seedStageHom H hH β a :
      FilteredGNSHilbertColimit.GNSHilbertColimit
        CStarMatrixStage cstarMatrixInductiveSystem ωseed →L[ℂ]
      FilteredGNSHilbertColimit.GNSHilbertColimit
        CStarMatrixStage cstarMatrixInductiveSystem ωseed) =
    FilteredGNSGlobalStageRepresentation.globalStageRepresentationStarAlgHom
      CStarMatrixStage cstarMatrixInductiveSystem ωseed k
        ((CStarMatrix.ofMatrixStarAlgEquiv :
          MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k) a) :=
  representedMatrixStageMap_coe CStarMatrixStage cstarMatrixInductiveSystem ωseed k
    (CStarMatrix.ofMatrixStarAlgEquiv :
      MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom a

def seedGenerator := matrixGenerator CStarMatrixStage cstarMatrixInductiveSystem
  ωseed (seedStageHom H hH β) H hH

def representedDensityUnit := matrixDensityUnit CStarMatrixStage cstarMatrixInductiveSystem
  ωseed (seedStageHom H hH β) H hH β

def seedUnitary := matrixUnitary CStarMatrixStage cstarMatrixInductiveSystem
  ωseed (seedStageHom H hH β) H hH

def seedUnitaryFlow := matrixUnitaryFlow CStarMatrixStage cstarMatrixInductiveSystem
  ωseed (seedStageHom H hH β) H hH

def seedRealTimeAut := matrixRealTimeAut CStarMatrixStage cstarMatrixInductiveSystem
  ωseed (seedStageHom H hH β) H hH

/-- Time continuity for the concrete finite-seed exponential unitary. -/
theorem seedUnitary_continuous : Continuous (seedUnitary H hH β) :=
  matrixUnitary_continuous CStarMatrixStage cstarMatrixInductiveSystem
    ωseed (seedStageHom H hH β) H hH

/-- Every actual finite-seed state is invariant under its constructed positive-time
unitary flow; no faithfulness or invariance field is assumed. -/
theorem finiteSeed_realTime_state_invariant (v : ℕ) (t : ℝ) :
    representedVacuumUnitaryInvariant CStarMatrixStage cstarMatrixInductiveSystem ωseed
      v (seedUnitary H hH β t) := by
  exact matrixStage_realTime_state_invariant CStarMatrixStage cstarMatrixInductiveSystem
    ωseed H hH β k v
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom
    (seedDensityUnit H hH β) (seedDensityUnit_eq_stage_map H hH β)
    (finiteSeed_representedVacuumTwistedCyclic H hH β v) t

end InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

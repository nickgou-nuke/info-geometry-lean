import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RicciMongeAmpere
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

open scoped TensorProduct

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Krein
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

section Core

variable {V : Type*}
  [AddCommGroup V] [Module ℝ V]

/-- Chiral projector `P₊ = (1/2)(Id + Γ)`. -/
noncomputable def chiralProjectorPlus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) + Γ))

/-- Chiral projector `P₋ = (1/2)(Id - Γ)`. -/
noncomputable def chiralProjectorMinus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) - Γ))

/-- Positive-chiral component `D⁺ := D ∘ P₊`. -/
noncomputable def chiralPartPlus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorPlus Γ)

/-- Negative-chiral component `D⁻ := D ∘ P₋`. -/
noncomputable def chiralPartMinus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorMinus Γ)

/--
Analytical index model:
`Index(D) = dim(ker(D) ∩ Im(P₊)) - dim(ker(D) ∩ Im(P₋))`.
-/
noncomputable def analyticalIndex [FiniteDimensional ℝ V] (D Γ : Endomorphism V) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker D ⊓ LinearMap.range (chiralProjectorPlus Γ) : Submodule ℝ V) : ℤ) -
    (Module.finrank ℝ (LinearMap.ker D ⊓ LinearMap.range (chiralProjectorMinus Γ) : Submodule ℝ V) : ℤ)

/-- Chiral decomposition identity: `D⁺ + D⁻ = D`. -/
lemma chiralPartPlus_add_chiralPartMinus (D Γ : Endomorphism V) :
    chiralPartPlus D Γ + chiralPartMinus D Γ = D := by
  ext v
  rw [show (chiralPartPlus D Γ + chiralPartMinus D Γ) v
        = D ((chiralProjectorPlus Γ + chiralProjectorMinus Γ) v) by
          simp [chiralPartPlus, chiralPartMinus, map_add]]
  have hproj :
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v = v := by
    calc
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v
          = (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) + Γ) v) +
              (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) - Γ) v) := by
                simp [chiralProjectorPlus, chiralProjectorMinus]
      _ = (1 / 2 : ℝ) •
            ((((LinearMap.id : Endomorphism V) + Γ) v) +
              (((LinearMap.id : Endomorphism V) - Γ) v)) := by
              rw [← smul_add]
      _ = (1 / 2 : ℝ) • (v + v) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • v := by
            simpa using (add_smul (1 / 2 : ℝ) (1 / 2 : ℝ) v).symm
      _ = (1 : ℝ) • v := by norm_num
      _ = v := by simp
  simp [hproj]

/--
If both chiral parts coincide, the corresponding Dirac endomorphisms coincide.

This is exactly the identity `D = D ∘ P₊ + D ∘ P₋` with `P₊ + P₋ = Id`.
-/
lemma dirac_eq_of_chiralParts_eq
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ') :
    D = D' := by
  calc
    D = chiralPartPlus D Γ + chiralPartMinus D Γ := by
      symm
      exact chiralPartPlus_add_chiralPartMinus (D := D) (Γ := Γ)
    _ = chiralPartPlus D' Γ' + chiralPartMinus D' Γ' := by
      rw [hplus, hminus]
    _ = D' := chiralPartPlus_add_chiralPartMinus (D := D') (Γ := Γ')

/-- Lemma `analyticalIndex_eq_of_chiralParts_eq`. -/
lemma analyticalIndex_eq_of_chiralParts_eq
    [FiniteDimensional ℝ V]
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ')
    (hRangePlus :
      LinearMap.range (chiralProjectorPlus Γ) = LinearMap.range (chiralProjectorPlus Γ'))
    (hRangeMinus :
      LinearMap.range (chiralProjectorMinus Γ) = LinearMap.range (chiralProjectorMinus Γ')) :
    analyticalIndex D Γ = analyticalIndex D' Γ' := by
  have hD : D = D' := dirac_eq_of_chiralParts_eq D Γ D' Γ' hplus hminus
  subst hD
  rw [analyticalIndex, analyticalIndex, hRangePlus, hRangeMinus]

/-- Index invariance along a parameterized Dirac/grading family. -/
def IndexInvariantAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop :=
  ∀ s : ℝ, analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0)

/--
Index invariance from pointwise constancy of the chiral parts and of the
projector ranges.
-/
theorem indexInvariantAlong_of_chiralData_const
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hplus : ∀ s : ℝ, chiralPartPlus (D s) (Γ s) = chiralPartPlus (D 0) (Γ 0))
    (hminus : ∀ s : ℝ, chiralPartMinus (D s) (Γ s) = chiralPartMinus (D 0) (Γ 0))
    (hRangePlus :
      ∀ s : ℝ,
        LinearMap.range (chiralProjectorPlus (Γ s)) =
          LinearMap.range (chiralProjectorPlus (Γ 0)))
    (hRangeMinus :
      ∀ s : ℝ,
        LinearMap.range (chiralProjectorMinus (Γ s)) =
          LinearMap.range (chiralProjectorMinus (Γ 0))) :
    IndexInvariantAlong D Γ := by
  intro s
  exact analyticalIndex_eq_of_chiralParts_eq
    (D := D s) (Γ := Γ s) (D' := D 0) (Γ' := Γ 0)
    (hplus s) (hminus s) (hRangePlus s) (hRangeMinus s)

end Core

section Bott

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global grading on the Bott tensor space: `Γ_bott = Γ₁ ⊗ Γₙ`. -/
def globalGrading (Γ1 : Endomorphism E) (Γn : Endomorphism F) :
    Endomorphism (E ⊗[ℝ] F) :=
  TensorProduct.map Γ1 Γn

/-- Analytical index of the Bott-Dirac operator with chosen grading pair. -/
noncomputable def bottAnalyticalIndex
    [FiniteDimensional ℝ (E ⊗[ℝ] F)]
    (D1 Γ1 : Endomorphism E) (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex (bottDirac D1 Γ1 Dn) (globalGrading Γ1 Γn)

/-- `Cl(1,1)` specialization of the global grading. -/
noncomputable def cl11GlobalGrading (Γn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  globalGrading (cl11Grading (E := E)) Γn

/-- `Cl(1,1)` specialization of the Bott analytical index. -/
noncomputable def cl11BottAnalyticalIndex
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
    (cl11GlobalGrading (E := E) Γn)

end Bott

section Laplacian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vanishing condition for the split Bott Laplacian term. -/
def Cl11BottLaplacianZero (Dn : Endomorphism F) : Prop :=
  cl11BottLaplacian (E := E) Dn = 0

/-- Theorem `cl11_bottDirac_sq_eq_zero_of_laplacian_zero`. -/
theorem cl11_bottDirac_sq_eq_zero_of_laplacian_zero
    (Dn : Endomorphism F)
    (hZero : Cl11BottLaplacianZero (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hZero

end Laplacian

section CoupledInvariant

variable (n : Nat)
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Coupled invariant package:
thermodynamic Sinkhorn control, scalar-Ricci fixed-point collapse, and
analytical index invariance along a Dirac/grading family.
-/
def SinkhornRicciIndexInvariant
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    ∧ (∀ s : ℝ, flow s = 0)
    ∧ IndexInvariantAlong D Γ

/--
Canonical constructor for the coupled invariant package from its three proved
components.
-/
theorem sinkhornRicciIndexInvariant_of_components
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hSinkhorn : ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
      trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
        trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    (hRicciZero : ∀ s : ℝ, flow s = 0)
    (hIndex : IndexInvariantAlong D Γ) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  exact ⟨hSinkhorn, hRicciZero, hIndex⟩

end CoupledInvariant

section KMSCapstone

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Explicit thermodynamic KMS capstone package:
exact KMS closure at each next step.
-/
def SinkhornKMSCapstone
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T K ω β

/-- Lemma `SinkhornKMSCapstone`. -/
lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
  hCap

/--
Constructive iterate specialization from closure (primary closure-first form).
-/
theorem sinkhornIterate_sinkhornKMSCapstone_of_closure
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSCapstone n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  exact hClosure

end KMSCapstone

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Full capstone package:
thermodynamic/KMS control + geometric fixed-point collapse + index invariance.
-/
def FullThermoGeoIndexCapstone
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ ∧
    SinkhornKMSCapstone n T.traj K ω β

/--
Canonical constructor for the full capstone package from the two state-level
components.
-/
theorem fullThermoGeoIndexCapstone_of_states
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hGeoAlg : SinkhornRicciIndexInvariant n T flow D Γ)
    (hClosure : SinkhornKMSClosure n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  exact ⟨hGeoAlg, hClosure⟩

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.geometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornRicciIndexInvariant n T flow D Γ :=
  hCap.1

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.thermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornKMSClosure n T.traj K ω β :=
  hCap.2

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Unified thermodynamic state naming used by higher-level synthesis modules.
-/
abbrev ThermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T.traj K ω β

/--
Unified geometric-algebraic state naming used by higher-level synthesis modules.
-/
abbrev GeometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ

/--
Unified full capstone naming used by higher-level synthesis modules.
-/
abbrev ThermoGeoIndexCapstoneState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  FullThermoGeoIndexCapstone n T flow D Γ K ω β

end UnifiedNaming

end InfoGeometry.Canonical.AnalyticalIndex

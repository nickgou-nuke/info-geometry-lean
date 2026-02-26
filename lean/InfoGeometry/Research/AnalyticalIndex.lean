import InfoGeometry.Research.BottDirac
import InfoGeometry.Research.ChiralAnomaly
import InfoGeometry.Research.KMSSinkhornBridge
import InfoGeometry.Research.RicciMongeAmpere
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

open scoped TensorProduct

namespace InfoGeometry.Research.AnalyticalIndex

open InfoGeometry.Research.BottDirac
open InfoGeometry.Research.ChiralAnomaly
open InfoGeometry.Research.KMSSinkhornBridge
open InfoGeometry.Research.MoE
open InfoGeometry.Research.RicciMongeAmpere

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
Analytical index surrogate:
`Index(D) = dim ker(D⁺) - dim ker(D⁻)`.
-/
noncomputable def analyticalIndex (D Γ : Endomorphism V) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker (chiralPartPlus D Γ)) : ℤ) -
    (Module.finrank ℝ (LinearMap.ker (chiralPartMinus D Γ)) : ℤ)

lemma analyticalIndex_eq_of_chiralParts_eq
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ') :
    analyticalIndex D Γ = analyticalIndex D' Γ' := by
  rw [analyticalIndex, analyticalIndex, hplus, hminus]

/-- Index invariance along a parameterized Dirac/grading family. -/
def IndexInvariantAlong (D Γ : ℝ → Endomorphism V) : Prop :=
  ∀ s : ℝ, analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0)

theorem indexInvariantAlong_of_chiralPart_const
    (D Γ : ℝ → Endomorphism V)
    (hplus : ∀ s : ℝ, chiralPartPlus (D s) (Γ s) = chiralPartPlus (D 0) (Γ 0))
    (hminus : ∀ s : ℝ, chiralPartMinus (D s) (Γ s) = chiralPartMinus (D 0) (Γ 0)) :
    IndexInvariantAlong D Γ := by
  intro s
  exact analyticalIndex_eq_of_chiralParts_eq (D := D s) (Γ := Γ s) (D' := D 0) (Γ' := Γ 0)
    (hplus s) (hminus s)

end Core

section Bott

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global grading on the Bott tensor space: `Γ_bott = Γ₁ ⊗ Γₙ`. -/
def globalGrading (Γ1 : Endomorphism E) (Γn : Endomorphism F) :
    Endomorphism (E ⊗[ℝ] F) :=
  TensorProduct.map Γ1 Γn

/-- Analytical index of the Bott-Dirac operator with chosen grading pair. -/
noncomputable def bottAnalyticalIndex
    (D1 Γ1 : Endomorphism E) (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex (bottDirac D1 Γ1 Dn) (globalGrading Γ1 Γn)

/-- `Cl(1,1)` specialization of the global grading. -/
def cl11GlobalGrading (Γn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  globalGrading (cl11Grading (E := E)) Γn

/-- `Cl(1,1)` specialization of the Bott analytical index. -/
noncomputable def cl11BottAnalyticalIndex (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
    (cl11GlobalGrading (E := E) Γn)

end Bott

section Laplacian

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vanishing condition for the split Bott Laplacian term. -/
def Cl11BottLaplacianZero (Dn : Endomorphism F) : Prop :=
  (TensorProduct.map
    ((cl11DiracSeed (E := E)).comp (cl11DiracSeed (E := E)))
    (LinearMap.id : Endomorphism F))
    +
  (TensorProduct.map
    (LinearMap.id : Endomorphism (DoubledSpace E))
    (Dn.comp Dn)) = 0

theorem cl11_bottDirac_sq_eq_zero_of_laplacian_zero
    (Dn : Endomorphism F)
    (hZero : Cl11BottLaplacianZero (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_sum_laplacians (E := E) (F := F) (Dn := Dn)).trans hZero

end Laplacian

section CoupledInvariant

variable (n : Nat)
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V]

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

theorem sinkhornRicciIndexInvariant_of_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hplus : ∀ s : ℝ, chiralPartPlus (D s) (Γ s) = chiralPartPlus (D 0) (Γ 0))
    (hminus : ∀ s : ℝ, chiralPartMinus (D s) (Γ s) = chiralPartMinus (D 0) (Γ 0)) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine ⟨?_, ?_, ?_⟩
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_chiralPart_const (D := D) (Γ := Γ) hplus hminus

end CoupledInvariant

section KMSCapstone

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Explicit thermodynamic KMS capstone package:
Sinkhorn barrier control plus exact KMS at each next step.
-/
def SinkhornKMSCapstone
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornDrivesToKMS n T K ω β ∧
    SinkhornKMSState n T K ω β

/--
Constructive thermodynamic state directly from the Sinkhorn-to-KMS drive law.
-/
theorem sinkhornKMSState_of_drive
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornDrivesToKMS n T K ω β) :
    SinkhornKMSState n T K ω β := by
  exact sinkhorn_step_exactKMS_of_barrier_control
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hDrive

theorem sinkhornKMSCapstone_of_drive
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornDrivesToKMS n T K ω β) :
    SinkhornKMSCapstone n T K ω β := by
  refine ⟨hDrive, ?_⟩
  exact sinkhornKMSState_of_drive (n := n) (T := T) (K := K) (ω := ω) (β := β) hDrive

lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSState n T K ω β :=
  hCap.2

/--
Constructive iterate specialization of the explicit KMS capstone package.
-/
theorem sinkhornIterate_sinkhornKMSCapstone_of_drive
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornDrivesToKMS n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSCapstone n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  exact sinkhornKMSCapstone_of_drive
    (n := n) (T := sinkhornIterateTrajectory (n := n) M0 hrow hcol)
    (K := K) (ω := ω) (β := β) hDrive

end KMSCapstone

section ConcreteFlow

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Concrete `Cl(1,1)` Bott-Dirac flow model on the deep factor:
time-dependent `Dn, Γn` with pointwise constancy constraints.
-/
structure ConcreteCl11BottFlow (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  Dn : ℝ → Endomorphism F
  Γn : ℝ → Endomorphism F
  Dn_const : ∀ s : ℝ, Dn s = Dn 0
  Γn_const : ∀ s : ℝ, Γn s = Γn 0

/-- Induced Bott-Dirac family on `DoubledSpace E ⊗ F`. -/
def concreteDiracFamily (B : ConcreteCl11BottFlow F) :
    ℝ → Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  fun s => bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (B.Dn s)

/-- Induced global grading family on `DoubledSpace E ⊗ F`. -/
def concreteGradingFamily (B : ConcreteCl11BottFlow F) :
    ℝ → Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  fun s => cl11GlobalGrading (E := E) (B.Γn s)

lemma concreteChiralPartPlus_const
    (B : ConcreteCl11BottFlow F) :
    ∀ s : ℝ,
      chiralPartPlus (concreteDiracFamily (E := E) B s) (concreteGradingFamily (E := E) B s)
        = chiralPartPlus (concreteDiracFamily (E := E) B 0) (concreteGradingFamily (E := E) B 0) := by
  intro s
  simp [concreteDiracFamily, concreteGradingFamily,
    B.Dn_const s, B.Γn_const s]

lemma concreteChiralPartMinus_const
    (B : ConcreteCl11BottFlow F) :
    ∀ s : ℝ,
      chiralPartMinus (concreteDiracFamily (E := E) B s) (concreteGradingFamily (E := E) B s)
        = chiralPartMinus (concreteDiracFamily (E := E) B 0) (concreteGradingFamily (E := E) B 0) := by
  intro s
  simp [concreteDiracFamily, concreteGradingFamily,
    B.Dn_const s, B.Γn_const s]

/--
Stricter derived theorem:
index invariance follows from a concrete Bott-Dirac flow model, without
assuming chiral-part constancy as external hypotheses.
-/
theorem ConcreteCl11BottFlow.indexInvariant
    (B : ConcreteCl11BottFlow F) :
    IndexInvariantAlong
      (concreteDiracFamily (E := E) B)
      (concreteGradingFamily (E := E) B) := by
  exact indexInvariantAlong_of_chiralPart_const
    (D := concreteDiracFamily (E := E) B)
    (Γ := concreteGradingFamily (E := E) B)
    (concreteChiralPartPlus_const (E := E) B)
    (concreteChiralPartMinus_const (E := E) B)

end ConcreteFlow

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup Fth] [NormedSpace ℝ Fth]

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

theorem fullThermoGeoIndexCapstone_of_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hplus : ∀ s : ℝ, chiralPartPlus (D s) (Γ s) = chiralPartPlus (D 0) (Γ 0))
    (hminus : ∀ s : ℝ, chiralPartMinus (D s) (Γ s) = chiralPartMinus (D 0) (Γ 0))
    (hDrive : SinkhornDrivesToKMS n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  refine ⟨?_, ?_⟩
  · exact sinkhornRicciIndexInvariant_of_hypotheses
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      hNorm hFixed hplus hminus
  · exact sinkhornKMSCapstone_of_drive
      (n := n) (T := T.traj) (K := K) (ω := ω) (β := β) hDrive

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup Fth] [NormedSpace ℝ Fth]

/--
Unified thermodynamic state naming used by higher-level synthesis modules.
-/
abbrev ThermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSState n T.traj K ω β

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

end InfoGeometry.Research.AnalyticalIndex

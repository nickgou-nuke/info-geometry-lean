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
Analytical index surrogate:
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

/--
Backward-compatible constant-family criterion.

This derives the chiral-data hypotheses from pointwise constancy of `D` and `Γ`.
-/
theorem indexInvariantAlong_of_chiralPart_const
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hD : ∀ s : ℝ, D s = D 0)
    (hΓ : ∀ s : ℝ, Γ s = Γ 0) :
    IndexInvariantAlong D Γ := by
  refine indexInvariantAlong_of_chiralData_const (D := D) (Γ := Γ) ?_ ?_ ?_ ?_
  · intro s
    simp [chiralPartPlus, hD s, hΓ s]
  · intro s
    simp [chiralPartMinus, hD s, hΓ s]
  · intro s
    simp [hΓ s]
  · intro s
    simp [hΓ s]

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
  [NormedAddCommGroup E] [NormedSpace ℝ E]
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
Constructive Sinkhorn-Ricci-index package from explicit normalized-flow and
constant-family hypotheses.
-/
theorem sinkhornRicciIndexInvariant_of_constructive_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : ∀ s : ℝ, D s = D 0)
    (hΓ : ∀ s : ℝ, Γ s = Γ 0) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine ⟨?_, ?_, ?_⟩
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · refine normalizedKaehlerRicci_fixedpoint_eq_zero (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_chiralPart_const (D := D) (Γ := Γ) hD hΓ

/-- Backward-compatible wrapper. -/
theorem sinkhornRicciIndexInvariant_of_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : ∀ s : ℝ, D s = D 0)
    (hΓ : ∀ s : ℝ, Γ s = Γ 0) :
    SinkhornRicciIndexInvariant n T flow D Γ :=
  sinkhornRicciIndexInvariant_of_constructive_hypotheses
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    hNorm hFixed hD hΓ

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
  SinkhornKMSControl n T K ω β ∧
    SinkhornKMSClosure n T K ω β

/--
Constructive thermodynamic state directly from the Sinkhorn-to-KMS drive law.
-/
theorem sinkhornKMSState_of_drive
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornKMSControl n T K ω β) :
    SinkhornKMSClosure n T K ω β := by
  exact sinkhorn_step_kmsClosure_of_control
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hDrive

/-- Theorem `sinkhornKMSCapstone_of_drive`. -/
theorem sinkhornKMSCapstone_of_drive
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hDrive : SinkhornKMSControl n T K ω β) :
    SinkhornKMSCapstone n T K ω β := by
  refine ⟨hDrive, ?_⟩
  exact sinkhornKMSState_of_drive (n := n) (T := T) (K := K) (ω := ω) (β := β) hDrive

/-- Lemma `SinkhornKMSCapstone`. -/
lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
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
    (hDrive : SinkhornKMSControl n
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
noncomputable def concreteDiracFamily (B : ConcreteCl11BottFlow F) :
    ℝ → Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  fun s => bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) (B.Dn s)

/-- Induced global grading family on `DoubledSpace E ⊗ F`. -/
noncomputable def concreteGradingFamily (B : ConcreteCl11BottFlow F) :
    ℝ → Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  fun s => cl11GlobalGrading (E := E) (B.Γn s)

/-- Lemma `concreteChiralPartPlus_const`. -/
lemma concreteChiralPartPlus_const
    (B : ConcreteCl11BottFlow F) :
    ∀ s : ℝ,
      chiralPartPlus (concreteDiracFamily (E := E) B s) (concreteGradingFamily (E := E) B s)
        = chiralPartPlus (concreteDiracFamily (E := E) B 0) (concreteGradingFamily (E := E) B 0) := by
  intro s
  simp [concreteDiracFamily, concreteGradingFamily,
    B.Dn_const s, B.Γn_const s]

/-- Lemma `concreteChiralPartMinus_const`. -/
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
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (B : ConcreteCl11BottFlow F) :
    IndexInvariantAlong
      (concreteDiracFamily (E := E) B)
      (concreteGradingFamily (E := E) B) := by
  exact indexInvariantAlong_of_chiralPart_const
    (D := concreteDiracFamily (E := E) B)
    (Γ := concreteGradingFamily (E := E) B)
    (by intro s; simp [concreteDiracFamily, B.Dn_const s])
    (by intro s; simp [concreteGradingFamily, B.Γn_const s])

end ConcreteFlow

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
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

/--
Constructive full capstone package:
thermodynamic/KMS drive + normalized Ricci fixed-point + constant Dirac/grading families.
-/
theorem fullThermoGeoIndexCapstone_of_constructive_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : ∀ s : ℝ, D s = D 0)
    (hΓ : ∀ s : ℝ, Γ s = Γ 0)
    (hDrive : SinkhornKMSControl n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  refine ⟨?_, ?_⟩
  · exact sinkhornRicciIndexInvariant_of_constructive_hypotheses
      (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
      hNorm hFixed hD hΓ
  · exact sinkhornKMSCapstone_of_drive
      (n := n) (T := T.traj) (K := K) (ω := ω) (β := β) hDrive

/-- Backward-compatible wrapper. -/
theorem fullThermoGeoIndexCapstone_of_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hD : ∀ s : ℝ, D s = D 0)
    (hΓ : ∀ s : ℝ, Γ s = Γ 0)
    (hDrive : SinkhornKMSControl n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β :=
  fullThermoGeoIndexCapstone_of_constructive_hypotheses
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    (K := K) (ω := ω) (β := β)
    hNorm hFixed hD hΓ hDrive

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
  hCap.2.2

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [NormedSpace ℝ Fth]

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

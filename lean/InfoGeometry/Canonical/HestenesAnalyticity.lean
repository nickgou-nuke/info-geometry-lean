import InfoGeometry.Canonical.HestenesPhaseSemilinear
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.HestenesAnalyticity

Hestenes/geometric reformulation of analytic symmetry closure.

This file does not introduce scalar-complex analyticity, KMS strip analyticity,
Tomita analytic vectors, or holomorphic functional calculus.  It records the
real doubled replacement used by the operator symmetry lane:

* holomorphic/analytic compatibility means preserving the internal phase axis
  `K = Jε`;
* antiholomorphic compatibility means flipping that phase axis;
* Lie/Kac--Moody/Virasoro closure is read through representations whose bracket
  is transported to the operator commutator.

The Kac--Moody and Virasoro algebra owners remain the imported external modules.
This file only proves that their represented symmetry brackets preserve the
Hestenes phase-equivariant sector once the representation and mode laws are
supplied.
-/

namespace InfoGeometry.Canonical.HestenesAnalyticity

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.HestenesPhaseSemilinear

section Core

variable {E F G : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

local notation "H₂E" => DoubledSpace E
local notation "EndE" => H₂E →L[ℝ] H₂E
local notation "H₂F" => DoubledSpace F
local notation "EndF" => H₂F →L[ℝ] H₂F
local notation "H₂G" => DoubledSpace G
local notation "EndG" => H₂G →L[ℝ] H₂G

/-- Differential Hestenes-holomorphicity: the differential intertwines phase axes. -/
@[rep_depth krein]
def IsHestenesHolomorphicDifferential (dF : H₂E →L[ℝ] H₂F) : Prop :=
  dF.comp (InfoGeometry.Krein.clockAxis (E := E)) =
    (InfoGeometry.Krein.clockAxis (E := F)).comp dF

/-- Differential Hestenes-antiholomorphicity: the differential flips phase axes. -/
@[rep_depth krein]
def IsHestenesAntiholomorphicDifferential (dF : H₂E →L[ℝ] H₂F) : Prop :=
  dF.comp (InfoGeometry.Krein.clockAxis (E := E)) =
    -((InfoGeometry.Krein.clockAxis (E := F)).comp dF)

/-- Identity differential is Hestenes-holomorphic. -/
@[rep_depth krein]
theorem id_isHestenesHolomorphicDifferential :
    IsHestenesHolomorphicDifferential (E := E) (F := E)
      (ContinuousLinearMap.id ℝ H₂E) := by
  simp [IsHestenesHolomorphicDifferential]

/-- Hestenes-holomorphic differentials are exactly Hestenes-linear endomorphisms. -/
@[rep_depth krein]
theorem endomorphism_holomorphic_iff_hestenesLinear (A : EndE) :
    IsHestenesHolomorphicDifferential (E := E) (F := E) A ↔
      IsHestenesSemilinear (E := E) PhaseTwist.linear A := by
  rw [isHestenesSemilinear_linear_iff]
  rfl

/-- Hestenes-antiholomorphic differentials are exactly Hestenes-antilinear endomorphisms. -/
@[rep_depth krein]
theorem endomorphism_antiholomorphic_iff_hestenesAntilinear (A : EndE) :
    IsHestenesAntiholomorphicDifferential (E := E) (F := E) A ↔
      IsHestenesSemilinear (E := E) PhaseTwist.antilinear A := by
  rw [isHestenesSemilinear_antilinear_iff]
  rfl

/-- Composition of Hestenes-holomorphic differentials is Hestenes-holomorphic. -/
@[rep_depth krein]
theorem holomorphicDifferential_comp
    {dF : H₂E →L[ℝ] H₂F} {dG : H₂F →L[ℝ] H₂G}
    (hF : IsHestenesHolomorphicDifferential (E := E) (F := F) dF)
    (hG : IsHestenesHolomorphicDifferential (E := F) (F := G) dG) :
    IsHestenesHolomorphicDifferential (E := E) (F := G) (dG.comp dF) := by
  unfold IsHestenesHolomorphicDifferential at hF hG ⊢
  calc
    (dG.comp dF).comp (InfoGeometry.Krein.clockAxis (E := E))
        = dG.comp (dF.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = dG.comp ((InfoGeometry.Krein.clockAxis (E := F)).comp dF) := by rw [hF]
    _ = (dG.comp (InfoGeometry.Krein.clockAxis (E := F))).comp dF := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = ((InfoGeometry.Krein.clockAxis (E := G)).comp dG).comp dF := by rw [hG]
    _ = (InfoGeometry.Krein.clockAxis (E := G)).comp (dG.comp dF) := by
            simp [ContinuousLinearMap.comp_assoc]

/-- Composition of two Hestenes-antiholomorphic differentials is Hestenes-holomorphic. -/
@[rep_depth krein]
theorem antiholomorphicDifferential_comp_antiholomorphic
    {dF : H₂E →L[ℝ] H₂F} {dG : H₂F →L[ℝ] H₂G}
    (hF : IsHestenesAntiholomorphicDifferential (E := E) (F := F) dF)
    (hG : IsHestenesAntiholomorphicDifferential (E := F) (F := G) dG) :
    IsHestenesHolomorphicDifferential (E := E) (F := G) (dG.comp dF) := by
  unfold IsHestenesAntiholomorphicDifferential at hF hG
  unfold IsHestenesHolomorphicDifferential
  calc
    (dG.comp dF).comp (InfoGeometry.Krein.clockAxis (E := E))
        = dG.comp (dF.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = dG.comp (-((InfoGeometry.Krein.clockAxis (E := F)).comp dF)) := by rw [hF]
    _ = -(dG.comp ((InfoGeometry.Krein.clockAxis (E := F)).comp dF)) := by
            simp
    _ = -((dG.comp (InfoGeometry.Krein.clockAxis (E := F))).comp dF) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = -((-((InfoGeometry.Krein.clockAxis (E := G)).comp dG)).comp dF) := by rw [hG]
    _ = (InfoGeometry.Krein.clockAxis (E := G)).comp (dG.comp dF) := by
            simp [ContinuousLinearMap.comp_assoc]

end Core

section SymmetryClosure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Operator commutator on the real doubled endomorphism algebra. -/
@[rep_depth operator]
noncomputable def hestenesSymmetryCommutator (A B : EndH) : EndH :=
  A.comp B - B.comp A

/-- Hestenes-analytic symmetry generator: a real operator preserving the phase axis. -/
@[rep_depth krein]
def IsHestenesAnalyticSymmetry (A : EndH) : Prop :=
  IsHestenesHolomorphicDifferential (E := E) (F := E) A

/-- The identity endomorphism is a Hestenes-analytic symmetry generator.

This is the constructive owner route for the identity-mode branch: callers no
longer need to pass a bare phase-axis-preservation hypothesis for the identity
operator before using commutator closure. -/
@[rep_depth krein]
theorem id_isHestenesAnalyticSymmetry :
    IsHestenesAnalyticSymmetry (E := E) (ContinuousLinearMap.id ℝ H₂) := by
  exact id_isHestenesHolomorphicDifferential (E := E)

/-- Hestenes-analytic symmetry generators are closed under operator commutator. -/
@[rep_depth krein]
theorem hestenesAnalyticSymmetry_commutator
    {A B : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A)
    (hB : IsHestenesAnalyticSymmetry (E := E) B) :
    IsHestenesAnalyticSymmetry (E := E) (hestenesSymmetryCommutator (E := E) A B) := by
  unfold IsHestenesAnalyticSymmetry IsHestenesHolomorphicDifferential at hA hB ⊢
  unfold hestenesSymmetryCommutator
  calc
    (A.comp B - B.comp A).comp (InfoGeometry.Krein.clockAxis (E := E))
        = A.comp (B.comp (InfoGeometry.Krein.clockAxis (E := E))) -
            B.comp (A.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    _ = A.comp ((InfoGeometry.Krein.clockAxis (E := E)).comp B) -
            B.comp ((InfoGeometry.Krein.clockAxis (E := E)).comp A) := by
            rw [hA, hB]
    _ = ((A.comp (InfoGeometry.Krein.clockAxis (E := E))).comp B) -
            ((B.comp (InfoGeometry.Krein.clockAxis (E := E))).comp A) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (((InfoGeometry.Krein.clockAxis (E := E)).comp A).comp B) -
            (((InfoGeometry.Krein.clockAxis (E := E)).comp B).comp A) := by
            rw [hA, hB]
    _ = (InfoGeometry.Krein.clockAxis (E := E)).comp (A.comp B - B.comp A) := by
            simp [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc]

/-- Right-identity commutator branch with the identity analytic witness derived
constructively from `id_isHestenesAnalyticSymmetry` rather than passed as a raw
hypothesis. -/
@[rep_depth krein]
theorem hestenesAnalyticSymmetry_commutator_id_right
    {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E)
      (hestenesSymmetryCommutator (E := E) A (ContinuousLinearMap.id ℝ H₂)) := by
  exact hestenesAnalyticSymmetry_commutator (E := E) hA
    (id_isHestenesAnalyticSymmetry (E := E))

/-- Left-identity commutator branch with the identity analytic witness derived
constructively from `id_isHestenesAnalyticSymmetry` rather than passed as a raw
hypothesis. -/
@[rep_depth krein]
theorem hestenesAnalyticSymmetry_commutator_id_left
    {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E)
      (hestenesSymmetryCommutator (E := E) (ContinuousLinearMap.id ℝ H₂) A) := by
  exact hestenesAnalyticSymmetry_commutator (E := E)
    (id_isHestenesAnalyticSymmetry (E := E)) hA

variable {𝔤 : Type*}
variable [AddCommGroup 𝔤] [Module ℝ 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/--
A represented Lie bracket is Hestenes-analytic when both represented modes are
phase-axis preserving and the bracket is represented by the operator commutator.
-/
@[rep_depth krein]
theorem represented_lieBracket_isHestenesAnalytic
    (ρ : 𝔤 → EndH) {X Y : 𝔤}
    (hρ : ρ ⁅X, Y⁆ = hestenesSymmetryCommutator (E := E) (ρ X) (ρ Y))
    (hX : IsHestenesAnalyticSymmetry (E := E) (ρ X))
    (hY : IsHestenesAnalyticSymmetry (E := E) (ρ Y)) :
    IsHestenesAnalyticSymmetry (E := E) (ρ ⁅X, Y⁆) := by
  rw [hρ]
  exact hestenesAnalyticSymmetry_commutator (E := E) hX hY

end SymmetryClosure

section VirasoroClosure

open VirasoroProject

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Virasoro mode closure in a real Hestenes representation.

The Virasoro algebra itself is owned by `InfoGeometry.External.Virasoro`.  This
readback only says that if a representation sends the Virasoro bracket to the
operator commutator and two modes preserve the Hestenes phase axis, then their
Virasoro bracket mode also preserves it.
-/
@[rep_depth krein]
theorem virasoro_lgen_bracket_isHestenesAnalytic
    (ρ : VirasoroAlgebra ℝ → EndH) (m n : ℤ)
    (hρ : ρ ⁅VirasoroAlgebra.lgen ℝ m, VirasoroAlgebra.lgen ℝ n⁆ =
      hestenesSymmetryCommutator (E := E)
        (ρ (VirasoroAlgebra.lgen ℝ m)) (ρ (VirasoroAlgebra.lgen ℝ n)))
    (hm : IsHestenesAnalyticSymmetry (E := E) (ρ (VirasoroAlgebra.lgen ℝ m)))
    (hn : IsHestenesAnalyticSymmetry (E := E) (ρ (VirasoroAlgebra.lgen ℝ n))) :
    IsHestenesAnalyticSymmetry (E := E)
      (ρ ⁅VirasoroAlgebra.lgen ℝ m, VirasoroAlgebra.lgen ℝ n⁆) := by
  exact represented_lieBracket_isHestenesAnalytic (E := E)
    (𝔤 := VirasoroAlgebra ℝ) ρ hρ hm hn

/-- The Virasoro central generator is central in the imported owner algebra. -/
@[rep_depth operator]
theorem virasoro_central_bracket_zero (Z : VirasoroAlgebra ℝ) :
    ⁅VirasoroAlgebra.cgen ℝ, Z⁆ = 0 := by
  simpa using VirasoroAlgebra.cgen_bracket (𝕜 := ℝ) Z

end VirasoroClosure

section Equivalences

open InfoGeometry.Geometry.BilingualAnalyticity

variable {E F : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂E" => DoubledSpace E
local notation "H₂F" => DoubledSpace F

/-- The canonical phase structure on the doubled carrier is given by `clockAxis`. -/
@[rep_depth krein]
noncomputable def clockPhaseStructure (E : Type 0)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    PhaseStructure (DoubledSpace E) where
  K := InfoGeometry.Krein.clockAxis (E := E)
  K_square := InfoGeometry.Krein.clockAxis_sq (E := E)

/-- Hestenes-holomorphic differentials are exactly phase-linear differentials for `K = clockAxis`. -/
@[rep_depth krein]
theorem isHestenesHolomorphicDifferential_iff_isPhaseLinearMap
    (dF : H₂E →L[ℝ] H₂F) :
    IsHestenesHolomorphicDifferential (E := E) (F := F) dF ↔
      (clockPhaseStructure (E := E)).IsPhaseLinearMap dF (clockPhaseStructure (E := F)) := by
  rfl

/-- Cauchy analyticity for the canonical doubled phase structures is exactly a derivative package
with Hestenes-holomorphic differential. -/
@[rep_depth krein]
noncomputable def cauchyAnalyticAtClockEquiv
    (Fmap : H₂E → H₂F) (x : H₂E) :
    CauchyAnalyticAt (clockPhaseStructure (E := E)) (clockPhaseStructure (E := F)) Fmap x ≃
      { deriv : H₂E →L[ℝ] H₂F //
          HasFDerivAt Fmap deriv x ∧
          IsHestenesHolomorphicDifferential (E := E) (F := F) deriv } where
  toFun A := ⟨A.deriv, A.has_fderiv_at, A.phase_linear_deriv⟩
  invFun s :=
    { deriv := s.1
      has_fderiv_at := s.2.1
      phase_linear_deriv := s.2.2 }
  left_inv A := by
    cases A
    rfl
  right_inv s := by
    cases s
    rfl

variable {Region Point Tangent Value : Type*}
variable [AddCommGroup Value] [Module ℝ Value]
variable (I : GeometricIntegralBackend Region Point Tangent Value)

/-- `HestenesAnalyticOn` is equivalent to its explicit closed-form data. -/
@[rep_depth krein]
noncomputable def hestenesAnalyticOnEquiv (Fgeo : Point → Value) :
    HestenesAnalyticOn I Fgeo ≃
      { ω : OperatorOneForm Point Tangent Value // I.IsClosedGeometricForm ω } where
  toFun A := ⟨A.cauchyForm, A.closed_form⟩
  invFun s := { cauchyForm := s.1, closed_form := s.2 }
  left_inv A := by
    cases A
    rfl
  right_inv s := by
    cases s
    rfl

/-- `BilingualAnalyticAt` is equivalent to its two pieces of data: Cauchy analyticity and a
compatibility backend. -/
@[rep_depth krein]
noncomputable def bilingualAnalyticAtEquiv
    (Fmap : H₂E → H₂F) (Fgeo : Point → Value) (x : H₂E) :
    BilingualAnalyticAt (clockPhaseStructure (E := E)) (clockPhaseStructure (E := F)) I Fmap Fgeo x ≃
      CauchyAnalyticAt (clockPhaseStructure (E := E)) (clockPhaseStructure (E := F)) Fmap x ×
      CauchyHestenesCompatibility (clockPhaseStructure (E := E)) (clockPhaseStructure (E := F)) I where
  toFun A := ⟨A.cauchy, A.compatibility⟩
  invFun s := { cauchy := s.1, compatibility := s.2 }
  left_inv A := by
    cases A
    rfl
  right_inv s := by
    cases s
    rfl

end Equivalences

end InfoGeometry.Canonical.HestenesAnalyticity

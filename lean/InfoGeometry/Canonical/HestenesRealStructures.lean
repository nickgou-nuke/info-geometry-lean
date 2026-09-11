import InfoGeometry.Canonical.HestenesKramersBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.HestenesRealStructures

Carrier-native symmetry structures for the real doubled Hestenes lane.

This file stays strictly in the language
`(H, [·,·], J, ε, K)` with `K = J ∘ ε`, and introduces:

- `KLinear` / `KAntilinear` (`[A,K]=0` / `AK=-KA`),
- `KreinIsometric`, `KreinSelfAdjoint`, `KreinSkewAdjoint`,
- `KramersSymmetry` on the real doubled carrier,
- `MajoranaRealStructure` as a real involution and its fixed sector.
-/

namespace InfoGeometry.Canonical.HestenesRealStructures

open InfoGeometry.Krein
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Carrier-native anticommutator on doubled endomorphisms. -/
@[rep_depth operator]
noncomputable def transportAnticommutator (A B : EndH) : EndH :=
  A.comp B + B.comp A

/-- `K`-linear operators: they commute with the internal phase axis `K = J ∘ ε`. -/
@[rep_depth krein]
abbrev KLinear (A : EndH) : Prop :=
  IsPhaseLinear (E := E) A

/-- `K`-antilinear operators: they anticommute with the internal phase axis `K = J ∘ ε`. -/
@[rep_depth krein]
abbrev KAntilinear (A : EndH) : Prop :=
  IsPhaseAntilinear (E := E) A

/-- Real-linearity plus pairing preservation in the owned Krein metric. -/
@[rep_depth krein]
abbrev KreinIsometric (U : EndH) : Prop :=
  KreinSpace.IsKreinIsometry (H := H₂) U

/-- Real-linearity plus pairing sign-flip in the owned Krein metric. -/
@[rep_depth krein]
abbrev KreinAntiIsometric (U : EndH) : Prop :=
  ∀ u v : H₂,
    KreinSpace.kreinInner (H := H₂) (U u) (U v)
      = -KreinSpace.kreinInner (H := H₂) u v

/-- Krein-selfadjoint operators on the doubled carrier. -/
@[rep_depth krein]
def KreinSelfAdjoint (A : EndH) : Prop :=
  KreinSpace.kreinAdjoint (H := H₂) A = A

/-- Krein-skew operators on the doubled carrier. -/
@[rep_depth krein]
def KreinSkewAdjoint (A : EndH) : Prop :=
  KreinSpace.kreinAdjoint (H := H₂) A = -A

section OmitCompleteLinearityLemmas

omit [CompleteSpace E]

/-- `K`-linearity is exactly vanishing phase-axis commutator. -/
@[rep_depth krein]
theorem kLinear_iff_phaseAxisCommutator_eq_zero (A : EndH) :
    transportCommutator (E := E) A (InfoGeometry.Krein.clockAxis (E := E)) = 0 ↔
      KLinear (E := E) A := by
  let K := InfoGeometry.Krein.clockAxis (E := E)
  show A.comp K - K.comp A = 0 ↔ A.comp K = K.comp A
  simpa using (sub_eq_zero : A.comp K - K.comp A = 0 ↔ A.comp K = K.comp A)

/-- `K`-antilinearity is exactly vanishing phase-axis anticommutator. -/
@[rep_depth krein]
theorem kAntilinear_iff_phaseAxisAnticommutator_eq_zero (A : EndH) :
    transportAnticommutator (E := E) A (InfoGeometry.Krein.clockAxis (E := E)) = 0 ↔
      KAntilinear (E := E) A := by
  let K := InfoGeometry.Krein.clockAxis (E := E)
  show A.comp K + K.comp A = 0 ↔ A.comp K = -(K.comp A)
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_left h
  · intro h
    calc
      A.comp K + K.comp A = -(K.comp A) + K.comp A := by rw [h]
      _ = 0 := by abel

end OmitCompleteLinearityLemmas

section OmitCompletePhaseAxisLinear

omit [CompleteSpace E]

/-- The internal phase axis `K` is `K`-linear (it commutes with itself). -/
@[rep_depth krein]
theorem phaseAxisK_isKLinear :
    KLinear (E := E) (InfoGeometry.Krein.clockAxis (E := E)) := by
  apply (kLinear_iff_phaseAxisCommutator_eq_zero (E := E)
    (InfoGeometry.Krein.clockAxis (E := E))).1
  unfold transportCommutator
  simp

end OmitCompletePhaseAxisLinear

/-- The internal phase axis `K` is the canonical Krein anti-isometric axis. -/
@[rep_depth krein]
theorem phaseAxisK_isKreinAntiIsometric :
    KreinAntiIsometric (E := E) (InfoGeometry.Krein.clockAxis (E := E)) := by
  intro u v
  exact InfoGeometry.Canonical.TomitaTakesaki.clockAxis_kreinInner_comp (E := E) u v

/-!
Canonical intrinsic phase axis package for the real doubled Kramers lane.
-/
@[rep_depth krein]
structure PhaseKramersAxis where
  Θ : EndH
  kreinAntiIsometric : KreinAntiIsometric (E := E) Θ
  phaseLinear : KLinear (E := E) Θ
  square_neg : Θ.comp Θ = -(ContinuousLinearMap.id ℝ H₂)

/-- Canonical phase-axis Kramers data owned by `K = J ∘ ε`. -/
@[rep_depth krein]
noncomputable def canonicalPhaseKramersAxis : PhaseKramersAxis (E := E) where
  Θ := InfoGeometry.Krein.clockAxis (E := E)
  kreinAntiIsometric := phaseAxisK_isKreinAntiIsometric (E := E)
  phaseLinear := phaseAxisK_isKLinear (E := E)
  square_neg := InfoGeometry.Krein.clockAxis_sq (E := E)

/--
Kramers symmetry on the real doubled carrier:
Krein isometric, phase-antilinear, and squares to `-1`.
-/
@[rep_depth krein]
structure KramersSymmetry where
  Θ : EndH
  kreinIsometric : KreinIsometric (E := E) Θ
  phaseAntilinear : KAntilinear (E := E) Θ
  square_neg : Θ.comp Θ = -(ContinuousLinearMap.id ℝ H₂)

namespace KramersSymmetry

variable (S : KramersSymmetry (E := E))

/-- The canonical Kramers pair `(u, Θu)`. -/
@[rep_depth krein]
noncomputable def pair (u : H₂) : H₂ × H₂ := (u, S.Θ u)

/-- Pairing is preserved by a Kramers symmetry. -/
@[rep_depth krein]
theorem preserves_kreinInner (u v : H₂) :
    KreinSpace.kreinInner (H := H₂) (S.Θ u) (S.Θ v)
      = KreinSpace.kreinInner (H := H₂) u v :=
  S.kreinIsometric u v

/-- Phase-antilinearity written directly against `K = phaseAxisK`. -/
@[rep_depth krein]
theorem anticomm_phaseAxisK :
    S.Θ.comp (InfoGeometry.Krein.clockAxis (E := E))
      =
    -((InfoGeometry.Krein.clockAxis (E := E)).comp S.Θ) := by
  simpa [KAntilinear, IsPhaseAntilinear] using
    S.phaseAntilinear

/-- Nontriviality of Kramers partner for nonzero vectors. -/
@[rep_depth krein]
theorem partner_ne_self_of_ne_zero {u : H₂} (hu : u ≠ 0) :
    S.Θ u ≠ u := by
  intro hEq
  have hSqApply : S.Θ (S.Θ u) = -u := by
    exact congrArg (fun F : EndH => F u) S.square_neg
  have hApply : S.Θ (S.Θ u) = S.Θ u := by
    exact congrArg S.Θ hEq
  have hNeg : -u = u := by
    calc
      -u = S.Θ (S.Θ u) := by simpa using hSqApply.symm
      _ = S.Θ u := hApply
      _ = u := hEq
  have hTwoSum : u + u = 0 := by
    calc
      u + u = u + (-u) := by rw [hNeg]
      _ = 0 := by simp
  have hTwoSmul : (2 : ℝ) • u = 0 := by
    simpa [two_smul] using hTwoSum
  have hu0 : u = 0 := (smul_eq_zero.mp hTwoSmul).resolve_left (by norm_num)
  exact hu hu0

end KramersSymmetry

/--
Majorana real structure on the doubled carrier:
an involution preserving Krein pairing and compatible with `K` and `ε`.
-/
@[rep_depth krein]
structure MajoranaRealStructure where
  C : EndH
  involutive : C.comp C = ContinuousLinearMap.id ℝ H₂
  kreinIsometric : KreinIsometric (E := E) C
  phaseLinear : KLinear (E := E) C
  gradingLinear :
    C.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp C

namespace MajoranaRealStructure

variable (M : MajoranaRealStructure (E := E))

/-- Majorana fixed-point predicate on the doubled carrier. -/
@[rep_depth krein]
def IsMajorana (u : H₂) : Prop := M.C u = u

/-- The Majorana fixed sector as a real submodule. -/
@[rep_depth krein]
def fixedSubmodule : Submodule ℝ H₂ where
  carrier := { u : H₂ | M.IsMajorana u }
  zero_mem' := by simp [IsMajorana]
  add_mem' := by
    intro u v hu hv
    change M.C (u + v) = u + v
    have hu' : M.C u = u := hu
    have hv' : M.C v = v := hv
    calc
      M.C (u + v) = M.C u + M.C v := by exact M.C.map_add u v
      _ = u + v := by simp [hu', hv']
  smul_mem' := by
    intro c u hu
    change M.C (c • u) = c • u
    have hu' : M.C u = u := hu
    calc
      M.C (c • u) = c • (M.C u) := by exact M.C.map_smul c u
      _ = c • u := by simp [hu']

/-- Involution fixes Majorana vectors on second application. -/
@[rep_depth krein]
theorem apply_apply_eq_self (u : H₂) :
    M.C (M.C u) = u := by
  exact congrArg (fun F : EndH => F u) M.involutive

/-- The fixed sector is stable under the internal phase axis `K`. -/
@[rep_depth krein]
theorem phaseAxis_closed {u : H₂} (hu : M.IsMajorana u) :
    M.IsMajorana ((InfoGeometry.Krein.clockAxis (E := E)) u) := by
  have hComm :
      M.C.comp (InfoGeometry.Krein.clockAxis (E := E))
        = (InfoGeometry.Krein.clockAxis (E := E)).comp M.C := by
    simpa [KLinear, IsPhaseLinear] using
      M.phaseLinear
  unfold IsMajorana at hu ⊢
  calc
    M.C ((InfoGeometry.Krein.clockAxis (E := E)) u)
        = (M.C.comp (InfoGeometry.Krein.clockAxis (E := E))) u := rfl
    _ = ((InfoGeometry.Krein.clockAxis (E := E)).comp M.C) u := by rw [hComm]
    _ = (InfoGeometry.Krein.clockAxis (E := E)) (M.C u) := rfl
    _ = (InfoGeometry.Krein.clockAxis (E := E)) u := by rw [hu]

/-- The fixed sector is stable under the grading axis `ε`. -/
@[rep_depth krein]
theorem grading_closed {u : H₂} (hu : M.IsMajorana u) :
    M.IsMajorana ((spectral_epsilon (E := E)) u) := by
  unfold IsMajorana at hu ⊢
  calc
    M.C ((spectral_epsilon (E := E)) u)
        = (M.C.comp (spectral_epsilon (E := E))) u := rfl
    _ = ((spectral_epsilon (E := E)).comp M.C) u := by rw [M.gradingLinear]
    _ = (spectral_epsilon (E := E)) (M.C u) := rfl
    _ = (spectral_epsilon (E := E)) u := by rw [hu]

end MajoranaRealStructure

end Core

end InfoGeometry.Canonical.HestenesRealStructures

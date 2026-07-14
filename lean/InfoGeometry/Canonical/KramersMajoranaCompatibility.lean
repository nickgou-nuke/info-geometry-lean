import InfoGeometry.Canonical.TimeReversalKramers
import InfoGeometry.Canonical.KramersPhaseAxisReduction
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KramersMajoranaCompatibility

Compatibility bridge between:
- abstract doubled-carrier Kramers symmetries `Θ`,
- intrinsic phase-axis partner map `K`,
- and Majorana fixed sectors defined by a real involution `C`.
-/

namespace KramersMajoranaCompatibility

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.HestenesKramersBridge
open InfoGeometry.Canonical.OperatorDictionary

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Compatibility package for the two doubled-real symmetry layers:
Kramers symmetry `Θ` and Majorana involution `C`.
-/
@[rep_depth krein]
structure KramersMajoranaCompatible where
  S : KramersSymmetry (E := E)
  M : MajoranaRealStructure (E := E)
  commute_C_Theta : Commute M.C S.Θ

namespace KramersMajoranaCompatible

variable (X : KramersMajoranaCompatible (E := E))

/-- Canonical right factor from the phase-axis reduction lane: `R := -(Θ ∘ K)`. -/
@[rep_depth krein]
noncomputable def phaseReductionFactor : EndH :=
  InfoGeometry.Canonical.KramersPhaseAxisReduction.phaseAxisRightFactor
    (E := E) X.S.Θ

/-- If `C` commutes with `Θ`, the Majorana fixed sector is stable under `Θ`. -/
@[rep_depth krein]
theorem majorana_closed_theta
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.S.Θ u) := by
  unfold MajoranaRealStructure.IsMajorana at hu ⊢
  calc
    X.M.C (X.S.Θ u) = (X.M.C * X.S.Θ) u := rfl
    _ = (X.S.Θ * X.M.C) u := by rw [X.commute_C_Theta.eq]
    _ = X.S.Θ (X.M.C u) := rfl
    _ = X.S.Θ u := by rw [hu]

/--
Capstone API name: if `C` commutes with `Θ`, then `Θ` preserves the
Majorana fixed sector.
-/
@[rep_depth krein]
theorem theta_preserves_majoranaFix_of_commute_C
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.S.Θ u) :=
  X.majorana_closed_theta hu

/-- The Majorana fixed sector is stable under the intrinsic phase partner `K u`. -/
@[rep_depth krein]
theorem majorana_closed_phasePartner
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (phasePartner (E := E) u) := by
  simpa [phasePartner] using X.M.phaseAxis_closed hu

/--
Mixed-channel stability:
if `u` is Majorana, then the Kramers image of its phase partner is Majorana.
-/
@[rep_depth krein]
theorem majorana_closed_theta_phasePartner
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.S.Θ (phasePartner (E := E) u)) := by
  exact X.majorana_closed_theta (X.majorana_closed_phasePartner hu)

/--
Canonical reduction identity imported from `KramersPhaseAxisReduction`:
`Θ = R ∘ K` with `R := -(Θ ∘ K)`.
-/
@[rep_depth krein]
theorem theta_eq_phaseReductionFactor_comp_phaseAxisK :
    X.S.Θ = X.phaseReductionFactor.comp (phaseAxisK (E := E)) := by
  simpa [phaseReductionFactor] using
    (InfoGeometry.Canonical.KramersPhaseAxisReduction.theta_eq_R_comp_phaseAxisK_of_phaseReduction
      (E := E) X.S)

/--
Majorana stability of the canonical reduction factor:
if `u` is Majorana, then `R u` is Majorana for `R := -(Θ ∘ K)`.
-/
@[rep_depth krein]
theorem majorana_closed_phaseReductionFactor
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.phaseReductionFactor u) := by
  have hK : X.M.IsMajorana (phasePartner (E := E) u) :=
    X.majorana_closed_phasePartner hu
  have hThetaK : X.M.IsMajorana (X.S.Θ (phasePartner (E := E) u)) :=
    X.majorana_closed_theta hK
  unfold phaseReductionFactor
  unfold MajoranaRealStructure.IsMajorana at hThetaK ⊢
  calc
    X.M.C
        (InfoGeometry.Canonical.KramersPhaseAxisReduction.phaseAxisRightFactor
          (E := E) X.S.Θ u)
      =
    X.M.C (-(X.S.Θ (phasePartner (E := E) u))) := by
      simp [InfoGeometry.Canonical.KramersPhaseAxisReduction.phaseAxisRightFactor, phasePartner]
    _ = -(X.M.C (X.S.Θ (phasePartner (E := E) u))) := by simp
    _ = -(X.S.Θ (phasePartner (E := E) u)) := by rw [hThetaK]
    _ =
      InfoGeometry.Canonical.KramersPhaseAxisReduction.phaseAxisRightFactor
        (E := E) X.S.Θ u := by
          simp [InfoGeometry.Canonical.KramersPhaseAxisReduction.phaseAxisRightFactor, phasePartner]

/--
Bridge law between abstract Kramers action and intrinsic phase partner:
`Θ (K u) = -K (Θ u)`.
-/
@[rep_depth krein]
theorem theta_phasePartner_eq_neg_phasePartner_theta
    (u : H₂) :
    X.S.Θ (phasePartner (E := E) u)
      =
    -(phasePartner (E := E) (X.S.Θ u)) := by
  have hApply := congrArg (fun F : EndH => F u) X.S.anticomm_phaseAxisK
  simpa [phasePartner, phaseAxisK] using hApply

/--
Pair-level compatibility:
if `u` is Majorana, both entries in `(u, Θu)` lie in the Majorana fixed sector.
-/
@[rep_depth krein]
theorem majorana_closed_kramersPair
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.S.pair u).1 ∧ X.M.IsMajorana (X.S.pair u).2 := by
  refine ⟨?_, ?_⟩
  · simpa [KramersSymmetry.pair] using hu
  · simpa [KramersSymmetry.pair] using X.majorana_closed_theta hu

/--
Pair-level compatibility on the intrinsic phase-partner input:
if `u` is Majorana, both entries in `(Ku, Θ(Ku))` are Majorana.
-/
@[rep_depth krein]
theorem majorana_closed_kramersPair_phasePartner
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.M.IsMajorana (X.S.pair (phasePartner (E := E) u)).1
      ∧
    X.M.IsMajorana (X.S.pair (phasePartner (E := E) u)).2 := by
  exact X.majorana_closed_kramersPair (X.majorana_closed_phasePartner hu)

/--
Unified reduction/compatibility package:
1. canonical phase reduction `Θ = R ∘ K`,
2. Majorana stability of `Θ`,
3. Majorana stability of the canonical reduced factor `R`.
-/
@[rep_depth krein]
theorem kramers_majorana_phaseReduction_package
    {u : H₂}
    (hu : X.M.IsMajorana u) :
    X.S.Θ = X.phaseReductionFactor.comp (phaseAxisK (E := E))
      ∧
    X.M.IsMajorana (X.S.Θ u)
      ∧
    X.M.IsMajorana (X.phaseReductionFactor u) := by
  refine ⟨X.theta_eq_phaseReductionFactor_comp_phaseAxisK, ?_, ?_⟩
  · exact X.majorana_closed_theta hu
  · exact X.majorana_closed_phaseReductionFactor hu

end KramersMajoranaCompatible

end Core

end KramersMajoranaCompatibility

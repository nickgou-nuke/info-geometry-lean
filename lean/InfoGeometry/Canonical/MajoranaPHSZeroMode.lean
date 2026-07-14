import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.BoundaryProjector
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.MajoranaPHSZeroMode

Canonical finite PHS/zero-mode surface over the doubled Tomita-Krein atom.

This module keeps the three notions separate:

* PHS / Majorana reality: `J γ J = γ`;
* boundary zero mode: `CCRBracket H γ = 0`;
* support in a selected corner projector: `P₀ (γ P₀) = γ`.

The finite `Cl(1,1)` swap already exists in
`TomitaKreinNilpotentAtom`; this file only packages the operator-level
predicates and exports the concrete PHS swap as a clean canonical surface.
-/

namespace MajoranaPHSZeroMode

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. PHS and zero-mode predicates -/

/-- PHS / Majorana reality: fixed by Tomita/PHS conjugation. -/
def IsPHSInvariant (T : FockEndomorphism E) : Prop :=
  tomitaConjOp (E := E) T = T

/-- Boundary zero mode: the operator commutes with the chosen boundary generator. -/
def IsBoundaryZeroMode (H T : FockEndomorphism E) : Prop :=
  CCRBracket (E := E) H T = 0

/-- Krein-self-adjoint and PHS-invariant on the doubled carrier. -/
def IsMajoranaOperator (T : FockEndomorphism E) : Prop :=
  KreinSpace.IsKreinSelfAdjoint (H := DoubledSpace E) T ∧ IsPHSInvariant (E := E) T

/-- Corner support by an idempotent/projector `P₀`, stated directly on operators. -/
def IsSupportedInCorner (P₀ T : FockEndomorphism E) : Prop :=
  P₀.comp (T.comp P₀) = T

/--
Majorana/PHS zero mode in a selected corner.

This is deliberately a plain proposition over a supplied operator projector,
not a wrapper datum: projection laws are imported/proved separately by the
projector owner, e.g. `boundaryProjector_idempotent` or
`spectralPlusProj_idempotent`.
-/
def IsMajoranaPHSZeroMode
    (P₀ H T : FockEndomorphism E) : Prop :=
  IsSupportedInCorner (E := E) P₀ T
    ∧ IsMajoranaOperator (E := E) T
    ∧ IsBoundaryZeroMode (E := E) H T

/-- Any boundary generator commutes with itself. -/
theorem boundaryGenerator_is_boundary_zero_mode
    (H : FockEndomorphism E) :
    IsBoundaryZeroMode (E := E) H H := by
  simp [IsBoundaryZeroMode, CCRBracket]

/-- The canonical `K = J ∘ ε` boundary lane is stationary with respect to itself. -/
theorem cptSuperchargeOp_is_boundary_zero_mode :
    IsBoundaryZeroMode (E := E)
      (cptSuperchargeOp (E := E))
      (cptSuperchargeOp (E := E)) := by
  simpa using (boundaryGenerator_is_boundary_zero_mode (E := E) (cptSuperchargeOp (E := E)))

/--
The canonical boundary projector is supported in its own corner.

This is the exact projection-side statement used by the zero-mode lane:
the boundary projector is idempotent, hence stable under its own corner
compression.
-/
theorem boundaryProjector_supportedInCorner
    (Δ : FockEndomorphism E)
    [(boundarySubspace (E := E) Δ).HasOrthogonalProjection] :
    IsSupportedInCorner (E := E)
      (boundaryProjector (E := E) Δ) (boundaryProjector (E := E) Δ) := by
  have h := boundaryProjector_idempotent (E := E) Δ
  simpa [IsSupportedInCorner, ContinuousLinearMap.comp_assoc, h] using
    (congrArg (fun f : FockEndomorphism E => f.comp (boundaryProjector (E := E) Δ)) h)

/--
Finite Majorana/PHS zero-mode package on the canonical split boundary lane.

This packages the two concrete finite facts that are already owned separately:
PHS invariance of the real Majorana swap and boundary-zero-mode closure of the
Tomita CPT generator.
-/
theorem concreteMajoranaPHSZeroModePackage :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) ∧
    IsBoundaryZeroMode (E := E)
      (cptSuperchargeOp (E := E))
      (cptSuperchargeOp (E := E)) := by
  refine ⟨concrete_majorana_swap_is_phs_invariant (E := E),
    cptSuperchargeOp_is_boundary_zero_mode (E := E)⟩

/-! ## 2. Canonical projector/corner facts -/

/-- The `+` spectral projector is supported in its own canonical corner. -/
theorem spectralPlusProj_supportedInCorner :
    IsSupportedInCorner (E := E)
      (spectralPlusProj (E := E)) (spectralPlusProj (E := E)) := by
  simp [IsSupportedInCorner, spectralPlusProj_idempotent (E := E)]

/-- The `-` spectral projector is supported in its own canonical corner. -/
theorem spectralMinusProj_supportedInCorner :
    IsSupportedInCorner (E := E)
      (spectralMinusProj (E := E)) (spectralMinusProj (E := E)) := by
  simp [IsSupportedInCorner, spectralMinusProj_idempotent (E := E)]

/-! ## 3. Concrete finite PHS swap -/

/-- The concrete split-null creation operator is sent to annihilation by Tomita/PHS. -/
theorem concrete_majorana_creation_swap :
    tomitaConjOp (E := E) (concreteCARCreation (E := E))
      = concreteCARAnnihilation (E := E) := by
  simpa using (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.tomitaConj_creation_eq_annihilation (E := E))

/-- The concrete split-null annihilation operator is sent to creation by Tomita/PHS. -/
theorem concrete_majorana_annihilation_swap :
    tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) := by
  simpa using
    (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.tomitaConj_annihilation_eq_creation (E := E))

/-- The concrete Majorana swap `u₊ + u₋` is Tomita/PHS invariant. -/
theorem concrete_majorana_swap_is_phs_invariant :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) := by
  simpa [IsPHSInvariant] using
    (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.concrete_majorana_swap_is_phs_invariant (E := E))

/-- The concrete Majorana swap is exactly the modular swap on the doubled carrier. -/
theorem concrete_majorana_swap_eq_modular_j :
    concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)
      = modular_j (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.add_apply,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled,
      add_comm]

/-- The modular swap is Hilbert-self-adjoint on the doubled carrier. -/
theorem modular_j_isHilbertSelfAdjoint :
    ContinuousLinearMap.adjoint (modular_j (E := E)) = modular_j (E := E) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (A := modular_j (E := E))
    (B := modular_j (E := E))).2 ?_
  intro u v
  simp [modular_j_apply, WithLp.prod_inner_apply, add_comm]

/-- The modular swap is Krein-skew-adjoint on the doubled carrier. -/
theorem modular_j_isKreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := DoubledSpace E) (modular_j (E := E)) := by
  rw [KreinSpace.isKreinSkewAdjoint_iff]
  intro u v
  rcases u with ⟨x, ξ⟩
  rcases v with ⟨y, η⟩
  change
    KreinSpace.kreinInner (H := DoubledSpace E)
        (modular_j (E := E) (InfoGeometry.Krein.to_doubled x ξ))
        (InfoGeometry.Krein.to_doubled y η)
      + KreinSpace.kreinInner (H := DoubledSpace E)
          (InfoGeometry.Krein.to_doubled x ξ)
          (modular_j (E := E) (InfoGeometry.Krein.to_doubled y η))
      = 0
  repeat rw [InfoGeometry.Krein.krein_inner_prod_l2]
  simp [modular_j_to_doubled, add_comm, add_left_comm, add_assoc]

/-- The concrete Majorana boundary swap is Krein-skew-adjoint. -/
theorem concrete_majorana_swap_isKreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := DoubledSpace E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) := by
  rw [concrete_majorana_swap_eq_modular_j (E := E)]
  exact modular_j_isKreinSkewAdjoint (E := E)

end Core

end MajoranaPHSZeroMode

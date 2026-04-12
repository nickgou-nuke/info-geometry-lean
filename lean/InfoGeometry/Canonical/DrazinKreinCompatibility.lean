import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Clifford.Grading
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinKreinCompatibility

Krein/graded compatibility layer for Drazin regularization on doubled carriers.

This file is intentionally structural:
- no spectral contour calculus;
- no KK/Fredholm consequences;
- no determinant/trace-class analytics.

It packages the compatibility conditions with the fundamental symmetry and
grading operators, then derives the defect-projector algebra (`P₀`) from the
owner Drazin witness.

Methodological note:
- the Drazin split is spectral in origin (`0`-singular vs. regular sector);
- Jordan/Lie/Cartan geometry is a candidate realization layer for that split;
- equalities between spectral sectors and geometric sectors are capstone
  theorems, not definitions.
-/

namespace InfoGeometry.Canonical.DrazinKreinCompatibility

open InfoGeometry.Canonical
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Op" => DoubledSpace E →L[ℝ] DoubledSpace E

/--
`η`-adjoint transport on the doubled carrier.

This is the metric-aware adjoint surface used to state compatibility claims
without introducing weighted-Drazin structure in this owner file.
-/
noncomputable abbrev etaAdjoint (η T : Op) : Op :=
  η * (ContinuousLinearMap.adjoint T) * η

/-- `η`-selfadjointness predicate on doubled-space operators. -/
def IsEtaSelfAdjoint (η T : Op) : Prop :=
  etaAdjoint (E := E) η T = T

/-- Chiral `+` projector from `ε`. -/
noncomputable abbrev chiralPlus :
    DoubledSpace E →L[ℝ] DoubledSpace E := spectralPlusProj (E := E)

/-- Chiral `-` projector from `ε`. -/
noncomputable abbrev chiralMinus :
    DoubledSpace E →L[ℝ] DoubledSpace E := spectralMinusProj (E := E)

/-- Drazin regular (invertible) block projector `P = T * Tᴰ`. -/
noncomputable abbrev Preg
    (T TD : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  IsDrazinInverse.projection T TD

/-- Drazin defect/null block projector `P₀ = 1 - P`. -/
noncomputable abbrev Pzero
    (T TD : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  IsDrazinInverse.complementaryProjection T TD

/--
Krein-graded compatibility package for a Drazin-regularized operator.

`η` is a chosen fundamental symmetry, while `ε` and `J` are the canonical
doubled-space grading/swap operators.
-/
@[rep_depth operator]
structure KreinGradedDrazinCompatibility
    (T TD : DoubledSpace E →L[ℝ] DoubledSpace E) (k : ℕ) where
  hD : IsDrazinInverse T TD k
  η : DoubledSpace E →L[ℝ] DoubledSpace E
  η_sq : η.comp η = ContinuousLinearMap.id ℝ (DoubledSpace E)
  η_star : star η = η
  η_comm_T : η.comp T = T.comp η
  η_comm_TD : η.comp TD = TD.comp η
  ε_comm_T : (spectral_epsilon (E := E)).comp T = T.comp (spectral_epsilon (E := E))
  ε_comm_TD : (spectral_epsilon (E := E)).comp TD = TD.comp (spectral_epsilon (E := E))
  J_comm_T : (modular_j (E := E)).comp T = T.comp (modular_j (E := E))
  J_comm_TD : (modular_j (E := E)).comp TD = TD.comp (modular_j (E := E))

section Algebra

variable {T TD : DoubledSpace E →L[ℝ] DoubledSpace E} {k : ℕ}

/-- `P = T*Tᴰ` is idempotent in the Krein-compatible Drazin lane. -/
@[rep_depth operator]
theorem Preg_idempotent :
    KreinGradedDrazinCompatibility (E := E) T TD k →
    Preg T TD * Preg T TD = Preg T TD := by
  intro hCompat
  change IsDrazinInverse.projection T TD * IsDrazinInverse.projection T TD
      = IsDrazinInverse.projection T TD
  exact IsDrazinInverse.projection_is_idempotent hCompat.hD

/-- `P₀ = 1 - P` is idempotent in the Krein-compatible Drazin lane. -/
@[rep_depth operator]
theorem Pzero_idempotent :
    KreinGradedDrazinCompatibility (E := E) T TD k →
    Pzero T TD * Pzero T TD = Pzero T TD := by
  intro hCompat
  change IsDrazinInverse.complementaryProjection T TD
      * IsDrazinInverse.complementaryProjection T TD
      = IsDrazinInverse.complementaryProjection T TD
  exact IsDrazinInverse.complementaryProjection_is_idempotent hCompat.hD

/-- Orthogonality `P * P₀ = 0`. -/
@[rep_depth operator]
theorem Preg_mul_Pzero :
    KreinGradedDrazinCompatibility (E := E) T TD k →
    Preg T TD * Pzero T TD = 0 := by
  intro hCompat
  change IsDrazinInverse.projection T TD * IsDrazinInverse.complementaryProjection T TD = 0
  exact IsDrazinInverse.projection_mul_complementaryProjection hCompat.hD

/-- Orthogonality `P₀ * P = 0`. -/
@[rep_depth operator]
theorem Pzero_mul_Preg :
    KreinGradedDrazinCompatibility (E := E) T TD k →
    Pzero T TD * Preg T TD = 0 := by
  intro hCompat
  change IsDrazinInverse.complementaryProjection T TD * IsDrazinInverse.projection T TD = 0
  exact IsDrazinInverse.complementaryProjection_mul_projection hCompat.hD

/-- Decomposition identity `P + P₀ = 1`. -/
@[rep_depth operator]
theorem Preg_add_Pzero :
    Preg T TD + Pzero T TD = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  change IsDrazinInverse.projection T TD + IsDrazinInverse.complementaryProjection T TD
      = (1 : DoubledSpace E →L[ℝ] DoubledSpace E)
  exact IsDrazinInverse.projection_add_complementaryProjection (a := T) (b := TD)

/-- Canonical chiral decomposition `P₊ + P₋ = 1`. -/
@[rep_depth operator]
theorem Pplus_add_Pminus :
    chiralPlus (E := E) + chiralMinus (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [chiralPlus, chiralMinus] using (krein_projector_completeness (E := E))

private theorem commutes_with_Preg
    {S T TD : Op}
    (hST : S.comp T = T.comp S)
    (hSTD : S.comp TD = TD.comp S) :
    S.comp (Preg T TD) = (Preg T TD).comp S := by
  apply ContinuousLinearMap.ext
  intro x
  have hSTx : S (T (TD x)) = T (S (TD x)) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : Op => f (TD x)) hST
  have hSTDx : S (TD x) = TD (S x) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : Op => f x) hSTD
  calc
    (S.comp (Preg T TD)) x = S (T (TD x)) := by rfl
    _ = T (S (TD x)) := hSTx
    _ = T (TD (S x)) := by rw [hSTDx]
    _ = ((Preg T TD).comp S) x := by rfl

private theorem commutes_with_Pzero
    {S T TD : Op}
    (hSP : S.comp (Preg T TD) = (Preg T TD).comp S) :
    S.comp (Pzero T TD) = (Pzero T TD).comp S := by
  apply ContinuousLinearMap.ext
  intro x
  have hSPx : S ((Preg T TD) x) = (Preg T TD) (S x) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun f : Op => f x) hSP
  calc
    (S.comp (Pzero T TD)) x = S x - S ((Preg T TD) x) := by
      simp [Pzero, IsDrazinInverse.complementaryProjection,
        Preg, IsDrazinInverse.projection]
    _ = S x - (Preg T TD) (S x) := by rw [hSPx]
    _ = ((Pzero T TD).comp S) x := by
      simp [Pzero, IsDrazinInverse.complementaryProjection,
        Preg, IsDrazinInverse.projection]

/--
`η`-compatibility descends from `(T, Tᴰ)` to the Drazin regular projector.
-/
@[rep_depth operator]
theorem eta_comm_Preg
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    hCompat.η.comp (Preg T TD) = (Preg T TD).comp hCompat.η :=
  commutes_with_Preg
    (S := hCompat.η)
    (T := T) (TD := TD)
    hCompat.η_comm_T hCompat.η_comm_TD

/--
`ε`-compatibility descends from `(T, Tᴰ)` to the Drazin regular projector.
-/
@[rep_depth operator]
theorem epsilon_comm_Preg
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (spectral_epsilon (E := E)).comp (Preg T TD)
      = (Preg T TD).comp (spectral_epsilon (E := E)) :=
  commutes_with_Preg
    (S := spectral_epsilon (E := E))
    (T := T) (TD := TD)
    hCompat.ε_comm_T hCompat.ε_comm_TD

/--
`J`-compatibility descends from `(T, Tᴰ)` to the Drazin regular projector.
-/
@[rep_depth operator]
theorem modularJ_comm_Preg
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (modular_j (E := E)).comp (Preg T TD)
      = (Preg T TD).comp (modular_j (E := E)) :=
  commutes_with_Preg
    (S := modular_j (E := E))
    (T := T) (TD := TD)
    hCompat.J_comm_T hCompat.J_comm_TD

/--
`η`-compatibility descends from `(T, Tᴰ)` to the Drazin defect projector.
-/
@[rep_depth operator]
theorem eta_comm_Pzero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    hCompat.η.comp (Pzero T TD) = (Pzero T TD).comp hCompat.η :=
  commutes_with_Pzero
    (S := hCompat.η)
    (T := T) (TD := TD)
    (eta_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
`ε`-compatibility descends from `(T, Tᴰ)` to the Drazin defect projector.
-/
@[rep_depth operator]
theorem epsilon_comm_Pzero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (spectral_epsilon (E := E)).comp (Pzero T TD)
      = (Pzero T TD).comp (spectral_epsilon (E := E)) :=
  commutes_with_Pzero
    (S := spectral_epsilon (E := E))
    (T := T) (TD := TD)
    (epsilon_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
`J`-compatibility descends from `(T, Tᴰ)` to the Drazin defect projector.
-/
@[rep_depth operator]
theorem modularJ_comm_Pzero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (modular_j (E := E)).comp (Pzero T TD)
      = (Pzero T TD).comp (modular_j (E := E)) :=
  commutes_with_Pzero
    (S := modular_j (E := E))
    (T := T) (TD := TD)
    (modularJ_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat)

end Algebra

/--
Minimal defect-sector package used by downstream KK/Fredholm bridges.
This file only defines the object; finiteness/compactness assumptions are added
later.
-/
@[rep_depth operator]
structure DefectSectorData
    (T TD : DoubledSpace E →L[ℝ] DoubledSpace E) (k : ℕ) where
  compat : KreinGradedDrazinCompatibility (E := E) T TD k
  nontrivial_defect : Pzero T TD ≠ 0

end InfoGeometry.Canonical.DrazinKreinCompatibility

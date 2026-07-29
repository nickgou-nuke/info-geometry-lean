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
open DrazinInfiniteCore
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
Cartan/modular compatibility surface for an operator on the doubled carrier.

This is intentionally a commutation-only interface. It does not identify the
spectral Drazin split with any geometric sector by definition.
-/
@[rep_depth operator]
abbrev IsCartanCompatible (η T : Op) : Prop :=
  η.comp T = T.comp η ∧
    (spectral_epsilon (E := E)).comp T = T.comp (spectral_epsilon (E := E)) ∧
    (modular_j (E := E)).comp T = T.comp (modular_j (E := E))

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

section CartanTransport

/-- The source operator is Cartan-compatible under a graded Drazin package. -/
@[rep_depth operator]
def isCartanCompatible_T_of_compat
    (T TD : Op) (k : ℕ)
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    IsCartanCompatible (E := E) hCompat.η T :=
  ⟨hCompat.η_comm_T, hCompat.ε_comm_T, hCompat.J_comm_T⟩

/-- The Drazin witness operator is Cartan-compatible under a graded package. -/
@[rep_depth operator]
def isCartanCompatible_TD_of_compat
    (T TD : Op) (k : ℕ)
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    IsCartanCompatible (E := E) hCompat.η TD :=
  ⟨hCompat.η_comm_TD, hCompat.ε_comm_TD, hCompat.J_comm_TD⟩

end CartanTransport

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

-- Decomposition identity `P + P₀ = 1`.
omit [CompleteSpace E] in
@[rep_depth operator]
theorem Preg_add_Pzero :
    Preg T TD + Pzero T TD = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  change IsDrazinInverse.projection T TD + IsDrazinInverse.complementaryProjection T TD
      = (1 : DoubledSpace E →L[ℝ] DoubledSpace E)
  exact IsDrazinInverse.projection_add_complementaryProjection (a := T) (b := TD)

/--
Regular-lane projector compression of an operator candidate.

This is the projector-controlled support restriction used before any logarithmic
generator readout lane.
-/
@[rep_depth operator]
noncomputable def regularCompression
    (T TD K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  Preg T TD * K * Preg T TD

/--
Left support law on the regular Drazin lane:
`P_reg * K_reg = K_reg`.
-/
@[rep_depth operator]
theorem Preg_mul_regularCompression
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k)
    (K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    Preg T TD * regularCompression (E := E) T TD K
      = regularCompression (E := E) T TD K := by
  unfold regularCompression
  calc
    Preg T TD * (Preg T TD * K * Preg T TD)
        = (Preg T TD * Preg T TD) * K * Preg T TD := by
            simp [mul_assoc]
    _ = Preg T TD * K * Preg T TD := by
          simp [Preg_idempotent (E := E) (T := T) (TD := TD) (k := k) hCompat, mul_assoc]

/--
Right support law on the regular Drazin lane:
`K_reg * P_reg = K_reg`.
-/
@[rep_depth operator]
theorem regularCompression_mul_Preg
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k)
    (K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    regularCompression (E := E) T TD K * Preg T TD
      = regularCompression (E := E) T TD K := by
  unfold regularCompression
  calc
    (Preg T TD * K * Preg T TD) * Preg T TD
        = Preg T TD * K * (Preg T TD * Preg T TD) := by
            simp [mul_assoc]
    _ = Preg T TD * K * Preg T TD := by
          simp [Preg_idempotent (E := E) (T := T) (TD := TD) (k := k) hCompat, mul_assoc]

/--
Left defect annihilation of the regular-lane compression:
`P₀ * K_reg = 0`.
-/
@[rep_depth operator]
theorem Pzero_mul_regularCompression_eq_zero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k)
    (K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    Pzero T TD * regularCompression (E := E) T TD K = 0 := by
  unfold regularCompression
  calc
    Pzero T TD * (Preg T TD * K * Preg T TD)
        = (Pzero T TD * Preg T TD) * K * Preg T TD := by
            simp [mul_assoc]
    _ = 0 := by
          simp [Pzero_mul_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat]

/--
Right defect annihilation of the regular-lane compression:
`K_reg * P₀ = 0`.
-/
@[rep_depth operator]
theorem regularCompression_mul_Pzero_eq_zero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k)
    (K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    regularCompression (E := E) T TD K * Pzero T TD = 0 := by
  unfold regularCompression
  calc
    (Preg T TD * K * Preg T TD) * Pzero T TD
        = Preg T TD * K * (Preg T TD * Pzero T TD) := by
            simp [mul_assoc]
    _ = 0 := by
          simp [Preg_mul_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat]

/--
Support package for regular-lane compression:
left/right support invariance and left/right defect annihilation.
-/
@[rep_depth operator]
theorem regularCompression_support_package
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k)
    (K : DoubledSpace E →L[ℝ] DoubledSpace E) :
    Preg T TD * regularCompression (E := E) T TD K
        = regularCompression (E := E) T TD K
      ∧ regularCompression (E := E) T TD K * Preg T TD
        = regularCompression (E := E) T TD K
      ∧ Pzero T TD * regularCompression (E := E) T TD K = 0
      ∧ regularCompression (E := E) T TD K * Pzero T TD = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Preg_mul_regularCompression (E := E) (T := T) (TD := TD) (k := k) hCompat K
  · exact regularCompression_mul_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat K
  · exact Pzero_mul_regularCompression_eq_zero (E := E) (T := T) (TD := TD) (k := k) hCompat K
  · exact regularCompression_mul_Pzero_eq_zero (E := E) (T := T) (TD := TD) (k := k) hCompat K

/-- Canonical chiral decomposition `P₊ + P₋ = 1`. -/
@[rep_depth operator]
theorem Pplus_add_Pminus :
    chiralPlus (E := E) + chiralMinus (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  unfold chiralPlus chiralMinus
  exact krein_projector_completeness (E := E)

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
private theorem commutes_with_comp
    {A B P : Op}
    (hA : A.comp P = P.comp A)
    (hB : B.comp P = P.comp B) :
    (A.comp B).comp P = P.comp (A.comp B) := by
  calc
    (A.comp B).comp P = A.comp (B.comp P) := by
      rfl
    _ = A.comp (P.comp B) := by
      rw [hB]
    _ = (A.comp P).comp B := by
      rfl
    _ = (P.comp A).comp B := by
      rw [hA]
    _ = P.comp (A.comp B) := by
      rfl

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

/--
The internal doubled-Krein phase axis `J ∘ ε` preserves the regular Drazin
sector whenever the Drazin package is compatible with both real operators.
-/
@[rep_depth operator]
theorem doubledKreinPhaseAxis_comm_Preg_of_drazinKreinCompatibility
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    ((modular_j (E := E)).comp (spectral_epsilon (E := E))).comp (Preg T TD)
      =
    (Preg T TD).comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  exact
    commutes_with_comp
      (A := modular_j (E := E))
      (B := spectral_epsilon (E := E))
      (P := Preg T TD)
      (modularJ_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat)
      (epsilon_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
The internal doubled-Krein phase axis `J ∘ ε` preserves the Drazin defect
sector whenever the Drazin package is compatible with both real operators.
-/
@[rep_depth operator]
theorem doubledKreinPhaseAxis_comm_Pzero_of_drazinKreinCompatibility
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    ((modular_j (E := E)).comp (spectral_epsilon (E := E))).comp (Pzero T TD)
      =
    (Pzero T TD).comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  exact
    commutes_with_comp
      (A := modular_j (E := E))
      (B := spectral_epsilon (E := E))
      (P := Pzero T TD)
      (modularJ_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat)
      (epsilon_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
The Drazin core split is invariant under the internal doubled-Krein phase axis
`J ∘ ε`.
-/
@[rep_depth operator]
theorem doubledKreinPhaseAxis_preserves_drazinCore_split
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    ((modular_j (E := E)).comp (spectral_epsilon (E := E))).comp (Preg T TD)
        = (Preg T TD).comp ((modular_j (E := E)).comp (spectral_epsilon (E := E)))
      ∧
    ((modular_j (E := E)).comp (spectral_epsilon (E := E))).comp (Pzero T TD)
        = (Pzero T TD).comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  exact
    ⟨doubledKreinPhaseAxis_comm_Preg_of_drazinKreinCompatibility
        (E := E) (T := T) (TD := TD) (k := k) hCompat,
      doubledKreinPhaseAxis_comm_Pzero_of_drazinKreinCompatibility
        (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

/--
Owner-name view of `doubledKreinPhaseAxis_comm_Preg_of_drazinKreinCompatibility`.
Here `complex_i` is the repo's real-linear doubled-Krein phase-axis name, not
an external scalar complex structure.
-/
@[rep_depth operator]
theorem complex_i_comm_Preg_of_drazinKreinCompatibility
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (complex_i (E := E)).comp (Preg T TD)
      = (Preg T TD).comp (complex_i (E := E)) := by
  simpa [complex_i] using
    (doubledKreinPhaseAxis_comm_Preg_of_drazinKreinCompatibility
      (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
Owner-name view of `doubledKreinPhaseAxis_comm_Pzero_of_drazinKreinCompatibility`.
Here `complex_i` is the repo's real-linear doubled-Krein phase-axis name, not
an external scalar complex structure.
-/
@[rep_depth operator]
theorem complex_i_comm_Pzero_of_drazinKreinCompatibility
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (complex_i (E := E)).comp (Pzero T TD)
      = (Pzero T TD).comp (complex_i (E := E)) := by
  simpa [complex_i] using
    (doubledKreinPhaseAxis_comm_Pzero_of_drazinKreinCompatibility
      (E := E) (T := T) (TD := TD) (k := k) hCompat)

/--
Owner-name view of `doubledKreinPhaseAxis_preserves_drazinCore_split`.
The statement remains entirely over real doubled-Krein operators.
-/
@[rep_depth operator]
theorem complex_i_preserves_drazinCore_split
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (complex_i (E := E)).comp (Preg T TD)
        = (Preg T TD).comp (complex_i (E := E))
      ∧
    (complex_i (E := E)).comp (Pzero T TD)
        = (Pzero T TD).comp (complex_i (E := E)) := by
  exact
    ⟨complex_i_comm_Preg_of_drazinKreinCompatibility
        (E := E) (T := T) (TD := TD) (k := k) hCompat,
      complex_i_comm_Pzero_of_drazinKreinCompatibility
        (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

/-- The regular Drazin projector inherits Cartan compatibility. -/
@[rep_depth operator]
theorem isCartanCompatible_Preg
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    IsCartanCompatible (E := E) hCompat.η (Preg T TD) := by
  exact ⟨eta_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat,
    epsilon_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat,
    modularJ_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

/-- The defect Drazin projector inherits Cartan compatibility. -/
@[rep_depth operator]
theorem isCartanCompatible_Pzero
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    IsCartanCompatible (E := E) hCompat.η (Pzero T TD) := by
  exact ⟨eta_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat,
    epsilon_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat,
    modularJ_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

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

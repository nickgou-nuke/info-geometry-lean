import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Meta.Architecture

/-!
# Bilingual real Hestenes dictionary

Certified readback from complex-language words into the repo-native real doubled
Hestenes/Krein lane.  This file does not introduce a complex Hilbert owner
surface and does not claim full Tomita-Takesaki standard form.
-/

namespace InfoGeometry.Canonical.BilingualRealHestenesDictionary

open scoped InnerProductSpace
open InfoGeometry.Krein
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.DrazinKreinCompatibility

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

omit [CompleteSpace E] in
/-- Complex scalar `i` is read as the real doubled phase axis `K = J ∘ ε`. -/
@[rep_depth krein]
theorem realPhaseAxis_eq_complex_i :
    InfoGeometry.Krein.clockAxis (E := E) = InfoGeometry.Krein.complex_i (E := E) :=
  InfoGeometry.Krein.clockAxis_eq_complex_i (E := E)

/-- The Tomita-named modular complex axis is the repo-native phase axis. -/
@[rep_depth krein]
theorem modularComplexI_eq_realPhaseAxis :
    modularComplexI (E := E) = InfoGeometry.Krein.clockAxis (E := E) :=
  modularComplexI_eq_clockAxis (E := E)

/-- The Tomita-named modular complex axis reads back to real doubled `complex_i`. -/
@[rep_depth krein]
theorem modularComplexI_readback_complex_i :
    modularComplexI (E := E) = InfoGeometry.Krein.complex_i (E := E) :=
  modularComplexI_eq_complex_i (E := E)

/-- The real phase axis squares to `-1`. -/
@[rep_depth krein]
theorem realPhaseAxis_sq :
    (InfoGeometry.Krein.clockAxis (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂) :=
  InfoGeometry.Krein.clockAxis_sq (E := E)

/-- The modular swap and sign involution are the real doubled `Cl(1,1)` generators. -/
@[rep_depth krein]
theorem realDoubled_cl11_relations :
    cl11_relations (InfoGeometry.Krein.modular_j (E := E))
      (InfoGeometry.Krein.spectral_epsilon (E := E)) :=
  InfoGeometry.Krein.modular_j_spectral_epsilon_has_cl11_relations E

/-- Real doubled `J` anticommutes with `ε`. -/
@[rep_depth krein]
theorem realDoubled_J_ε_anticommute :
    (InfoGeometry.Krein.modular_j (E := E)).comp
        (InfoGeometry.Krein.spectral_epsilon (E := E)) =
      -((InfoGeometry.Krein.spectral_epsilon (E := E)).comp
        (InfoGeometry.Krein.modular_j (E := E))) :=
  InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute E

omit [CompleteSpace E] in
/-- Complex-linearity readback: real operators commute with the internal phase axis. -/
@[rep_depth krein]
theorem complexLinear_readback (A : EndH) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        (E := E) A (InfoGeometry.Krein.clockAxis (E := E)) = 0 ↔
      KLinear (E := E) A :=
  kLinear_iff_phaseAxisCommutator_eq_zero (E := E) A

omit [CompleteSpace E] in
/-- Complex-antilinearity readback: real operators anticommute with the phase axis. -/
@[rep_depth krein]
theorem complexAntilinear_readback (A : EndH) :
    InfoGeometry.Canonical.HestenesRealStructures.transportAnticommutator
        (E := E) A (InfoGeometry.Krein.clockAxis (E := E)) = 0 ↔
      KAntilinear (E := E) A :=
  kAntilinear_iff_phaseAxisAnticommutator_eq_zero (E := E) A

omit [CompleteSpace E] in
/-- The phase axis is itself `K`-linear. -/
@[rep_depth krein]
theorem realPhaseAxis_isKLinear :
    KLinear (E := E) (InfoGeometry.Krein.clockAxis (E := E)) :=
  phaseAxisK_isKLinear (E := E)

/-- The phase axis is Krein anti-isometric. -/
@[rep_depth krein]
theorem realPhaseAxis_isKreinAntiIsometric :
    KreinAntiIsometric (E := E) (InfoGeometry.Krein.clockAxis (E := E)) :=
  phaseAxisK_isKreinAntiIsometric (E := E)

/-- Positive Hilbert metric readback: the phase axis is skew for one input. -/
@[rep_depth krein]
theorem realPhaseAxis_inner_skew (u v : H₂) :
    ⟪InfoGeometry.Krein.clockAxis (E := E) u, v⟫_ℝ =
      -⟪u, InfoGeometry.Krein.clockAxis (E := E) v⟫_ℝ :=
  clockAxis_inner_skew (E := E) u v

/-- Positive Hilbert metric readback: the phase axis preserves the inner product. -/
@[rep_depth krein]
theorem realPhaseAxis_inner_comp (u v : H₂) :
    ⟪InfoGeometry.Krein.clockAxis (E := E) u,
      InfoGeometry.Krein.clockAxis (E := E) v⟫_ℝ = ⟪u, v⟫_ℝ :=
  clockAxis_inner_comp (E := E) u v

/-- Krein metric readback: applying the phase axis to both inputs flips sign. -/
@[rep_depth krein]
theorem realPhaseAxis_kreinInner_comp (u v : H₂) :
    KreinSpace.kreinInner (H := H₂)
        ((InfoGeometry.Krein.clockAxis (E := E)) u)
        ((InfoGeometry.Krein.clockAxis (E := E)) v) =
      -KreinSpace.kreinInner (H := H₂) u v :=
  clockAxis_kreinInner_comp (E := E) u v

/-- Hestenes pseudoscalar readback: the `Cl(1,1)` pseudoscalar represents `ε`. -/
@[rep_depth krein]
theorem hestenesPseudoscalar_readback_spectralEpsilon :
    _root_.cl11Rep (E := E) Pseudoscalar = InfoGeometry.Krein.spectral_epsilon (E := E) :=
  cl11Rep_pseudoscalar_eq_spectral_epsilon (E := E)

/-- The represented Hestenes pseudoscalar squares to identity. -/
@[rep_depth krein]
theorem hestenesPseudoscalar_readback_sq :
    (_root_.cl11Rep (E := E) Pseudoscalar).comp (_root_.cl11Rep (E := E) Pseudoscalar) =
      ContinuousLinearMap.id ℝ H₂ :=
  cl11Rep_pseudoscalar_comp_self (E := E)

/-- Drazin regular/defect projectors preserve the internal phase axis under compatibility. -/
@[rep_depth krein]
theorem drazinCore_phaseAxis_preserved
    {T TD : EndH} {k : ℕ}
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    (InfoGeometry.Krein.complex_i (E := E)).comp (Preg T TD) =
        (Preg T TD).comp (InfoGeometry.Krein.complex_i (E := E))
      ∧
    (InfoGeometry.Krein.complex_i (E := E)).comp (Pzero T TD) =
        (Pzero T TD).comp (InfoGeometry.Krein.complex_i (E := E)) :=
  complex_i_preserves_drazinCore_split (E := E) hCompat

end InfoGeometry.Canonical.BilingualRealHestenesDictionary

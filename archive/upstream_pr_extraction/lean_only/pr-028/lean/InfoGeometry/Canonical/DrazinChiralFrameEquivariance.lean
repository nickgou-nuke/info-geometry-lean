import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinChiralFrameEquivariance

Drazin/chiral sector invariance for the real doubled Hestenes carrier.

This file deliberately avoids eigenvector-basis authority. The invariant data are
projectors, preserved sectors, and bilinear/graded compatibility laws.

Bogoliubov frames are admissible only up to symmetries preserving the Drazin
regular/defect split and the `Cl(1,1)` chiral split.
-/

namespace InfoGeometry.Canonical.DrazinChiralFrameEquivariance

open InfoGeometry.Krein
open InfoGeometry.Canonical.DrazinKreinCompatibility
open InfoGeometry.Canonical.HestenesRealStructures

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
An operator preserves the Drazin regular/defect split when it commutes with both
`P_reg` and `P₀`.

This is the sector invariant. It is not an eigenbasis statement.
-/
@[rep_depth operator]
def PreservesDrazinSplit (T TD U : EndH) : Prop :=
  U.comp (Preg T TD) = (Preg T TD).comp U ∧
  U.comp (Pzero T TD) = (Pzero T TD).comp U

/--
An operator preserves the fixed `ε`-chiral split when it commutes with the
fundamental grading.
-/
@[rep_depth krein]
def PreservesChiralSplit (U : EndH) : Prop :=
  U.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp U

/--
A real doubled gauge symmetry for the Drazin/chiral sector calculus.
-/
@[rep_depth operator]
def IsDrazinChiralGauge (T TD U : EndH) : Prop :=
  PreservesDrazinSplit (E := E) T TD U ∧ PreservesChiralSplit (E := E) U

/-- Under compatibility, `ε` preserves the Drazin split. -/
@[rep_depth operator]
theorem epsilon_preservesDrazinSplit
    {T TD : EndH} {k : ℕ}
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    PreservesDrazinSplit (E := E) T TD (spectral_epsilon (E := E)) := by
  exact
    ⟨epsilon_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat,
      epsilon_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

/-- Under compatibility, `J` preserves the Drazin split. -/
@[rep_depth operator]
theorem modularJ_preservesDrazinSplit
    {T TD : EndH} {k : ℕ}
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    PreservesDrazinSplit (E := E) T TD (modular_j (E := E)) := by
  exact
    ⟨modularJ_comm_Preg (E := E) (T := T) (TD := TD) (k := k) hCompat,
      modularJ_comm_Pzero (E := E) (T := T) (TD := TD) (k := k) hCompat⟩

/-- Under compatibility, `K = J ∘ ε` preserves the Drazin split. -/
@[rep_depth operator]
theorem phaseAxis_preservesDrazinSplit
    {T TD : EndH} {k : ℕ}
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    PreservesDrazinSplit (E := E) T TD
      ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  exact
    doubledKreinPhaseAxis_preserves_drazinCore_split
      (E := E) (T := T) (TD := TD) (k := k) hCompat

/--
`ε` is a Drazin/chiral gauge symmetry under compatibility.
The chiral part is tautological (`ε` commutes with itself).
-/
@[rep_depth operator]
theorem epsilon_isDrazinChiralGauge
    {T TD : EndH} {k : ℕ}
    (hCompat : KreinGradedDrazinCompatibility (E := E) T TD k) :
    IsDrazinChiralGauge (E := E) T TD (spectral_epsilon (E := E)) := by
  constructor
  · exact epsilon_preservesDrazinSplit (E := E) hCompat
  · unfold PreservesChiralSplit
    rfl

/-- Pointwise membership in the Drazin regular sector. -/
@[rep_depth operator]
def IsInRegularSector (T TD : EndH) (x : H₂) : Prop :=
  ∃ y : H₂, Preg T TD y = x

/-- Pointwise membership in the Drazin defect/null sector. -/
@[rep_depth operator]
def IsInNullSector (T TD : EndH) (x : H₂) : Prop :=
  ∃ y : H₂, Pzero T TD y = x

/--
Bogoliubov frame equivalence as a gauge-orbit datum preserving Drazin/chiral
invariants in both directions.
-/
@[rep_depth operator]
structure BogoliubovFrameEquiv (T TD : EndH) where
  U : EndH
  Uinv : EndH
  left_inv : Uinv.comp U = ContinuousLinearMap.id ℝ H₂
  right_inv : U.comp Uinv = ContinuousLinearMap.id ℝ H₂
  preserves : IsDrazinChiralGauge (E := E) T TD U
  preserves_inv : IsDrazinChiralGauge (E := E) T TD Uinv

namespace BogoliubovFrameEquiv

/-- Transport by `U` preserves membership in the regular Drazin sector. -/
@[rep_depth operator]
theorem maps_regular_sector
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD)
    {x : H₂} :
    IsInRegularSector (E := E) T TD x →
      IsInRegularSector (E := E) T TD (F.U x) := by
  intro hx
  rcases hx with ⟨y, hy⟩
  refine ⟨F.U y, ?_⟩
  have hPreg := F.preserves.1.1
  have hApply : F.U (Preg T TD y) = Preg T TD (F.U y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun G : EndH => G y) hPreg
  calc
    Preg T TD (F.U y) = F.U (Preg T TD y) := hApply.symm
    _ = F.U x := by simp [hy]

/-- Transport by `U` preserves membership in the null/defect Drazin sector. -/
@[rep_depth operator]
theorem maps_null_sector
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD)
    {x : H₂} :
    IsInNullSector (E := E) T TD x →
      IsInNullSector (E := E) T TD (F.U x) := by
  intro hx
  rcases hx with ⟨y, hy⟩
  refine ⟨F.U y, ?_⟩
  have hPzero := F.preserves.1.2
  have hApply : F.U (Pzero T TD y) = Pzero T TD (F.U y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun G : EndH => G y) hPzero
  calc
    Pzero T TD (F.U y) = F.U (Pzero T TD y) := hApply.symm
    _ = F.U x := by simp [hy]

/-- Inverse transport preserves regular-sector membership. -/
@[rep_depth operator]
theorem inverse_maps_regular_sector
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD)
    {x : H₂} :
    IsInRegularSector (E := E) T TD x →
      IsInRegularSector (E := E) T TD (F.Uinv x) := by
  intro hx
  rcases hx with ⟨y, hy⟩
  refine ⟨F.Uinv y, ?_⟩
  have hPreg := F.preserves_inv.1.1
  have hApply : F.Uinv (Preg T TD y) = Preg T TD (F.Uinv y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun G : EndH => G y) hPreg
  calc
    Preg T TD (F.Uinv y) = F.Uinv (Preg T TD y) := hApply.symm
    _ = F.Uinv x := by simp [hy]

/-- Inverse transport preserves null/defect-sector membership. -/
@[rep_depth operator]
theorem inverse_maps_null_sector
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD)
    {x : H₂} :
    IsInNullSector (E := E) T TD x →
      IsInNullSector (E := E) T TD (F.Uinv x) := by
  intro hx
  rcases hx with ⟨y, hy⟩
  refine ⟨F.Uinv y, ?_⟩
  have hPzero := F.preserves_inv.1.2
  have hApply : F.Uinv (Pzero T TD y) = Pzero T TD (F.Uinv y) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun G : EndH => G y) hPzero
  calc
    Pzero T TD (F.Uinv y) = F.Uinv (Pzero T TD y) := hApply.symm
    _ = F.Uinv x := by simp [hy]

/-- Transport by `U` preserves the fixed chiral commutation law. -/
@[rep_depth krein]
theorem preserves_chiral
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD) :
    F.U.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp F.U :=
  F.preserves.2

/-- Inverse transport preserves the fixed chiral commutation law. -/
@[rep_depth krein]
theorem inverse_preserves_chiral
    {T TD : EndH}
    (F : BogoliubovFrameEquiv (E := E) T TD) :
    F.Uinv.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp F.Uinv :=
  F.preserves_inv.2

end BogoliubovFrameEquiv

/--
Infinitesimal Noether-style generator compatible with the Drazin/chiral gauge lane.
-/
@[rep_depth operator]
def IsDrazinChiralNoetherGenerator (T TD A : EndH) : Prop :=
  InfoGeometry.Krein.is_krein_skew_adjoint (E := E) A ∧
    PreservesDrazinSplit (E := E) T TD A ∧
    PreservesChiralSplit (E := E) A

/--
A Drazin/chiral Noether generator is infinitesimally Hessian-preserving.
-/
@[rep_depth krein]
theorem drazinChiralNoetherGenerator_hessian_infinitesimal
    {T TD A : EndH}
    (hA : IsDrazinChiralNoetherGenerator (E := E) T TD A)
    (x y : H₂) :
    InfoGeometry.Krein.hessian_indefinite_form (E := E) (A x) y +
      InfoGeometry.Krein.hessian_indefinite_form (E := E) x (A y) = 0 :=
  InfoGeometry.Krein.is_krein_skew_adjoint_hessian_infinitesimal
    (E := E) (A := A) hA.1 x y

/--
A Drazin/chiral Noether generator lies in the ambient information Lie algebra.
-/
@[rep_depth operator]
theorem drazinChiralNoetherGenerator_mem_information_lie_algebra
    {T TD A : EndH}
    (hA : IsDrazinChiralNoetherGenerator (E := E) T TD A) :
    A ∈ InfoGeometry.Krein.information_lie_algebra (E := E) :=
  hA.1

end Core

end InfoGeometry.Canonical.DrazinChiralFrameEquivariance

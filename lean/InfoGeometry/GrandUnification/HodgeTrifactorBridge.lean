import Mathlib
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Hodge-Trifactor Bridge

This module gives finite theorem ownership to the Hodge-style language attached
to the tripotent decomposition `T ^ 3 = T`.

It is a naming bridge only in the safe algebraic sense:

* harmonic sector  := `P_zero`;
* exact sector     := `P_plus`;
* coexact sector   := `P_minus`.

No analytic Hodge theorem, spectral-triple theorem, KMS statement, CFT claim, or
Riemann-hypothesis claim is asserted here.

#### BUCKET 1: CLOSED FINITE THEOREMS
`hodge_trifactor_decomposition`, `T_annihilates_harmonicSector`,
`T_on_exactSector`, `T_on_coexactSector`, and
`harmonicSector_eq_self_of_active_sectors_vanish`.  The sector functoriality
lemmas prove that linear maps preserve the three scalar tripotent sectors.
The sector-dictionary lemmas prove the finite type-level correspondence between
the Hodge labels and the tripotent labels.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The spectral-action theorems require the explicit tripotence premise
`T ^ 3 = T`.  The harmonic-collapse theorem requires the explicit active-sector
vanishing premise.

#### BUCKET 3: OPEN CLOSURE DEBT
Any identification with analytic Hodge decomposition, zeta zeros, Dirac-Hodge
operators, KMS thermodynamics, CFT, or Riemann-hypothesis statements.
-/

namespace HodgeTrifactorBridge

open TrifactorDecomposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {H : Type*} [AddCommGroup H] [Module R H]
variable {H₂ : Type*} [AddCommGroup H₂] [Module R H₂]

/-! ## Finite Hodge-to-trifactor sector dictionary -/

/-- The three formal Hodge labels used in the finite dictionary. -/
inductive HodgeSector
  | exact
  | coexact
  | harmonic
  deriving DecidableEq, Repr

/-- The three tripotent labels for the `+1`, `-1`, and `0` sectors. -/
inductive TrifactorSector
  | plus
  | minus
  | zero
  deriving DecidableEq, Repr

/-- Dictionary from Hodge labels to tripotent labels. -/
def hodgeToTrifactor : HodgeSector → TrifactorSector
  | HodgeSector.exact => TrifactorSector.plus
  | HodgeSector.coexact => TrifactorSector.minus
  | HodgeSector.harmonic => TrifactorSector.zero

/-- Inverse dictionary from tripotent labels to Hodge labels. -/
def trifactorToHodge : TrifactorSector → HodgeSector
  | TrifactorSector.plus => HodgeSector.exact
  | TrifactorSector.minus => HodgeSector.coexact
  | TrifactorSector.zero => HodgeSector.harmonic

theorem trifactorToHodge_hodgeToTrifactor (s : HodgeSector) :
    trifactorToHodge (hodgeToTrifactor s) = s := by
  cases s <;> rfl

theorem hodgeToTrifactor_trifactorToHodge (s : TrifactorSector) :
    hodgeToTrifactor (trifactorToHodge s) = s := by
  cases s <;> rfl

/-- The finite sector dictionary as an explicit equivalence of labels. -/
def hodgeTrifactorEquiv : HodgeSector ≃ TrifactorSector where
  toFun := hodgeToTrifactor
  invFun := trifactorToHodge
  left_inv := trifactorToHodge_hodgeToTrifactor
  right_inv := hodgeToTrifactor_trifactorToHodge

/-- Projector attached to a tripotent sector label. -/
def trifactorSectorProjector (T : R) : TrifactorSector → R
  | TrifactorSector.plus => P_plus T
  | TrifactorSector.minus => P_minus T
  | TrifactorSector.zero => P_zero T

/-- Projector attached to a formal Hodge sector through the finite dictionary. -/
def hodgeSectorProjector (T : R) (s : HodgeSector) : R :=
  trifactorSectorProjector T (hodgeToTrifactor s)

theorem hodgeSectorProjector_exact (T : R) :
    hodgeSectorProjector T HodgeSector.exact = P_plus T := rfl

theorem hodgeSectorProjector_coexact (T : R) :
    hodgeSectorProjector T HodgeSector.coexact = P_minus T := rfl

theorem hodgeSectorProjector_harmonic (T : R) :
    hodgeSectorProjector T HodgeSector.harmonic = P_zero T := rfl

/-- State component attached to a formal Hodge sector. -/
def hodgeSectorComponent (T : R) (s : HodgeSector) (ρ : H) : H :=
  hodgeSectorProjector T s • ρ

/-- Hodge-style harmonic sector: the `0` sector of the tripotent projector. -/
def harmonicSector (T : R) (ρ : H) : H :=
  P_zero T • ρ

/-- Hodge-style exact/holomorphic sector: the `+1` tripotent sector. -/
def exactSector (T : R) (ρ : H) : H :=
  P_plus T • ρ

/-- Hodge-style coexact/antiholomorphic sector: the `-1` tripotent sector. -/
def coexactSector (T : R) (ρ : H) : H :=
  P_minus T • ρ

theorem hodgeSectorComponent_exact (T : R) (ρ : H) :
    hodgeSectorComponent T HodgeSector.exact ρ = exactSector T ρ := rfl

theorem hodgeSectorComponent_coexact (T : R) (ρ : H) :
    hodgeSectorComponent T HodgeSector.coexact ρ = coexactSector T ρ := rfl

theorem hodgeSectorComponent_harmonic (T : R) (ρ : H) :
    hodgeSectorComponent T HodgeSector.harmonic ρ = harmonicSector T ρ := rfl

/-- Every state decomposes into harmonic, exact, and coexact tripotent sectors. -/
theorem hodge_trifactor_decomposition (T : R) (ρ : H) :
    harmonicSector T ρ + exactSector T ρ + coexactSector T ρ = ρ := by
  calc
    harmonicSector T ρ + exactSector T ρ + coexactSector T ρ
        = (P_zero T + P_plus T + P_minus T) • ρ := by
            simp [harmonicSector, exactSector, coexactSector, add_smul]
    _ = ρ := by
            rw [partition_of_unity T, one_smul]

omit [Invertible (2 : R)] in
/-- The tripotent operator annihilates the harmonic sector. -/
theorem T_annihilates_harmonicSector (T : R) (hT : T ^ 3 = T) (ρ : H) :
    T • harmonicSector T ρ = 0 := by
  simp [harmonicSector, smul_smul, T_on_P_zero T hT]

/-- The tripotent operator acts by `+1` on the exact sector. -/
theorem T_on_exactSector (T : R) (hT : T ^ 3 = T) (ρ : H) :
    T • exactSector T ρ = exactSector T ρ := by
  simp [exactSector, smul_smul, T_on_P_plus T hT]

/-- The tripotent operator acts by `-1` on the coexact sector. -/
theorem T_on_coexactSector (T : R) (hT : T ^ 3 = T) (ρ : H) :
    T • coexactSector T ρ = -coexactSector T ρ := by
  simp [coexactSector, smul_smul, T_on_P_minus T hT]

/--
If the active exact/coexact sectors cancel on a state, the state is equal to its
harmonic sector.  This is the finite projector-collapse statement behind the
Hodge/trifactor analogy.
-/
theorem harmonicSector_eq_self_of_active_sectors_vanish
    (T : R) (ρ : H)
    (hactive : exactSector T ρ + coexactSector T ρ = 0) :
    harmonicSector T ρ = ρ := by
  have hdec := hodge_trifactor_decomposition (T := T) (ρ := ρ)
  have hgroup :
      harmonicSector T ρ + exactSector T ρ + coexactSector T ρ =
        harmonicSector T ρ + (exactSector T ρ + coexactSector T ρ) := by
    abel
  rw [hgroup, hactive, add_zero] at hdec
  exact hdec

/-! ## Functoriality under linear maps -/

omit [Invertible (2 : R)] in
/-- Linear maps preserve the harmonic sector. -/
theorem linearMap_map_harmonicSector
    (T : R) (F : H →ₗ[R] H₂) (ρ : H) :
    F (harmonicSector T ρ) = harmonicSector T (F ρ) := by
  simp [harmonicSector]

/-- Linear maps preserve the exact sector. -/
theorem linearMap_map_exactSector
    (T : R) (F : H →ₗ[R] H₂) (ρ : H) :
    F (exactSector T ρ) = exactSector T (F ρ) := by
  simp [exactSector]

/-- Linear maps preserve the coexact sector. -/
theorem linearMap_map_coexactSector
    (T : R) (F : H →ₗ[R] H₂) (ρ : H) :
    F (coexactSector T ρ) = coexactSector T (F ρ) := by
  simp [coexactSector]

/-- Linear maps preserve the three-sector decomposition. -/
theorem linearMap_map_hodge_trifactor_decomposition
    (T : R) (F : H →ₗ[R] H₂) (ρ : H) :
    harmonicSector T (F ρ) + exactSector T (F ρ) + coexactSector T (F ρ) =
      F ρ := by
  exact hodge_trifactor_decomposition (T := T) (ρ := F ρ)

/--
If the active sectors vanish before applying a linear map, they vanish after
applying it.  This is the finite functorial shadow of the Hodge/trifactor
sector dictionary.
-/
theorem linearMap_preserves_active_sector_vanishing
    (T : R) (F : H →ₗ[R] H₂) (ρ : H)
    (hactive : exactSector T ρ + coexactSector T ρ = 0) :
    exactSector T (F ρ) + coexactSector T (F ρ) = 0 := by
  rw [← linearMap_map_exactSector (T := T) F ρ,
    ← linearMap_map_coexactSector (T := T) F ρ,
    ← F.map_add, hactive, F.map_zero]

end HodgeTrifactorBridge

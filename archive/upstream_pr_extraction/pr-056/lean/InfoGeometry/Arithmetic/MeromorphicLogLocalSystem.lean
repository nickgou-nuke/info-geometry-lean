import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannZetaDivisorLogGeometry
import InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
import InfoGeometry.Geometry.HelicalCovering

/-!
# Finite meromorphic logarithmic local system

This file instantiates the repository's generic helical-cover owner on a
punctured algebraic coordinate.  A point of the cover is a nonzero base
coordinate together with an integer sheet label.  The deck action preserves
the base and adds to the sheet label.

The logarithmic differential and its divisor charge remain owned by
`RiemannZetaDivisorLogGeometry` and `RiemannPoleZeroMonodromy`; this file only
connects them to the native finite sheet action.  No global logarithm,
analytic continuation, or contour integral is introduced.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MeromorphicLogLocalSystem

open InfoGeometry.Arithmetic.RiemannZetaDivisorLogGeometry
open InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Algebraic.EulerLaurentHestenesDivisor
open InfoGeometry.Clifford.HestenesWindingRotor
open InfoGeometry.Arithmetic.IndexTheorem
open InfoGeometry.Geometry.HelicalCovering
open Filter
open scoped Topology

/-! ## The punctured coordinate and its integer-sheet cover -/

abbrev PuncturedCoordinate (R : Type*) [Zero R] := {x : R // x ≠ 0}

abbrev LogSheet (R : Type*) [Zero R] := PuncturedCoordinate R × ℤ

def logSheetCovering (R : Type*) [Ring R] :
    HelicalCovering (PuncturedCoordinate R) (LogSheet R) where
  project := Prod.fst
  winding := Prod.snd
  branchLocus := ∅
  branch_requires_nonzero_winding := by simp

def logSheetDeckAction (R : Type*) [Ring R] :
    DeckAction (logSheetCovering R) where
  deck := fun n x => (x.1, x.2 + n)
  project_deck := by
    intro n x
    rfl
  winding_deck := by
    intro n x
    rfl
  deck_zero := by
    rintro ⟨x, k⟩
    simp
  deck_add := by
    rintro m n ⟨x, k⟩
    simp [add_assoc, add_left_comm, add_comm]

@[simp] theorem logSheetCovering_project_apply
    {R : Type*} [Ring R] (x : LogSheet R) :
    (logSheetCovering R).project x = x.1 :=
  rfl

@[simp] theorem logSheetCovering_winding_apply
    {R : Type*} [Ring R] (x : LogSheet R) :
    (logSheetCovering R).winding x = x.2 :=
  rfl

@[simp] theorem logSheetDeckAction_apply
    {R : Type*} [Ring R] (n : ℤ) (x : LogSheet R) :
    (logSheetDeckAction R).deck n x = (x.1, x.2 + n) :=
  rfl

theorem logSheetDeckAction_project
    {R : Type*} [Ring R] (n : ℤ) (x : LogSheet R) :
    (logSheetCovering R).project ((logSheetDeckAction R).deck n x) =
      (logSheetCovering R).project x := by
  exact (logSheetDeckAction R).project_deck n x

theorem logSheetDeckAction_winding
    {R : Type*} [Ring R] (n : ℤ) (x : LogSheet R) :
    (logSheetCovering R).winding ((logSheetDeckAction R).deck n x) =
      (logSheetCovering R).winding x + n := by
  exact (logSheetDeckAction R).winding_deck n x

theorem logSheetDeckAction_zeroSheet_iff
    {R : Type*} [Ring R] (n : ℤ) (x : LogSheet R) :
    (logSheetDeckAction R).deck n x ∈
        (logSheetCovering R).zeroSheet ↔ x.2 + n = 0 := by
  rfl

theorem logSheetDeckAction_nonzeroSheet
    {R : Type*} [Ring R] (n : ℤ) (x : LogSheet R)
    (_hx : x.2 ≠ 0) (hn : x.2 + n ≠ 0) :
    (logSheetDeckAction R).deck n x ∈
        (logSheetCovering R).nonzeroWindingSector := by
  exact hn

/-! ## The finite meromorphic charge readout -/

theorem logSystem_residue_eq_divisor_order
    {R : Type*} [Ring R] (F : LocalDivisorData R) :
    residue (chargeForm F) = F.order := by
  exact residue_dlog_equals_divisor_order F

theorem logSystem_normalForm_residue_eq_order
    {R : Type*} [CommRing R]
    (F : LocalLaurentNormalForm (R := R)) :
    residue (chargeForm (localDivisorDataOfNormalForm F)) = F.order := by
  exact residue_normalForm_charge F

theorem logSystem_finite_charge_winding
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (order : ι → ℤ) :
    winding r (finiteKernelIndex (divisorKernelComplex order)) =
      ∏ a : ι, winding r (order a) := by
  exact winding_of_divisor_kernel_index r order

theorem logSystem_zeta_pole_normalization :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (1 : ℂ)) := by
  exact riemannZeta_simplePole_normalization

/-! ## Finite puncture packets and homological winding -/

/-- A finite puncture configuration with signed zero/pole orders. -/
structure PuncturedBase (ι : Type*) [Fintype ι] [DecidableEq ι] where
  order : ι → ℤ

/-- The local divisor packet at one marked puncture. -/
def localDivisorOfPuncture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (i : ι) : LocalDivisorData ℤ :=
  { order := B.order i, unit := 0 }

@[simp] theorem localDivisorOfPuncture_order
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (i : ι) :
    (localDivisorOfPuncture B i).order = B.order i :=
  rfl

/-- The formal logarithmic one-form carried by a marked puncture. -/
def punctureConnection1Form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (i : ι) : LaurentOneForm ℤ :=
  chargeForm (localDivisorOfPuncture B i)

@[simp] theorem punctureConnection1Form_residue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (i : ι) :
    residue (punctureConnection1Form B i) = B.order i := by
  rw [punctureConnection1Form, residue_chargeForm]
  rfl

/-- Abelianized loop data, recorded by its integer winding at each puncture. -/
structure HomologyLoop (ι : Type*) [Fintype ι] [DecidableEq ι] where
  winding : ι → ℤ

instance (ι : Type*) [Fintype ι] [DecidableEq ι] : Add (HomologyLoop ι) where
  add γ₁ γ₂ := ⟨fun i => γ₁.winding i + γ₂.winding i⟩

instance (ι : Type*) [Fintype ι] [DecidableEq ι] : Zero (HomologyLoop ι) where
  zero := ⟨fun _ => 0⟩

@[simp] theorem homologyLoop_add_winding
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ₁ γ₂ : HomologyLoop ι) (i : ι) :
    (γ₁ + γ₂).winding i = γ₁.winding i + γ₂.winding i :=
  rfl

/-- The finite de Rham pairing of a loop with the signed divisor packet. -/
def deRhamPairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (γ : HomologyLoop ι) : ℤ :=
  ∑ i : ι, γ.winding i * B.order i

theorem deRhamPairing_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) (γ₁ γ₂ : HomologyLoop ι) :
    deRhamPairing B (γ₁ + γ₂) =
      deRhamPairing B γ₁ + deRhamPairing B γ₂ := by
  simp [deRhamPairing, add_mul, Finset.sum_add_distrib]

@[simp] theorem deRhamPairing_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : PuncturedBase ι) :
    deRhamPairing B 0 = 0 := by
  change (∑ i : ι, (0 : ℤ) * B.order i) = 0
  simp

/-- Integer-power rotor monodromy of a finite loop. -/
def monodromyRepresentation {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : PuncturedBase ι) (γ : HomologyLoop ι) : G :=
  winding r (deRhamPairing B γ)

theorem monodromy_is_homomorphism
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : PuncturedBase ι) (γ₁ γ₂ : HomologyLoop ι) :
    monodromyRepresentation r B (γ₁ + γ₂) =
      monodromyRepresentation r B γ₁ * monodromyRepresentation r B γ₂ := by
  change winding r (deRhamPairing B (γ₁ + γ₂)) =
    winding r (deRhamPairing B γ₁) * winding r (deRhamPairing B γ₂)
  rw [deRhamPairing_add, winding_add]

@[simp] theorem monodromy_contractible_is_one
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : PuncturedBase ι) :
    monodromyRepresentation r B 0 = 1 := by
  simp [monodromyRepresentation]

/-- The loop winding once around exactly one marked puncture. -/
def elementaryLoop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι) : HomologyLoop ι :=
  ⟨fun i => if i = k then 1 else 0⟩

theorem monodromy_elementary_loop
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : PuncturedBase ι) (k : ι) :
    monodromyRepresentation r B (elementaryLoop k) =
      winding r (B.order k) := by
  simp [monodromyRepresentation, deRhamPairing, elementaryLoop]

/-- The boundary loop winding once around every finite puncture. -/
def totalBoundaryLoop {ι : Type*} [Fintype ι] [DecidableEq ι] : HomologyLoop ι :=
  ⟨fun _ => 1⟩

theorem total_boundary_monodromy_eq_divisor_index
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : PuncturedBase ι) :
    monodromyRepresentation r B (totalBoundaryLoop (ι := ι)) =
      winding r (InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisorIndex
        B.order) := by
  change winding r (∑ i : ι, (1 : ℤ) * B.order i) =
    winding r (InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisorIndex
      B.order)
  simp [InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisorIndex]

/-- A puncture permutation preserving all signed local orders. -/
structure ReflectedPuncturedBase (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends PuncturedBase ι where
  reflect : ι ≃ ι
  reflect_involutive : ∀ i, reflect (reflect i) = i
  order_reflect : ∀ i, order (reflect i) = order i

/-- Transport loop windings along a permutation of punctures. -/
def reflectLoop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (γ : HomologyLoop ι) : HomologyLoop ι :=
  ⟨fun i => γ.winding (e.symm i)⟩

theorem deRhamPairing_reflection_invariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ReflectedPuncturedBase ι) (γ : HomologyLoop ι) :
    deRhamPairing B.toPuncturedBase (reflectLoop B.reflect γ) =
      deRhamPairing B.toPuncturedBase γ := by
  classical
  simp only [deRhamPairing, reflectLoop]
  rw [← B.reflect.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Equiv.symm_apply_apply]
  rw [B.order_reflect]

theorem monodromy_reflection_equivariant
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : G) (B : ReflectedPuncturedBase ι) (γ : HomologyLoop ι) :
    monodromyRepresentation r B.toPuncturedBase (reflectLoop B.reflect γ) =
      monodromyRepresentation r B.toPuncturedBase γ := by
  rw [monodromyRepresentation, monodromyRepresentation,
    deRhamPairing_reflection_invariant]

end InfoGeometry.Arithmetic.MeromorphicLogLocalSystem

end noncomputable section

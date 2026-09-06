/-
InfoGeometry/OperatorAlgebra/CrossoverResidue.lean

Chiral crossover residues and Hawking-point divisor audit.

This module formalizes only the constructive algebraic content:

* a Hawking-point residue is a weighted projective null ray;
* chirality is a finite orientation sign;
* a divisor is a finite list of such residues;
* crossover flips chirality and therefore flips chiral charge;
* a resolution audit supplies a smooth nonzero seed for each residue;
* chiral parity determines the sign of the resolved vorticity readout.

No claim is made that CCC Hawking points are physically observed.
No Navier-Stokes regularity theorem is asserted.
No ethical interpretation is encoded.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ConformalCrossover

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CrossoverResidue

open InfoGeometry.OperatorAlgebra.ConformalCrossover

/-! ## 1. Chiral orientation -/

/-- Two chiral orientations. This is the formal replacement for informal “handedness.” -/
inductive Chirality where
  | left
  | right
deriving DecidableEq, Repr

namespace Chirality

/-- Signed integer readout of chirality. -/
def sign : Chirality → ℤ
  | left => 1
  | right => -1

/-- Orientation reversal. -/
def flip : Chirality → Chirality
  | left => right
  | right => left

@[simp]
theorem sign_left :
    sign left = 1 :=
  rfl

@[simp]
theorem sign_right :
    sign right = -1 :=
  rfl

@[simp]
theorem flip_left :
    flip left = right :=
  rfl

@[simp]
theorem flip_right :
    flip right = left :=
  rfl

@[simp]
theorem flip_flip
    (χ : Chirality) :
    flip (flip χ) = χ := by
  cases χ <;> rfl

/-- Flipping chirality reverses the orientation sign. -/
@[simp]
theorem sign_flip
    (χ : Chirality) :
    sign (flip χ) = -sign χ := by
  cases χ <;> simp [sign, flip]

end Chirality

/-! ## 2. Hawking-point residue -/

/--
A Hawking-point residue in the algebraic crossover ledger.

The name is model-facing. The object itself is only finite algebraic data.
-/
structure HawkingPointResidue
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConformalCrossoverDatum V) where
  ray : ProjectiveNullRay C
  weight : ℤ
  chirality : Chirality

namespace HawkingPointResidue

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}

variable (R : HawkingPointResidue C)

/-- Signed chiral residue contribution. -/
def signedWeight : ℤ :=
  R.weight * R.chirality.sign

/--
Crossover of a residue.

The projective ray crosses by the conformal crossover map. The chiral
orientation flips.
-/
def crossover : HawkingPointResidue C where
  ray := ConformalCrossover.crossover R.ray
  weight := R.weight
  chirality := R.chirality.flip

/-- Crossover reverses signed chiral contribution. -/
theorem signedWeight_crossover :
    R.crossover.signedWeight = -R.signedWeight := by
  rcases R with ⟨ray, weight, χ⟩
  cases χ <;> simp [signedWeight, crossover, Chirality.sign, Chirality.flip]

/--
Applying crossover twice restores the ray projectively and restores finite labels exactly.
-/
theorem sameRay_crossover_twice :
    ProjectiveNullRay.SameRay
      (ConformalCrossover.crossover
        (ConformalCrossover.crossover R.ray))
      R.ray :=
  R.ray.sameRay_crossover_twice

@[simp]
theorem crossover_weight :
    R.crossover.weight = R.weight :=
  rfl

@[simp]
theorem crossover_chirality :
    R.crossover.chirality = R.chirality.flip :=
  rfl

end HawkingPointResidue

/-! ## 3. Finite Hawking-point divisors -/

/--
A finite Hawking-point divisor.

The finiteness is important. A finite divisor is auditably resolvable
residue-by-residue.
-/
structure HawkingPointDivisor
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ConformalCrossoverDatum V) where
  residues : List (HawkingPointResidue C)

namespace HawkingPointDivisor

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}

variable (D : HawkingPointDivisor C)

/-- Number of listed residues. -/
def supportCard : ℕ :=
  D.residues.length

/-- Total unsigned integer weight. -/
def totalWeight : ℤ :=
  (D.residues.map (fun R => R.weight)).sum

/-- Total chiral charge. -/
def chiralCharge : ℤ :=
  (D.residues.map (fun R => R.signedWeight)).sum

/-- Crossover of the whole divisor. -/
def crossover : HawkingPointDivisor C where
  residues := D.residues.map HawkingPointResidue.crossover

/-- The empty divisor has zero chiral charge. -/
theorem chiralCharge_empty :
    ({ residues := [] } : HawkingPointDivisor C).chiralCharge = 0 :=
  rfl

/-- Cons formula for chiral charge. -/
theorem chiralCharge_cons
    (R : HawkingPointResidue C)
    (Rs : List (HawkingPointResidue C)) :
    ({ residues := R :: Rs } : HawkingPointDivisor C).chiralCharge =
      R.signedWeight +
        ({ residues := Rs } : HawkingPointDivisor C).chiralCharge := by
  rfl

/-- Crossover reverses the total chiral charge. -/
theorem chiralCharge_crossover :
    D.crossover.chiralCharge = -D.chiralCharge := by
  cases D with
  | mk residues =>
  induction residues with
  | nil =>
      simp [crossover, chiralCharge]
  | cons R Rs ih =>
      simp [crossover, chiralCharge, HawkingPointResidue.signedWeight_crossover]
      have htail :
          (List.map ((fun R => R.signedWeight) ∘ HawkingPointResidue.crossover) Rs).sum =
            -(List.map (fun R => R.signedWeight) Rs).sum := by
        simpa [crossover, chiralCharge] using ih
      rw [htail]
      ring

/-- Chiral balance means total chiral charge vanishes. -/
def IsChirallyBalanced : Prop :=
  D.chiralCharge = 0

/-- Crossover preserves chiral balance. -/
theorem crossover_chirallyBalanced_iff :
    D.crossover.IsChirallyBalanced ↔ D.IsChirallyBalanced := by
  constructor
  · intro h
    have hneg : -D.chiralCharge = 0 := by
      simpa [IsChirallyBalanced, chiralCharge_crossover] using h
    exact neg_eq_zero.mp hneg
  · intro h
    rw [IsChirallyBalanced, chiralCharge_crossover, h]
    simp

/--
Every residue in the divisor is explicitly in the finite list. This is the
finite-support audit boundary.
-/
theorem residue_mem_finite_support
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues) :
    ∃ Rs₁ Rs₂ : List (HawkingPointResidue C),
      D.residues = Rs₁ ++ R :: Rs₂ := by
  cases D with
  | mk residues =>
  induction residues with
  | nil =>
      cases hR
  | cons S Ss ih =>
      simp at hR
      rcases hR with h | h
      · subst h
        exact ⟨[], Ss, rfl⟩
      · rcases ih h with ⟨Rs₁, Rs₂, hsplit⟩
        have hSs : Ss = Rs₁ ++ R :: Rs₂ := by
          simpa using hsplit
        exact ⟨S :: Rs₁, Rs₂, by simp [hSs]⟩

end HawkingPointDivisor

/-! ## 4. Resolution audit -/

/--
A smooth seed resolving one crossover residue.

`Smooth` and `Orientation` are supplied by the concrete geometric model.
-/
structure ResolvedResidueSeed
    {V NewState : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup NewState] [Module ℝ NewState]
    {C : ConformalCrossoverDatum V}
    (Smooth : NewState → Prop)
    (Orientation : NewState → Chirality)
    (R : HawkingPointResidue C) where
  seed : NewState
  seed_ne_zero : seed ≠ 0
  seed_smooth : Smooth seed
  orientation_matches : Orientation seed = R.chirality

/--
A divisor resolution audit.

For each listed residue, produce a nonzero smooth seed whose orientation
matches the residue chirality.
-/
structure DivisorResolutionAudit
    {V NewState : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup NewState] [Module ℝ NewState]
    {C : ConformalCrossoverDatum V}
    (Smooth : NewState → Prop)
    (Orientation : NewState → Chirality)
    (D : HawkingPointDivisor C) where
  resolve :
    ∀ R : HawkingPointResidue C,
      R ∈ D.residues →
        ResolvedResidueSeed Smooth Orientation R

namespace DivisorResolutionAudit

variable
    {V NewState : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup NewState] [Module ℝ NewState]
    {C : ConformalCrossoverDatum V}
    {Smooth : NewState → Prop}
    {Orientation : NewState → Chirality}
    {D : HawkingPointDivisor C}

variable (A : DivisorResolutionAudit Smooth Orientation D)

/-- Every residue in an audited divisor has a nonzero smooth resolved seed. -/
theorem every_residue_has_smooth_seed
    (A : DivisorResolutionAudit Smooth Orientation D)
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues) :
    ∃ s : NewState,
      s ≠ 0 ∧
      Smooth s ∧
      Orientation s = R.chirality := by
  let S := DivisorResolutionAudit.resolve A R hR
  exact
    ⟨S.seed,
      S.seed_ne_zero,
      S.seed_smooth,
      S.orientation_matches⟩

/-- Resolved seed orientation determines the chiral sign. -/
theorem seed_orientation_sign
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues) :
    Chirality.sign (Orientation (DivisorResolutionAudit.resolve A R hR).seed) =
      Chirality.sign R.chirality := by
  rw [(DivisorResolutionAudit.resolve A R hR).orientation_matches]

/-- A left-chiral residue resolves to a left-oriented seed. -/
theorem left_residue_resolves_left
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues)
    (hχ : R.chirality = Chirality.left) :
    Orientation (DivisorResolutionAudit.resolve A R hR).seed = Chirality.left := by
  rw [(DivisorResolutionAudit.resolve A R hR).orientation_matches, hχ]

/-- A right-chiral residue resolves to a right-oriented seed. -/
theorem right_residue_resolves_right
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues)
    (hχ : R.chirality = Chirality.right) :
    Orientation (DivisorResolutionAudit.resolve A R hR).seed = Chirality.right := by
  rw [(DivisorResolutionAudit.resolve A R hR).orientation_matches, hχ]

end DivisorResolutionAudit

/-! ## 5. Chiral vorticity readout -/

/--
A chiral vorticity readout on resolved seeds.

This is the formal version of the admissible claim:

“chirality determines vorticity orientation.”

It does not assert Navier-Stokes regularity.
-/
abbrev ChiralVorticityReadout (NewState : Type*) :=
  NewState → Chirality

namespace ChiralVorticityReadout

variable {NewState : Type*}
variable (Vort : ChiralVorticityReadout NewState)

abbrev orientation : NewState → Chirality :=
  Vort

def vorticitySign : NewState → ℤ :=
  fun s => Chirality.sign (Vort s)

theorem vorticitySign_eq_orientation
    (s : NewState) :
    Vort.vorticitySign s = Chirality.sign (Vort.orientation s) :=
  rfl

/-- Vorticity sign is fixed by orientation. -/
theorem sign_eq
    (s : NewState) :
    Vort.vorticitySign s =
      Chirality.sign (Vort.orientation s) :=
  Vort.vorticitySign_eq_orientation s

end ChiralVorticityReadout

namespace DivisorResolutionAudit

variable
    {V NewState : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup NewState] [Module ℝ NewState]
    {C : ConformalCrossoverDatum V}
    {Smooth : NewState → Prop}
    {D : HawkingPointDivisor C}

variable
    (Vort : ChiralVorticityReadout NewState)

variable
    (A : DivisorResolutionAudit Smooth Vort.orientation D)

/--
For an audited residue, the resolved vorticity sign equals the residue
chirality sign.
-/
theorem resolved_seed_vorticity_sign
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues) :
    Vort.vorticitySign (DivisorResolutionAudit.resolve A R hR).seed =
      Chirality.sign R.chirality := by
  rw [Vort.vorticitySign_eq_orientation]
  exact A.seed_orientation_sign hR

/-- Left residue gives positive vorticity sign. -/
theorem left_residue_vorticity_positive
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues)
    (hχ : R.chirality = Chirality.left) :
    Vort.vorticitySign (DivisorResolutionAudit.resolve A R hR).seed = 1 := by
  rw [A.resolved_seed_vorticity_sign Vort hR, hχ]
  simp [Chirality.sign]

/-- Right residue gives negative vorticity sign. -/
theorem right_residue_vorticity_negative
    {R : HawkingPointResidue C}
    (hR : R ∈ D.residues)
    (hχ : R.chirality = Chirality.right) :
    Vort.vorticitySign (DivisorResolutionAudit.resolve A R hR).seed = -1 := by
  rw [A.resolved_seed_vorticity_sign Vort hR, hχ]
  simp [Chirality.sign]

end DivisorResolutionAudit

end InfoGeometry.OperatorAlgebra.CrossoverResidue

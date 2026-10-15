import InfoGeometry.Topology.KleinQuotientDeckInvariants
import InfoGeometry.Canonical.O55FiveGradeClosure
import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Clifford.ConformalLieAlgebra55
import InfoGeometry.CliffordWeyl.SplitSpinorFierz
import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic.NoncommRing

/-!
# The Klein deck orientation character on the native `Cl(5,5)` five-grading

The affine Klein deck group acts on the existing split `Cl(5,5)` algebra by
its orientation character: orientation-preserving deck elements act trivially,
and orientation-reversing elements act by the already-defined conformal
inversion `thetaOp`.  The action is nontrivial and exchanges actual opposite
grade generators.  This is an algebraic action on the five-graded carrier; it
does not identify the affine deck group with a fundamental group or assert a
physical CPT theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinDeckFiveGradeAction

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLieAlgebra55

local instance kleinDeckGroupStructure : Group KleinDeckGroup where
  mul := KleinDeckGroup.mul
  one := KleinDeckGroup.one
  inv := KleinDeckGroup.inv
  mul_assoc := KleinDeckGroup.mul_assoc
  one_mul := KleinDeckGroup.one_mul
  mul_one := KleinDeckGroup.mul_one
  inv_mul_cancel := KleinDeckGroup.mul_left_inv

/-- The existing five-grade reflection as a ring automorphism. -/
def thetaRingAut : RingAut (Alg 5) where
  toFun := thetaOp
  invFun := thetaOp
  left_inv := theta_inv
  right_inv := theta_inv
  map_mul' := theta_mul
  map_add' := by
    intro x y
    dsimp [thetaOp]
    noncomm_ring

/-- The deck orientation character, expressed as a sign. -/
def deckOrientationSign (g : KleinDeckGroup) : ℤ := signZ g.n

theorem deckOrientationSign_mul (g h : KleinDeckGroup) :
    deckOrientationSign (KleinDeckGroup.mul g h) =
      deckOrientationSign g * deckOrientationSign h := by
  exact signZ_add g.n h.n

private theorem deckOrientationSign_cases (g : KleinDeckGroup) :
    deckOrientationSign g = 1 ∨ deckOrientationSign g = -1 := by
  simp only [deckOrientationSign, signZ]
  split_ifs <;> simp

/-- Linear part of the affine action of a deck element on the covering plane. -/
def deckActionDifferential (g : KleinDeckGroup) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![signR g.n, 0; 0, 1]

/-- The parity character used by the Clifford action is exactly the determinant
of the differential of the affine Klein deck transformation. -/
theorem deckOrientationSign_eq_determinant (g : KleinDeckGroup) :
    (deckOrientationSign g : ℝ) = Matrix.det (deckActionDifferential g) := by
  simp [deckOrientationSign, deckActionDifferential, signR, Matrix.det_fin_two]

/-- The deck group acts by ring automorphisms on the actual split Clifford
algebra.  Its parity is the second coordinate of the semidirect-product deck
group, not an independently chosen label action. -/
def deckGradeAction (g : KleinDeckGroup) : RingAut (Alg 5) :=
  if deckOrientationSign g = 1 then 1 else thetaRingAut

theorem deckGradeAction_one :
    deckGradeAction KleinDeckGroup.one = 1 := by
  simp [deckGradeAction, deckOrientationSign, signZ, KleinDeckGroup.one]

/-- Composition of deck transformations is represented by composition of the
corresponding Clifford ring automorphisms. -/
theorem deckGradeAction_mul (g h : KleinDeckGroup) :
    deckGradeAction (KleinDeckGroup.mul g h) =
      deckGradeAction g * deckGradeAction h := by
  have hg := deckOrientationSign_cases g
  have hh := deckOrientationSign_cases h
  have hmul := deckOrientationSign_mul g h
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · simp [deckGradeAction, hg, hh, hmul]
  · simp [deckGradeAction, hg, hh, hmul]
  · simp [deckGradeAction, hg, hh, hmul]
  · ext x
    simp [deckGradeAction, hg, hh, hmul, thetaRingAut, theta_inv]

/-- Operators invariant under every Klein deck transformation form a
subring of the noncommutative five-graded Clifford algebra. -/
def deckInvariantSubring : Subring (Alg 5) where
  carrier := {x | ∀ g : KleinDeckGroup, deckGradeAction g x = x}
  zero_mem' := by
    intro g
    simp
  one_mem' := by
    intro g
    simp
  add_mem' := by
    intro a b ha hb g
    rw [(deckGradeAction g).map_add, ha g, hb g]
  mul_mem' := by
    intro a b ha hb g
    rw [(deckGradeAction g).map_mul, ha g, hb g]
  neg_mem' := by
    intro a ha g
    rw [(deckGradeAction g).map_neg, ha g]

/-- Typed representation of the actual Klein deck group by automorphisms of
the native split Clifford algebra. -/
def deckGradeActionHom : KleinDeckGroup →* RingAut (Alg 5) where
  toFun := deckGradeAction
  map_one' := deckGradeAction_one
  map_mul' := deckGradeAction_mul

@[simp] theorem deckGradeAction_apply (g : KleinDeckGroup) (x : Alg 5) :
    deckGradeAction g x =
      if deckOrientationSign g = 1 then x else thetaOp x := by
  by_cases h : deckOrientationSign g = 1 <;>
    simp [deckGradeAction, h, thetaRingAut]

@[simp] theorem deckGradeAction_translation (x : Alg 5) :
    deckGradeAction ⟨1, 0⟩ x = x := by
  simp [deckGradeAction, deckOrientationSign, signZ]

@[simp] theorem deckGradeAction_glide (x : Alg 5) :
    deckGradeAction ⟨0, 1⟩ x = thetaOp x := by
  simp [deckGradeAction, deckOrientationSign, signZ, thetaRingAut]

/-- The orientation-reversing glide exchanges the actual positive and
negative first-grade subspaces of `Cl(5,5)`. -/
theorem glide_maps_grade
    (g : InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade)
    (x : Alg 5)
    (hx : x ∈ gradeSpace g) :
    deckGradeAction ⟨0, 1⟩ x ∈ gradeSpace
      (InfoGeometry.Canonical.ConformalFiveGradeInversion.ConformalGrade.swap g) := by
  rw [deckGradeAction_glide]
  exact theta_maps g x hx

/-- On the concrete null generators, the glide exchanges the two opposite
grade modes; hence this deck action is not the trivial action. -/
theorem glide_exchanges_null_generators :
    deckGradeAction ⟨0, 1⟩ u5 = v5 ∧
    deckGradeAction ⟨0, 1⟩ v5 = u5 := by
  exact ⟨by rw [deckGradeAction_glide, theta_u5],
    by rw [deckGradeAction_glide, theta_v5]⟩

theorem glide_action_nontrivial :
    deckGradeAction ⟨0, 1⟩ ≠ 1 := by
  intro h
  have hact : deckGradeAction ⟨0, 1⟩ u5 = v5 := by
    rw [deckGradeAction_glide, theta_u5]
  have hfixed : deckGradeAction ⟨0, 1⟩ u5 = u5 := by
    simpa using congrArg (fun f : RingAut (Alg 5) => f u5) h
  have hu : v5 = u5 := hact.symm.trans hfixed
  have hne : u5 ≠ v5 := by
    intro huv
    have hrel := u5_v5_add_v5_u5
    have hone : (1 : Alg 5) = 0 := by
      calc
        1 = u5 * v5 + v5 * u5 := hrel.symm
        _ = 0 := by rw [← huv, u5_sq]; simp
    have h01 : (0 : Alg 5) ≠ 1 := by
      intro h
      have hmat := congrArg (InfoGeometry.CliffordWeyl.SplitSpinorFierz.spinorEquiv 5) h
      have hmat' : (0 : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) = 1 := by
        simpa using hmat
      exact zero_ne_one hmat'
    exact h01 hone.symm
  exact hne hu.symm

/-- The invariant subring for the full affine deck group is exactly the fixed
subring of the nontrivial glide reflection `thetaOp`.  This is the concrete
Erlangen-style invariant algebra for this action. -/
theorem mem_deckInvariantSubring_iff_theta_fixed (x : Alg 5) :
    x ∈ deckInvariantSubring ↔ thetaOp x = x := by
  constructor
  · intro hx
    have hglide := hx ⟨0, 1⟩
    rw [deckGradeAction_glide] at hglide
    exact hglide
  · intro hx g
    rw [deckGradeAction_apply]
    split_ifs with h
    · rfl
    · exact hx

end InfoGeometry.Canonical.KleinDeckFiveGradeAction

end noncomputable section

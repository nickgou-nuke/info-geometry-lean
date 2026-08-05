import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Algebraic GNS quotient over the native Cuntz tensor quotient

This file records the genuinely algebraic part of a GNS construction.  The
carrier is the native noncommutative `CuntzAlg n`; no commutative diagonal
model, Hilbert completion, or C*-analytic assertion is introduced here.
The state supplies the null-relation and its left-action stability explicitly,
which is the exact data needed for quotient descent.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzGNSTensorQuotient

open InfoGeometry.Algebra.CuntzTensorQuotient

structure CuntzGNSState (n : ℕ) where
  toLinearMap : CuntzAlg n →ₗ[ℂ] ℂ
  normalized : toLinearMap 1 = 1
  positive : ∀ x : CuntzAlg n,
    0 ≤ (toLinearMap (star x * x)).re
  nullRel : CuntzAlg n → CuntzAlg n → Prop
  null_refl : ∀ x, nullRel x x
  null_symm : ∀ {x y}, nullRel x y → nullRel y x
  null_trans : ∀ {x y z}, nullRel x y → nullRel y z → nullRel x z
  null_left_stable : ∀ a {x y}, nullRel x y → nullRel (a * x) (a * y)

def gnsSetoid (F : CuntzGNSState n) : Setoid (CuntzAlg n) where
  r := F.nullRel
  iseqv := {
    refl := F.null_refl
    symm := F.null_symm
    trans := F.null_trans }

abbrev GNSQuotient (F : CuntzGNSState n) : Type _ :=
  Quotient (gnsSetoid F)

def cyclicVector (F : CuntzGNSState n) : GNSQuotient F :=
  Quotient.mk (gnsSetoid F) 1

def leftRepresentation (F : CuntzGNSState n) (a : CuntzAlg n) :
    GNSQuotient F → GNSQuotient F :=
  Quotient.lift (fun x => Quotient.mk (gnsSetoid F) (a * x))
    (by
      intro x y hxy
      exact Quotient.sound (F.null_left_stable a hxy))

theorem cyclicVector_normalized (F : CuntzGNSState n) :
    F.toLinearMap 1 = 1 :=
  F.normalized

@[simp] theorem leftRepresentation_cyclic (F : CuntzGNSState n)
    (a : CuntzAlg n) :
    leftRepresentation F a (cyclicVector F) =
      Quotient.mk (gnsSetoid F) a := by
  change Quotient.mk (gnsSetoid F) (a * 1) =
    Quotient.mk (gnsSetoid F) a
  rw [mul_one]

theorem leftRepresentation_one (F : CuntzGNSState n) :
    leftRepresentation F (1 : CuntzAlg n) = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk (gnsSetoid F) (1 * x) =
    Quotient.mk (gnsSetoid F) x
  rw [one_mul]

theorem leftRepresentation_mul (F : CuntzGNSState n)
    (a b : CuntzAlg n) (q : GNSQuotient F) :
    leftRepresentation F (a * b) q =
      leftRepresentation F a (leftRepresentation F b q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk (gnsSetoid F) ((a * b) * x) =
    Quotient.mk (gnsSetoid F) (a * (b * x))
  rw [mul_assoc]

end InfoGeometry.Algebra.CuntzGNSTensorQuotient

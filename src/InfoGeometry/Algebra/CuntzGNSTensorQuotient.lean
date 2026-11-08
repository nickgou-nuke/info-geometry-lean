import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

def CuntzGNSStateLaws (n : ℕ)
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (nullRel : CuntzAlg n → CuntzAlg n → Prop) : Prop :=
  (φ 1 = 1) ∧
  (∀ x : CuntzAlg n, 0 ≤ (φ (star x * x)).re) ∧
  (∀ x, nullRel x x) ∧
  (∀ {x y}, nullRel x y → nullRel y x) ∧
  (∀ {x y z}, nullRel x y → nullRel y z → nullRel x z) ∧
  (∀ a {x y}, nullRel x y → nullRel (a * x) (a * y))

def CuntzGNSState (n : ℕ) :=
  {d : (CuntzAlg n →ₗ[ℂ] ℂ) ×
      (CuntzAlg n → CuntzAlg n → Prop) // CuntzGNSStateLaws n d.1 d.2}

namespace CuntzGNSState

def toLinearMap (F : CuntzGNSState n) : CuntzAlg n →ₗ[ℂ] ℂ := F.1.1
def nullRel (F : CuntzGNSState n) : CuntzAlg n → CuntzAlg n → Prop := F.1.2

theorem normalized (F : CuntzGNSState n) : F.toLinearMap 1 = 1 := F.2.1
theorem positive (F : CuntzGNSState n) (x : CuntzAlg n) :
    0 ≤ (F.toLinearMap (star x * x)).re := F.2.2.1 x
theorem null_refl (F : CuntzGNSState n) (x : CuntzAlg n) : F.nullRel x x := F.2.2.2.1 x
theorem null_symm (F : CuntzGNSState n) {x y : CuntzAlg n} :
    F.nullRel x y → F.nullRel y x := F.2.2.2.2.1
theorem null_trans (F : CuntzGNSState n) {x y z : CuntzAlg n} :
    F.nullRel x y → F.nullRel y z → F.nullRel x z := F.2.2.2.2.2.1
theorem null_left_stable (F : CuntzGNSState n) (a : CuntzAlg n) {x y : CuntzAlg n} :
    F.nullRel x y → F.nullRel (a * x) (a * y) := by
  change F.1.2 x y → F.1.2 (a * x) (a * y)
  exact F.2.2.2.2.2.2 a

end CuntzGNSState

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

theorem leftRepresentation_cuntz_isometry (F : CuntzGNSState n)
    (i : Fin n) (q : GNSQuotient F) :
    leftRepresentation F (cuntzSdag n i)
        (leftRepresentation F (cuntzS n i) q) = q := by
  rw [← leftRepresentation_mul F (cuntzSdag n i) (cuntzS n i) q]
  rw [cuntz_isometry]
  simpa using congrArg (fun f => f q) (leftRepresentation_one F)

end InfoGeometry.Algebra.CuntzGNSTensorQuotient

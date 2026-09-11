import InfoGeometry.Algebra.InductiveSuperClosureLemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Infinite image superclosure lemmas

This extends `InductiveSuperClosureLemmas` to an explicit infinite target.

The target is a semiring `Limit`, and every finite stage maps into it by a
ring homomorphism.  The result is image-local: finite-stage closure is proved
first, then transported through the chosen stage map.  If the stage maps form a
compatible cone, transported generator images are also independent of the
finite stage.
-/

namespace InfoGeometry.Algebra.InfiniteSuperClosureLemmas

open InductiveSuperClosureLemmas

universe u

section ImageLimit

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/-- Compatibility of stage maps into an infinite target. -/
def CompatibleCone
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit) : Prop :=
  ∀ (n : Nat) (x : Stage n), toLimit (n + 1) (bond n x) = toLimit n x

/--
If a stagewise object is transported by the bonding maps, its image in a
compatible target is unchanged after one step.
-/
theorem compatibleCone_image_step
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n, bond n (F n) = F (n + 1))
    (n : Nat) :
    toLimit (n + 1) (F (n + 1)) = toLimit n (F n) := by
  rw [← hF n]
  exact hcone n (F n)

/--
If a stagewise object is transported by the bonding maps, every finite-stage
image agrees with the stage-zero image in a compatible target.
-/
theorem compatibleCone_image_eq_zero
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n, bond n (F n) = F (n + 1)) :
    ∀ n : Nat, toLimit n (F n) = toLimit 0 (F 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        toLimit (n + 1) (F (n + 1)) = toLimit n (F n) := by
          exact compatibleCone_image_step bond toLimit hcone F hF n
        _ = toLimit 0 (F 0) := ih

/--
Single-supercharge closure transported into an infinite target image.
-/
theorem limitImage_superClosure_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (Q H Z : ∀ n : Nat, Stage n)
    (h0 : SuperClosureAt Q H Z 0)
    (hQ : ∀ n, bond n (Q n) = Q (n + 1))
    (hH : ∀ n, bond n (H n) = H (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat,
      anticommutator (toLimit n (Q n)) (toLimit n (Q n)) =
        toLimit n (H n) + toLimit n (Z n) := by
  intro n
  have hstage : SuperClosureAt Q H Z n :=
    superClosure_all bond Q H Z h0 hQ hH hZ n
  unfold SuperClosureAt at hstage
  calc
    anticommutator (toLimit n (Q n)) (toLimit n (Q n))
        = toLimit n (anticommutator (Q n) (Q n)) := by
          exact (map_anticommutator (toLimit n) (Q n) (Q n)).symm
    _ = toLimit n (H n + Z n) := by
          rw [hstage]
    _ = toLimit n (H n) + toLimit n (Z n) := by
          simp

/--
Single-supercharge closure in a compatible target, read back at stage zero.
-/
theorem compatibleCone_limitImage_superClosure_zeroStage
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (Q H Z : ∀ n : Nat, Stage n)
    (h0 : SuperClosureAt Q H Z 0)
    (hQ : ∀ n, bond n (Q n) = Q (n + 1))
    (hH : ∀ n, bond n (H n) = H (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat,
      anticommutator (toLimit n (Q n)) (toLimit n (Q n)) =
        toLimit 0 (H 0) + toLimit 0 (Z 0) := by
  intro n
  calc
    anticommutator (toLimit n (Q n)) (toLimit n (Q n))
        = toLimit n (H n) + toLimit n (Z n) := by
          exact limitImage_superClosure_all bond toLimit Q H Z h0 hQ hH hZ n
    _ = toLimit 0 (H 0) + toLimit 0 (Z 0) := by
          rw [compatibleCone_image_eq_zero bond toLimit hcone H hH n,
            compatibleCone_image_eq_zero bond toLimit hcone Z hZ n]

/--
Mixed odd-odd closure transported into an infinite target image.
-/
theorem limitImage_mixedSuperClosure_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (QA QB K Z : ∀ n : Nat, Stage n)
    (h0 : MixedSuperClosureAt QA QB K Z 0)
    (hQA : ∀ n, bond n (QA n) = QA (n + 1))
    (hQB : ∀ n, bond n (QB n) = QB (n + 1))
    (hK : ∀ n, bond n (K n) = K (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat,
      anticommutator (toLimit n (QA n)) (toLimit n (QB n)) =
        toLimit n (K n) + toLimit n (Z n) := by
  intro n
  have hstage : MixedSuperClosureAt QA QB K Z n :=
    mixedSuperClosure_all bond QA QB K Z h0 hQA hQB hK hZ n
  unfold MixedSuperClosureAt at hstage
  calc
    anticommutator (toLimit n (QA n)) (toLimit n (QB n))
        = toLimit n (anticommutator (QA n) (QB n)) := by
          exact (map_anticommutator (toLimit n) (QA n) (QB n)).symm
    _ = toLimit n (K n + Z n) := by
          rw [hstage]
    _ = toLimit n (K n) + toLimit n (Z n) := by
          simp

/--
Mixed odd-odd closure in a compatible target, read back at stage zero.
-/
theorem compatibleCone_limitImage_mixedSuperClosure_zeroStage
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (QA QB K Z : ∀ n : Nat, Stage n)
    (h0 : MixedSuperClosureAt QA QB K Z 0)
    (hQA : ∀ n, bond n (QA n) = QA (n + 1))
    (hQB : ∀ n, bond n (QB n) = QB (n + 1))
    (hK : ∀ n, bond n (K n) = K (n + 1))
    (hZ : ∀ n, bond n (Z n) = Z (n + 1)) :
    ∀ n : Nat,
      anticommutator (toLimit n (QA n)) (toLimit n (QB n)) =
        toLimit 0 (K 0) + toLimit 0 (Z 0) := by
  intro n
  calc
    anticommutator (toLimit n (QA n)) (toLimit n (QB n))
        = toLimit n (K n) + toLimit n (Z n) := by
          exact limitImage_mixedSuperClosure_all
            bond toLimit QA QB K Z h0 hQA hQB hK hZ n
    _ = toLimit 0 (K 0) + toLimit 0 (Z 0) := by
          rw [compatibleCone_image_eq_zero bond toLimit hcone K hK n,
            compatibleCone_image_eq_zero bond toLimit hcone Z hZ n]

end ImageLimit

end InfoGeometry.Algebra.InfiniteSuperClosureLemmas

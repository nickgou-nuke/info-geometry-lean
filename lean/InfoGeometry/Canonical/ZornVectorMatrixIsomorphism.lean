import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-!
## Multiplicative comparison of the two split-octonion models

`ZornVectorMatrixRationalEquiv` owns only the rational linear coordinates.
This file owns the separate statement that the coordinate Cayley--Dickson
product agrees with the native Zorn product.  No associative `AlgEquiv` is
introduced: both products are explicit and the Zorn product is nonassociative.
-/

abbrev SplitQuaternionQ := ℚ × ℚ × ℚ × ℚ

def splitQuaternionOfQ
    (x : StandardRationalSplitOctonion) : SplitQuaternionQ :=
  (x .one, (x .i, (x .j, x .k)))

def splitQuaternionLPartQ
    (x : StandardRationalSplitOctonion) : SplitQuaternionQ :=
  (x .l, (x .il, (x .jl, x .kl)))

def splitQuaternionConjQ (q : SplitQuaternionQ) : SplitQuaternionQ :=
  (q.1, (-q.2.1, (-q.2.2.1, -q.2.2.2)))

def splitQuaternionAddQ
    (p q : SplitQuaternionQ) : SplitQuaternionQ :=
  (p.1 + q.1,
    (p.2.1 + q.2.1,
      (p.2.2.1 + q.2.2.1, p.2.2.2 + q.2.2.2)))

def splitQuaternionMulQ
    (p q : SplitQuaternionQ) : SplitQuaternionQ :=
  (p.1 * q.1 - p.2.1 * q.2.1 -
      p.2.2.1 * q.2.2.1 - p.2.2.2 * q.2.2.2,
    (p.1 * q.2.1 + p.2.1 * q.1 +
        p.2.2.1 * q.2.2.2 - p.2.2.2 * q.2.2.1,
      (p.1 * q.2.2.1 - p.2.1 * q.2.2.2 +
          p.2.2.1 * q.1 + p.2.2.2 * q.2.1,
        p.1 * q.2.2.2 + p.2.1 * q.2.2.1 -
          p.2.2.1 * q.2.1 + p.2.2.2 * q.1)))

def splitOctonionOfQuaternionPairQ
    (q r : SplitQuaternionQ) : StandardRationalSplitOctonion
  | .one => q.1
  | .l => r.1
  | .i => q.2.1
  | .il => r.2.1
  | .j => q.2.2.1
  | .jl => r.2.2.1
  | .k => q.2.2.2
  | .kl => r.2.2.2

def splitOctonionMulQ
    (x y : StandardRationalSplitOctonion) :
    StandardRationalSplitOctonion :=
  let q := splitQuaternionOfQ x
  let r := splitQuaternionLPartQ x
  let s := splitQuaternionOfQ y
  let t := splitQuaternionLPartQ y
  let left := splitQuaternionAddQ
    (splitQuaternionMulQ q s)
    (splitQuaternionMulQ (splitQuaternionConjQ t) r)
  let right := splitQuaternionAddQ
    (splitQuaternionMulQ t q)
    (splitQuaternionMulQ r (splitQuaternionConjQ s))
  splitOctonionOfQuaternionPairQ left right

theorem zornVectorMatrixRationalEquiv_map_one :
    zornVectorMatrixRationalEquiv (rationalBasis .one) =
      ({ a := 1, v := 0, w := 0, b := 1 } : ZornVectorMatrix ℚ) :=
  rationalEquiv_one

theorem zornVectorMatrixRationalEquiv_map_mul
    (x y : StandardRationalSplitOctonion) :
    zornVectorMatrixRationalEquiv (splitOctonionMulQ x y) =
      ZornVectorMatrix.mul
        (zornVectorMatrixRationalEquiv x)
        (zornVectorMatrixRationalEquiv y) := by
  change toZorn (splitOctonionMulQ x y) =
    ZornVectorMatrix.mul (toZorn x) (toZorn y)
  apply ZornVectorMatrix.ext
  · simp [toZorn, splitOctonionMulQ, splitQuaternionOfQ,
      splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
      splitQuaternionMulQ, splitOctonionOfQuaternionPairQ,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring
  · funext i
    fin_cases i <;>
      dsimp [toZorn, splitOctonionMulQ, splitQuaternionOfQ,
        splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
        splitQuaternionMulQ, splitOctonionOfQuaternionPairQ,
        ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross] <;>
      ring
  · funext i
    fin_cases i <;>
      dsimp [toZorn, splitOctonionMulQ, splitQuaternionOfQ,
        splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
        splitQuaternionMulQ, splitOctonionOfQuaternionPairQ,
        ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross] <;>
      ring
  · simp [toZorn, splitOctonionMulQ, splitQuaternionOfQ,
      splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
      splitQuaternionMulQ, splitOctonionOfQuaternionPairQ,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring

structure NonAssocEquiv
    (A B : Type*)
    (mulA : A → A → A) (mulB : B → B → B) where
  toEquiv : A ≃ B
  map_mul : ∀ x y, toEquiv (mulA x y) =
    mulB (toEquiv x) (toEquiv y)

noncomputable def splitOctonionZornNonAssocEquiv :
    NonAssocEquiv
      StandardRationalSplitOctonion
      (ZornVectorMatrix ℚ)
      splitOctonionMulQ
      ZornVectorMatrix.mul where
  toEquiv := zornVectorMatrixRationalEquiv
  map_mul := zornVectorMatrixRationalEquiv_map_mul

end InfoGeometry.Canonical

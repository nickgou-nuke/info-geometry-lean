import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Typed complex polarized Jordan-pair data

The positive and negative polarization sectors are distinct tagged carriers.
Only the rectangular triple is defined on the polarized pair.  A spin-factor
triple is defined separately on a common carrier, where its final term is
well-typed.  No real signature or TKK identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexPolarizedJordanPair

@[ext] structure PPlus where
  scalar : ℂ
  vector : Fin 3 → ℂ

@[ext] structure PMinus where
  scalar : ℂ
  vector : Fin 3 → ℂ

def beta (x : PPlus) (y : PMinus) : ℂ :=
  x.scalar * y.scalar + ∑ i, x.vector i * y.vector i

def plusScale (c : ℂ) (x : PPlus) : PPlus :=
  ⟨c * x.scalar, fun i => c * x.vector i⟩

def plusAdd (x z : PPlus) : PPlus :=
  ⟨x.scalar + z.scalar, fun i => x.vector i + z.vector i⟩

def minusScale (c : ℂ) (y : PMinus) : PMinus :=
  ⟨c * y.scalar, fun i => c * y.vector i⟩

def minusAdd (y w : PMinus) : PMinus :=
  ⟨y.scalar + w.scalar, fun i => y.vector i + w.vector i⟩

def rectangularTriplePlus (x z : PPlus) (y : PMinus) : PPlus :=
  plusAdd (plusScale (beta x y) z) (plusScale (beta z y) x)

def rectangularTripleMinus (y w : PMinus) (x : PPlus) : PMinus :=
  minusAdd (minusScale (beta x y) w) (minusScale (beta x w) y)

theorem rectangularTriplePlus_outer (x z : PPlus) (y : PMinus) :
    rectangularTriplePlus x z y = rectangularTriplePlus z x y := by
  ext <;> simp [rectangularTriplePlus, plusAdd, plusScale, beta, add_comm,
    add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

theorem rectangularTripleMinus_outer (y w : PMinus) (x : PPlus) :
    rectangularTripleMinus y w x = rectangularTripleMinus w y x := by
  ext <;> simp [rectangularTripleMinus, minusAdd, minusScale, beta, add_comm,
    add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

@[ext] structure CommonCarrier where
  scalar : ℂ
  vector : Fin 3 → ℂ

def commonB (x y : CommonCarrier) : ℂ :=
  x.scalar * y.scalar + ∑ i, x.vector i * y.vector i

def commonScale (c : ℂ) (x : CommonCarrier) : CommonCarrier :=
  ⟨c * x.scalar, fun i => c * x.vector i⟩

def commonAdd (x z : CommonCarrier) : CommonCarrier :=
  ⟨x.scalar + z.scalar, fun i => x.vector i + z.vector i⟩

def commonNeg (x : CommonCarrier) : CommonCarrier :=
  ⟨-x.scalar, fun i => -x.vector i⟩

def spinFactorTriple (x y z : CommonCarrier) : CommonCarrier :=
  commonAdd
    (commonAdd (commonScale (commonB x y) z)
      (commonScale (commonB z y) x))
    (commonNeg (commonScale (commonB x z) y))

theorem spinFactorTriple_outer (x y z : CommonCarrier) :
    spinFactorTriple x y z = spinFactorTriple z y x := by
  ext <;> simp [spinFactorTriple, commonAdd, commonScale, commonNeg, commonB,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

structure RealJordanData where
  scalar : ℝ
  vector : Fin 3 → ℝ

def realB (x y : RealJordanData) : ℝ :=
  x.scalar * y.scalar + ∑ i, x.vector i * y.vector i

def extendedRealCarrier := ℝ × RealJordanData × ℝ

end InfoGeometry.Canonical.ComplexPolarizedJordanPair

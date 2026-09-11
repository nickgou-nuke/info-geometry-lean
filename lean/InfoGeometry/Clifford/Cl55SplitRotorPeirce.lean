import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Clifford.Cl55SplitRotorPeirce

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

def peircePlus (i : Fin 5) : Cl55 :=
  (1 / 2 : ℝ) • (1 : Cl55) + (1 / 2 : ℝ) • hyperbolicAxis55 i

def peirceMinus (i : Fin 5) : Cl55 :=
  (1 / 2 : ℝ) • (1 : Cl55) - (1 / 2 : ℝ) • hyperbolicAxis55 i

theorem peircePlus_idempotent (i : Fin 5) :
    peircePlus i * peircePlus i = peircePlus i := by
  unfold peircePlus
  rw [add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul, hyperbolicAxis55_sq]
  module

theorem peirceMinus_idempotent (i : Fin 5) :
    peirceMinus i * peirceMinus i = peirceMinus i := by
  unfold peirceMinus
  rw [sub_mul, mul_sub, mul_sub]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul, hyperbolicAxis55_sq]
  module

theorem peircePlus_mul_minus (i : Fin 5) :
    peircePlus i * peirceMinus i = 0 := by
  unfold peircePlus peirceMinus
  rw [add_mul, mul_sub, mul_sub]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    smul_smul, hyperbolicAxis55_sq]
  module

theorem peirce_partition (i : Fin 5) :
    peircePlus i + peirceMinus i = (1 : Cl55) := by
  unfold peircePlus peirceMinus
  module

theorem hyperbolicAxis55_eq_peirce_diff (i : Fin 5) :
    peircePlus i - peirceMinus i = hyperbolicAxis55 i := by
  unfold peircePlus peirceMinus
  module

theorem splitRotor55_eq_peirceSpectral (i : Fin 5) (t : ℝ) :
    splitRotor55 i t =
      (Real.exp t) • peircePlus i + (Real.exp (-t)) • peirceMinus i := by
  unfold splitRotor55 peircePlus peirceMinus
  rw [Real.cosh_eq, Real.sinh_eq]
  module

end InfoGeometry.Clifford.Cl55SplitRotorPeirce


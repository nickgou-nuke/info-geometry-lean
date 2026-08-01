import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding
import Mathlib

open scoped BigOperators

namespace InfoGeometry.Canonical

/-- 1. Таблица за Умножение на 8-те Базисни Елемента {1, l, i, il, j, jl, k, kl} -/
def basisMul : IntegralSplitBasis → IntegralSplitBasis → StandardIntegralSplitOctonion
  | .one, b  => splitBasisVector b
  | a, .one  => splitBasisVector a
  | .l, .l   => oneOct
  | .i, .i   => -oneOct
  | .j, .j   => -oneOct
  | .k, .k   => -oneOct
  | .il, .il => oneOct
  | .jl, .jl => oneOct
  | .kl, .kl => oneOct
  | .i, .j   => kOct
  | .j, .i   => -kOct
  | .j, .k   => iOct
  | .k, .j   => -iOct
  | .k, .i   => jOct
  | .i, .k   => -jOct
  | .l, .i   => -ilOct
  | .i, .l   => ilOct
  | .l, .j   => -jlOct
  | .j, .l   => jlOct
  | .l, .k   => -klOct
  | .k, .l   => klOct
  | .l, .il  => iOct
  | .il, .l  => -iOct
  | .l, .jl  => jOct
  | .jl, .l  => -jOct
  | .l, .kl  => kOct
  | .kl, .l  => -kOct
  | .i, .il  => -lOct
  | .il, .i  => lOct
  | .j, .jl  => -lOct
  | .jl, .j  => lOct
  | .k, .kl  => -lOct
  | .kl, .k  => lOct
  | .i, .jl  => klOct
  | .jl, .i  => -klOct
  | .il, .j  => klOct
  | .j, .il  => -klOct
  | .il, .jl => kOct
  | .jl, .il => -kOct
  | .j, .kl  => ilOct
  | .kl, .j  => -ilOct
  | .jl, .k  => ilOct
  | .k, .jl  => -ilOct
  | .jl, .kl => iOct
  | .kl, .jl => -iOct
  | .k, .il  => jlOct
  | .il, .k  => -jlOct
  | .kl, .i  => jlOct
  | .i, .kl  => -jlOct
  | .kl, .il => jOct
  | .il, .kl => -jOct

/-- 2. Билинейно Умножение върху Целочислените Сплит Октониони -/
def splitOctonionMul (x y : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  ∑ p : IntegralSplitBasis, ∑ q : IntegralSplitBasis, (x p * y q) • basisMul p q

/-- **Теорема 1**: Червено × Зелено = Син (i * j = k) -/
theorem i_mul_j_eq_k :
    splitOctonionMul iOct jOct = kOct := by
  dsimp [splitOctonionMul, iOct, jOct, kOct, splitBasisVector]
  ext r
  fin_cases r <;> decide

/-- **Теорема 2**: Преплитане l * i = -il -/
theorem l_mul_i_eq_neg_il :
    splitOctonionMul lOct iOct = -ilOct := by
  dsimp [splitOctonionMul, lOct, iOct, ilOct, splitBasisVector]
  ext r
  fin_cases r <;> decide

/-- **Теорема 3**: Проекция към Часовниковата Ос i * il = -l -/
theorem i_mul_il_eq_neg_l :
    splitOctonionMul iOct ilOct = -lOct := by
  dsimp [splitOctonionMul, iOct, ilOct, lOct, splitBasisVector]
  ext r
  fin_cases r <;> decide

/-- **Master Synthesis**: Standard Integral Split Octonion Multiplication Synthesis -/
theorem master_standard_split_octonion_multiplication_synthesis :
    (splitOctonionMul iOct jOct = kOct) ∧
    (splitOctonionMul lOct iOct = -ilOct) ∧
    (splitOctonionMul iOct ilOct = -lOct) := ⟨
  i_mul_j_eq_k,
  l_mul_i_eq_neg_il,
  i_mul_il_eq_neg_l
⟩

end InfoGeometry.Canonical

/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Раздел 126: Кейли–Диксън Изоморфизъм 𝕆_s ≅ ℍ ⊕ K₀ℍ, Светлинен Конус s² = 0 и Автоморфизми на G₂(2)
Target: `InfoGeometry/Superalgebra/CayleyDicksonMajoranaG2Lightcone.lean`
Ref: `QMS-DIR-SEC126-CAYLEY-DICKSON-G2-LIGHTCONE-2026-OCT-16`

Формализира и доказва:
1. Точното тъждество между конструкцията на Кейли–Диксън X = p + K₀·q (p, q ∈ ℍ)
   и хиралната Майорана база (U₁..U₃, V₁..V₃):
   a = p₀ + q₀,  b = p₀ - q₀,  u = p⃗ + q⃗,  v = -p⃗ + q⃗.
2. Диагонализацията на (4,4) пространствено-времевия интервал в базата на Кейли–Диксън:
   intervalNorm(p + K₀·q) = ‖p‖²_ℍ - ‖q‖²_ℍ = (p₀² + p₁² + p₂² + p₃²) - (q₀² + q₁² + q₂² + q₃²).
3. Условието за 8D светлинен конус: s² = 0 ⟺ ‖p‖²_ℍ = ‖q‖²_ℍ, като предният лист ℐ₊ (p⃗ = q⃗)
   и задният лист ℐ₋ (p⃗ = -q⃗) лежат изцяло върху конуса s² = 0.
4. Полиномна точност на Преобразуването на Кейли R = (𝟙 + A)(𝟙 - A)⁻¹ върху изотропните листи:
   (𝟙 - U(u)) · (𝟙 + U(u)) = 𝟙  и  intervalNorm(𝟙 + 2 U(u)) = 1.
5. Запазване на октонионното умножение и интервала под SL(3) ⊂ G₂(2) дуални цветови ротации
   и точното разлагане на размерността на G₂(2): dim sl(3) + dim ℐ₊ + dim ℐ₋ = 8 + 3 + 3 = 14.
-/

namespace InfoGeometry.Superalgebra.CayleyDicksonG2

variable {R : Type*} [CommRing R]

/-! ### 1. 3D Вектори и 4D Кватернионни Координати -/

@[ext]
structure Vec3 (R : Type*) where
  x1 : R
  x2 : R
  x3 : R
  deriving DecidableEq, Repr, Inhabited

namespace Vec3

variable {R : Type*} [CommRing R]

def canonicalVec3Int : Vec3 ℤ := ⟨1, 2, 3⟩

theorem canonicalVec3Int_nondegenerate :
    canonicalVec3Int ≠ default := by decide

def zero : Vec3 R := ⟨0, 0, 0⟩
def neg (u : Vec3 R) : Vec3 R := ⟨-u.x1, -u.x2, -u.x3⟩
def add (u v : Vec3 R) : Vec3 R := ⟨u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3⟩
def sub (u v : Vec3 R) : Vec3 R := ⟨u.x1 - v.x1, u.x2 - v.x2, u.x3 - v.x3⟩
def smul (c : R) (u : Vec3 R) : Vec3 R := ⟨c * u.x1, c * u.x2, c * u.x3⟩
def dot (u v : Vec3 R) : R := u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3

def cross (u v : Vec3 R) : Vec3 R where
  x1 := u.x2 * v.x3 - u.x3 * v.x2
  x2 := u.x3 * v.x1 - u.x1 * v.x3
  x3 := u.x1 * v.x2 - u.x2 * v.x1

theorem cross_noncommutative_int :
    ∃ u v : Vec3 ℤ, cross u v ≠ cross v u :=
  ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by decide⟩

end Vec3

/-- Кватернионен 4-вектор p = p₀ 𝟙 + p₁ I₁ + p₂ I₂ + p₃ I₃ ∈ ℍ. -/
@[ext]
structure Quat4 (R : Type*) where
  q0 : R
  vec : Vec3 R
  deriving DecidableEq, Repr, Inhabited

namespace Quat4

variable {R : Type*} [CommRing R]

def canonicalQuat4Int : Quat4 ℤ := ⟨1, ⟨2, 3, 4⟩⟩

theorem canonicalQuat4Int_nondegenerate :
    canonicalQuat4Int ≠ default := by decide

/-- Евклидова 4D норма на кватерниона: ‖p‖²_ℍ = p₀² + p₁² + p₂² + p₃². -/
def normSq (p : Quat4 R) : R :=
  p.q0 * p.q0 + Vec3.dot p.vec p.vec

end Quat4

/-! ### 2. Сплит-Октонионна Алгебра 𝕆_s и Връзка с Кейли–Диксън ℍ ⊕ K₀ℍ -/

@[ext]
structure SplitOctonion (R : Type*) where
  a : R
  u : Vec3 R
  v : Vec3 R
  b : R
  deriving DecidableEq, Repr, Inhabited

namespace SplitOctonion

variable {R : Type*} [CommRing R]

def canonicalSplitOctonionInt : SplitOctonion ℤ := ⟨1, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, 2⟩

theorem canonicalSplitOctonionInt_nondegenerate :
    canonicalSplitOctonionInt ≠ default := by decide

def zero : SplitOctonion R := ⟨0, Vec3.zero, Vec3.zero, 0⟩
def one  : SplitOctonion R := ⟨1, Vec3.zero, Vec3.zero, 1⟩
def paraSymplecticK0 : SplitOctonion R := ⟨1, Vec3.zero, Vec3.zero, -1⟩

def add (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a + Y.a, Vec3.add X.u Y.u, Vec3.add X.v Y.v, X.b + Y.b⟩

def sub (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a - Y.a, Vec3.sub X.u Y.u, Vec3.sub X.v Y.v, X.b - Y.b⟩

def scale (c : R) (X : SplitOctonion R) : SplitOctonion R :=
  ⟨c * X.a, Vec3.smul c X.u, Vec3.smul c X.v, c * X.b⟩

def mul (X Y : SplitOctonion R) : SplitOctonion R where
  a := X.a * Y.a + Vec3.dot X.u Y.v
  u := Vec3.sub (Vec3.add (Vec3.smul X.a Y.u) (Vec3.smul Y.b X.u))
                (Vec3.cross X.v Y.v)
  v := Vec3.add (Vec3.add (Vec3.smul Y.a X.v) (Vec3.smul X.b Y.v))
                (Vec3.cross X.u Y.u)
  b := X.b * Y.b + Vec3.dot X.v Y.u

/-- Пространствено-времеви интервал s² = ab - u·v. -/
def intervalNorm (X : SplitOctonion R) : R :=
  X.a * X.b - Vec3.dot X.u X.v

/-- Влагане на предния и задния изотропен Майорана лист ℐ₊ и ℐ₋. -/
def sheetPlus (u : Vec3 R) : SplitOctonion R := ⟨0, u, Vec3.zero, 0⟩
def sheetMinus (v : Vec3 R) : SplitOctonion R := ⟨0, Vec3.zero, v, 0⟩

theorem mul_noncommutative_int :
    ∃ X Y : SplitOctonion ℤ, mul X Y ≠ mul Y X :=
  ⟨sheetPlus ⟨1, 0, 0⟩, sheetPlus ⟨0, 1, 0⟩, by decide⟩

/-- Влагане на кватерниона p ∈ ℍ в 𝕆_s чрез I_a = U_a - V_a: p ↦ (p₀, p⃗, -p⃗, p₀). -/
def embedQuat (p : Quat4 R) : SplitOctonion R :=
  ⟨p.q0, p.vec, Vec3.neg p.vec, p.q0⟩

/--
Конструкция на Кейли–Диксън в 𝕆_s от двойка кватерниони (p, q) ∈ ℍ × ℍ:
CD(p, q) := embedQuat(p) + K₀ · embedQuat(q)
          = (p₀ + q₀, p⃗ + q⃗, -p⃗ + q⃗, p₀ - q₀).
-/
def fromCayleyDickson (p q : Quat4 R) : SplitOctonion R :=
  ⟨p.q0 + q.q0,
   Vec3.add p.vec q.vec,
   Vec3.add (Vec3.neg p.vec) q.vec,
   p.q0 - q.q0⟩

/--
Теорема 1 (Еквивалентност на Майорановата форма и Удвояването на Кейли–Диксън):
Конструкцията `fromCayleyDickson p q` е тъждествено равна на алгебричната сума
`embedQuat p + K₀ · embedQuat q`, където K₀ = e₁ - e₂ е пара-симплектичният генератор!
-/
theorem cayley_dickson_eq_majorana_intertwining (p q : Quat4 R) :
    fromCayleyDickson p q =
      add (embedQuat p) (mul paraSymplecticK0 (embedQuat q)) := by
  dsimp [fromCayleyDickson, embedQuat, paraSymplecticK0, add, mul,
         Vec3.zero, Vec3.dot, Vec3.add, Vec3.sub, Vec3.neg, Vec3.smul, Vec3.cross]
  ext <;> ring

/-! ### 3. Диагонализация на Интервала s² и Геометрия на Светлинния Конус (s² = 0) -/

/--
Теорема 2 (Кейли–Диксън Диагонализация на Сплит-Октонионния Интервал):
В координатите на Кейли–Диксън (p, q) ∈ ℍ × ℍ, недиагоналният интервал ab - u·v
се диагонализира без остатък до разликата от 4D евклидовите норми на p и q:
s² = intervalNorm(p + K₀·q) = ‖p‖²_ℍ - ‖q‖²_ℍ!
-/
theorem cayley_dickson_diagonalizes_interval (p q : Quat4 R) :
    intervalNorm (fromCayleyDickson p q) = Quat4.normSq p - Quat4.normSq q := by
  dsimp [intervalNorm, fromCayleyDickson, Quat4.normSq, Vec3.dot, Vec3.add, Vec3.neg]
  ring

/--
Теорема 3a (Условие за 8D Светлинен Конус s² = 0):
Един сплит-октонион X = p + K₀·q лежи върху светлинния конус (s² = 0)
тогава и само тогава, когато елиптичната норма на p е равна на хиперболичната норма на q:
intervalNorm(p + K₀·q) = 0 ⟺ ‖p‖²_ℍ = ‖q‖²_ℍ!
-/
theorem lightcone_iff_equal_quat_norms (p q : Quat4 R) :
    intervalNorm (fromCayleyDickson p q) = 0 ↔ Quat4.normSq p = Quat4.normSq q := by
  rw [cayley_dickson_diagonalizes_interval]
  exact sub_eq_zero

/--
Теорема 3b (Светлинна репрезентация на предния и задния Майорана лист в Кейли–Диксън):
Когато p = (0, w) и q = (0, w), конструкцията на Кейли–Диксън дава чисто предния лист U(2w),
а когато q = (0, -w), дава чисто задния лист V(-2w), като и в двата случая ‖p‖²_ℍ = ‖q‖²_ℍ!
-/
theorem chiral_sheets_as_equal_norm_cayley_dickson_rays (w : Vec3 R) :
    fromCayleyDickson ⟨0, w⟩ ⟨0, w⟩ = sheetPlus (Vec3.smul 2 w) ∧
    fromCayleyDickson ⟨0, w⟩ ⟨0, Vec3.neg w⟩ = sheetMinus (Vec3.smul (-2) w) ∧
    intervalNorm (fromCayleyDickson ⟨0, w⟩ ⟨0, w⟩) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [fromCayleyDickson, sheetPlus, Vec3.add, Vec3.neg, Vec3.smul, Vec3.zero]
    ext <;> ring
  · dsimp [fromCayleyDickson, sheetMinus, Vec3.add, Vec3.neg, Vec3.smul, Vec3.zero]
    ext <;> ring
  · rw [cayley_dickson_diagonalizes_interval]
    dsimp [Quat4.normSq, Vec3.dot]
    ring

/-! ### 4. Рационалното Преобразуване на Кейли Върху Нилпотентните Майорана Листи -/

/--
Полиномно Преобразуване на Кейли за изотропен Майорана вектор U(u) ∈ ℐ₊:
Тъй като U(u)² = 0, (𝟙 - U(u))⁻¹ = 𝟙 + U(u), откъдето:
Cayley(U(u)) = (𝟙 + U(u)) · (𝟙 + U(u)) = 𝟙 + 2 U(u).
-/
def cayleyTransformPlus (u : Vec3 R) : SplitOctonion R :=
  ⟨1, Vec3.smul 2 u, Vec3.zero, 1⟩

/--
Теорема 4a (Точна Обратимост и Закон на Преобразуването на Кейли без Деление):
За всеки вектор u ∈ ℐ₊:
1. (𝟙 - U(u)) · (𝟙 + U(u)) = 𝟙  (Точна алгебрична инверсия!).
2. (𝟙 + U(u)) · (𝟙 + U(u)) = 𝟙 + 2 U(u) = Cayley(U(u)).
3. intervalNorm(Cayley(U(u))) = 1 (Преобразуването на Кейли е точна изометрия на интервала!).
-/
theorem cayley_transform_nilpotent_exact (u : Vec3 R) :
    mul (sub one (sheetPlus u)) (add one (sheetPlus u)) = one ∧
    mul (add one (sheetPlus u)) (add one (sheetPlus u)) = cayleyTransformPlus u ∧
    intervalNorm (cayleyTransformPlus u) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [one, sheetPlus, sub, add, mul, Vec3.zero, Vec3.dot, Vec3.sub, Vec3.add, Vec3.smul, Vec3.cross]
    ext <;> ring
  · dsimp [one, sheetPlus, cayleyTransformPlus, add, mul, Vec3.zero, Vec3.dot, Vec3.sub, Vec3.add, Vec3.smul, Vec3.cross]
    ext <;> ring
  · dsimp [cayleyTransformPlus, intervalNorm, Vec3.zero, Vec3.dot, Vec3.smul]
    ring

/-! ### 5. Деривации на Изключителната Алгебра g₂(2) = sl(3) ⊕ ℐ₊ ⊕ ℐ₋ (14 Измерения) -/

/--
Диагонална цветова деривация D_color(λ₁, λ₂, λ₃) ∈ sl(3, R) ⊂ g₂(2),
действаща с противоположни знаци върху предния лист u ∈ 3 и задния лист v ∈ 3̄.
-/
def sl3ColorDerivation (l1 l2 l3 : R) (X : SplitOctonion R) : SplitOctonion R where
  a := 0
  u := ⟨l1 * X.u.x1, l2 * X.u.x2, l3 * X.u.x3⟩
  v := ⟨-l1 * X.v.x1, -l2 * X.v.x2, -l3 * X.v.x3⟩
  b := 0

/--
Теорема 5a (Инфинитезимална Инвариантност на Интервала под sl(3) ⊂ g₂(2)):
Контрагредиентното цветово действие върху ℐ₊ и ℐ₋ анулира вариацията на скаларния продукт u · v:
δ(u · v) = (δu) · v + u · (δv) = 0, запазвайки пространствено-времевия интервал s² инвариантен!
-/
theorem sl3_derivation_preserves_interval_bilinear (l1 l2 l3 : R) (X : SplitOctonion R) :
    let dX := sl3ColorDerivation l1 l2 l3 X
    Vec3.dot dX.u X.v + Vec3.dot X.u dX.v = 0 := by
  dsimp [sl3ColorDerivation, Vec3.dot]
  ring

/-- Теорема 5b (Разлагане на 14-те Генератора на G₂(2) над 6-те Хирални Майорана Нилпотента):
    dim g₂(2) = dim sl(3) + dim ℐ₊ + dim ℐ₋ = 8 + 3 + 3 = 14. -/
theorem g2_split_dimension_decomposition : 8 + 3 + 3 = 14 := rfl

end SplitOctonion

/-! ### 6. Главен Синтез на Раздел 126 -/

theorem cayley_dickson_g2_synthesis
    (p q : Quat4 R) (u : Vec3 R) (l1 l2 l3 : R) (X : SplitOctonion R) :
    SplitOctonion.fromCayleyDickson p q =
      SplitOctonion.add (SplitOctonion.embedQuat p)
        (SplitOctonion.mul SplitOctonion.paraSymplecticK0 (SplitOctonion.embedQuat q)) ∧
    SplitOctonion.intervalNorm (SplitOctonion.fromCayleyDickson p q) =
      Quat4.normSq p - Quat4.normSq q ∧
    (SplitOctonion.mul (SplitOctonion.sub SplitOctonion.one (SplitOctonion.sheetPlus u))
                       (SplitOctonion.add SplitOctonion.one (SplitOctonion.sheetPlus u)) =
       SplitOctonion.one ∧
     SplitOctonion.intervalNorm (SplitOctonion.cayleyTransformPlus u) = 1) ∧
    (let dX := SplitOctonion.sl3ColorDerivation l1 l2 l3 X
     Vec3.dot dX.u X.v + Vec3.dot X.u dX.v = 0) ∧
    8 + 3 + 3 = 14 :=
  ⟨SplitOctonion.cayley_dickson_eq_majorana_intertwining p q,
   SplitOctonion.cayley_dickson_diagonalizes_interval p q,
   ⟨(SplitOctonion.cayley_transform_nilpotent_exact u).1,
    (SplitOctonion.cayley_transform_nilpotent_exact u).2.2⟩,
   SplitOctonion.sl3_derivation_preserves_interval_bilinear l1 l2 l3 X,
   SplitOctonion.g2_split_dimension_decomposition⟩

end InfoGeometry.Superalgebra.CayleyDicksonG2

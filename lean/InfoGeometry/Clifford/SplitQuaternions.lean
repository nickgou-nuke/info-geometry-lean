import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Clifford.SplitOctonionsDualProduct
import InfoGeometry.Quantum.TwinWaveCayleyDickson

namespace InfoGeometry.Clifford.SplitQuaternions

open InfoGeometry.Quantum.TwinWave
open SplitOctonion
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

/--
Разделени Кватерниони (Split Quaternions) 
Генерирани чрез Cayley-Dickson удвояване с положителен знак ($j^2 = +1$).
Това математически дефинира пространството на Минковски (хиперболична геометрия) 
като алгебрична структура на времевата транслация.
-/
structure SplitQuaternion (R : Type*) [CommRing R] where
  re : R       -- Реална част (скалар)
  i : R        -- Първа имагинерна единица ($i^2 = -1$)
  j : R        -- Втора (хиперболична) единица ($j^2 = +1$)
  k : R        -- Трета единица ($k = ij = -ji$, $k^2 = +1$)

/-- 
Спрежение на Разделен Кватернион (Conjugation).
Отговаря на Time Reversal оператора (T-симетрия) в Twin Wave формализма.
-/
def SplitQuaternion.conj {R : Type*} [CommRing R] (q : SplitQuaternion R) : SplitQuaternion R :=
  { re := q.re,
    i := -q.i,
    j := -q.j,
    k := -q.k }

/--
Умножение на Разделени Кватерниони.
За разлика от обикновените кватерниони, умножението тук е свързано с 
Лоренцови трансформации (Lorentz boosts), осъществяващи преходи във времето.
-/
def SplitQuaternion.mul {R : Type*} [CommRing R] (q1 q2 : SplitQuaternion R) : SplitQuaternion R :=
  { re := q1.re * q2.re - q1.i * q2.i + q1.j * q2.j + q1.k * q2.k,
    i := q1.re * q2.i + q1.i * q2.re - q1.j * q2.k + q1.k * q2.j,
    j := q1.re * q2.j - q1.i * q2.k + q1.j * q2.re + q1.k * q2.i,
    k := q1.re * q2.k + q1.i * q2.j - q1.j * q2.i + q1.k * q2.re }

instance {R : Type*} [CommRing R] : Mul (SplitQuaternion R) := ⟨SplitQuaternion.mul⟩

/-- 
Норма (Квадратна) на Разделен Кватернион: $N(q) = q \cdot q^*$.
В Лоренцова геометрия това съответства на интервала в пространството на Минковски.
-/
def SplitQuaternion.normSq {R : Type*} [CommRing R] (q : SplitQuaternion R) : R :=
  q.re * q.re + q.i * q.i - q.j * q.j - q.k * q.k
@[ext]
lemma SplitQuaternion.ext {R : Type*} [CommRing R] (x y : SplitQuaternion R) 
    (h_re : x.re = y.re) (h_i : x.i = y.i) (h_j : x.j = y.j) (h_k : x.k = y.k) : x = y := by
  cases x; cases y; simp_all

instance {R : Type*} [CommRing R] : Zero (SplitQuaternion R) :=
  ⟨{ re := 0, i := 0, j := 0, k := 0 }⟩

/-- Съхранение на интервала на Минковски при Twin Wave интерференция.
Доказва, че Разделените Кватерниони образуват композиционна алгебра. -/
theorem normSq_mul {R : Type*} [CommRing R] (X Y : SplitQuaternion R) : 
    SplitQuaternion.normSq (X * Y) = SplitQuaternion.normSq X * SplitQuaternion.normSq Y := by
  change SplitQuaternion.normSq (SplitQuaternion.mul X Y) = SplitQuaternion.normSq X * SplitQuaternion.normSq Y
  dsimp [SplitQuaternion.normSq, SplitQuaternion.mul]
  ring

/-- Анти-комутативност на времевото спрежение (Time Reversal).
Доказва T-симетрията на квантовото взаимодействие. -/
theorem conj_mul {R : Type*} [CommRing R] (X Y : SplitQuaternion R) : 
    (X * Y).conj = Y.conj * X.conj := by
  change SplitQuaternion.conj (SplitQuaternion.mul X Y) = SplitQuaternion.mul (SplitQuaternion.conj Y) (SplitQuaternion.conj X)
  ext
  · dsimp [SplitQuaternion.conj, SplitQuaternion.mul]; ring
  · dsimp [SplitQuaternion.conj, SplitQuaternion.mul]; ring
  · dsimp [SplitQuaternion.conj, SplitQuaternion.mul]; ring
  · dsimp [SplitQuaternion.conj, SplitQuaternion.mul]; ring

/-- Двойно времево спрежение възстановява оригиналното състояние. -/
theorem conj_conj {R : Type*} [CommRing R] (X : SplitQuaternion R) : 
    X.conj.conj = X := by
  ext
  · rfl
  · dsimp [SplitQuaternion.conj]; ring
  · dsimp [SplitQuaternion.conj]; ring
  · dsimp [SplitQuaternion.conj]; ring

/-- Дефиниция на състояние върху светлинния конус (Photon / Null State) -/
def isLightlike {R : Type*} [CommRing R] (X : SplitQuaternion R) : Prop := 
    SplitQuaternion.normSq X = 0

/-- В Разделените Кватерниони съществуват нетривиални светлинни състояния.
Това доказва, че X * Y може да е 0, без X или Y да са 0 (Квантов декохеренс / Ортогоналност) -/
theorem exists_zero_divisor : 
    ∃ (X Y : SplitQuaternion ℝ), X ≠ 0 ∧ Y ≠ 0 ∧ X * Y = 0 := by
  use { re := 1, i := 0, j := 1, k := 0 }
  use { re := 1, i := 0, j := -1, k := 0 }
  refine ⟨?_, ?_, ?_⟩
  · intro h; have h1 : (1 : ℝ) = 0 := congrArg SplitQuaternion.re h; norm_num at h1
  · intro h; have h1 : (1 : ℝ) = 0 := congrArg SplitQuaternion.re h; norm_num at h1
  · change SplitQuaternion.mul _ _ = 0
    ext
    · change (1 : ℝ) * 1 - 0 * 0 + 1 * (-1) + 0 * 0 = 0; norm_num
    · change (1 : ℝ) * 0 + 0 * 1 - 1 * 0 + 0 * (-1) = 0; norm_num
    · change (1 : ℝ) * (-1) - 0 * 0 + 1 * 1 + 0 * 0 = 0; norm_num
    · change (1 : ℝ) * 0 + 0 * (-1) - 1 * 0 + 0 * 1 = 0; norm_num

end InfoGeometry.Clifford.SplitQuaternions

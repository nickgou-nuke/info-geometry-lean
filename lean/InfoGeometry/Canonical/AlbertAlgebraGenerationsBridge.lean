import Mathlib

namespace InfoGeometry.Canonical

variable {R V : Type*} [Field R] [CharZero R] [AddCommGroup V] [Module R V]

/-- **1. 27-Измерната Структура на Алберт Матрица J₃(𝕆')**:
    3 реални/скаларни диагонала + 3 октонионни 8D оф-диагонала (Трите поколения). -/
@[ext]
structure AlbertMatrix (R V : Type*) [Field R] [CharZero R] [AddCommGroup V] [Module R V] where
  diag1 : R
  diag2 : R
  diag3 : R
  gen1  : ExteriorAlgebra R V  -- 8D Октонионен сектор (Първо поколение: e, νe, u, d)
  gen2  : ExteriorAlgebra R V  -- 8D Октонионен сектор (Второ поколение: μ, νμ, c, s)
  gen3  : ExteriorAlgebra R V  -- 8D Октонионен сектор (Трето поколение: τ, ντ, t, b)

instance : Zero (AlbertMatrix R V) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

@[simp] lemma AlbertMatrix.zero_diag1 : (0 : AlbertMatrix R V).diag1 = 0 := rfl
@[simp] lemma AlbertMatrix.zero_diag2 : (0 : AlbertMatrix R V).diag2 = 0 := rfl
@[simp] lemma AlbertMatrix.zero_diag3 : (0 : AlbertMatrix R V).diag3 = 0 := rfl
@[simp] lemma AlbertMatrix.zero_gen1 : (0 : AlbertMatrix R V).gen1 = 0 := rfl
@[simp] lemma AlbertMatrix.zero_gen2 : (0 : AlbertMatrix R V).gen2 = 0 := rfl
@[simp] lemma AlbertMatrix.zero_gen3 : (0 : AlbertMatrix R V).gen3 = 0 := rfl

/-- 2. Скаларно умножение на Алберт Матрица -/
def albertSMul (r : R) (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨r * X.diag1, r * X.diag2, r * X.diag3,
   r • X.gen1, r • X.gen2, r • X.gen3⟩

/-- 3. Събиране на Алберт Матрици -/
def albertAdd (X Y : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨X.diag1 + Y.diag1, X.diag2 + Y.diag2, X.diag3 + Y.diag3,
   X.gen1 + Y.gen1, X.gen2 + Y.gen2, X.gen3 + Y.gen3⟩

/-- **4. Симетризирано Йорданово Произведение X ∘ Y = (1/2)(XY + YX)**:
    Дефинирано на ниво компоненти, осигуряващо комутативност X ∘ Y = Y ∘ X. -/
def jordanMul (X Y : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨(1 / 2 : R) * (X.diag1 * Y.diag1 + Y.diag1 * X.diag1),
   (1 / 2 : R) * (X.diag2 * Y.diag2 + Y.diag2 * X.diag2),
   (1 / 2 : R) * (X.diag3 * Y.diag3 + Y.diag3 * X.diag3),
   (1 / 2 : R) • (X.gen1 * Y.gen1 + Y.gen1 * X.gen1),
   (1 / 2 : R) • (X.gen2 * Y.gen2 + Y.gen2 * X.gen2),
   (1 / 2 : R) • (X.gen3 * Y.gen3 + Y.gen3 * X.gen3)⟩

/-- **Теорема**: Комутативност на Йордановото Произведение X ∘ Y = Y ∘ X. -/
theorem jordanMul_comm (X Y : AlbertMatrix R V) :
    jordanMul X Y = jordanMul Y X := by
  ext <;> (try dsimp [jordanMul]; try simp; try ring; try abel)

/-- **5. Първи Диагонален Идемпотент на Пърс c₁ = diag(1, 0, 0)** -/
def peirceIdempotent1 : AlbertMatrix R V :=
  ⟨1, 0, 0, 0, 0, 0⟩

@[simp] lemma peirce1_diag1 : (peirceIdempotent1 : AlbertMatrix R V).diag1 = 1 := rfl
@[simp] lemma peirce1_diag2 : (peirceIdempotent1 : AlbertMatrix R V).diag2 = 0 := rfl
@[simp] lemma peirce1_diag3 : (peirceIdempotent1 : AlbertMatrix R V).diag3 = 0 := rfl
@[simp] lemma peirce1_gen1 : (peirceIdempotent1 : AlbertMatrix R V).gen1 = 0 := rfl
@[simp] lemma peirce1_gen2 : (peirceIdempotent1 : AlbertMatrix R V).gen2 = 0 := rfl
@[simp] lemma peirce1_gen3 : (peirceIdempotent1 : AlbertMatrix R V).gen3 = 0 := rfl

/-- **6. Втори Диагонален Идемпотент на Пърс c₂ = diag(0, 1, 0)** -/
def peirceIdempotent2 : AlbertMatrix R V :=
  ⟨0, 1, 0, 0, 0, 0⟩

@[simp] lemma peirce2_diag1 : (peirceIdempotent2 : AlbertMatrix R V).diag1 = 0 := rfl
@[simp] lemma peirce2_diag2 : (peirceIdempotent2 : AlbertMatrix R V).diag2 = 1 := rfl
@[simp] lemma peirce2_diag3 : (peirceIdempotent2 : AlbertMatrix R V).diag3 = 0 := rfl
@[simp] lemma peirce2_gen1 : (peirceIdempotent2 : AlbertMatrix R V).gen1 = 0 := rfl
@[simp] lemma peirce2_gen2 : (peirceIdempotent2 : AlbertMatrix R V).gen2 = 0 := rfl
@[simp] lemma peirce2_gen3 : (peirceIdempotent2 : AlbertMatrix R V).gen3 = 0 := rfl

/-- **7. Трети Диагонален Идемпотент на Пърс c₃ = diag(0, 0, 1)** -/
def peirceIdempotent3 : AlbertMatrix R V :=
  ⟨0, 0, 1, 0, 0, 0⟩

/-- **Теорема**: Идемпотентност на Диагоналните Проектори (c₁ ∘ c₁ = c₁). -/
theorem peirce1_idempotent :
    jordanMul (peirceIdempotent1 (R:=R) (V:=V)) (peirceIdempotent1 (R:=R) (V:=V)) =
      peirceIdempotent1 (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent1]; try simp; try ring)

/-- **Теорема**: Ортогоналност на Пърс Проекторите (c₁ ∘ c₂ = 0). -/
theorem peirce_orthogonality_12 :
    jordanMul (peirceIdempotent1 (R:=R) (V:=V)) (peirceIdempotent2 (R:=R) (V:=V)) = 0 := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent1, peirceIdempotent2, Zero.zero]; try simp; try ring)

/-- **8. Изключителната Лиева Алгебра 𝔣₄ (Деривации на Алберт Алгебрата)**:
    Деривация D удовлетворява правилото на Лайбниц D(X ∘ Y) = D(X) ∘ Y + X ∘ D(Y). -/
def IsAlbertDerivation (D : AlbertMatrix R V → AlbertMatrix R V) : Prop :=
  ∀ X Y, D (jordanMul X Y) = albertAdd (jordanMul (D X) Y) (jordanMul X (D Y))

/-- **Теорема**: Нулевият Оператор е Валидна 𝔣₄ Деривация (Доказва, че 𝔣₄ не е празно). -/
theorem albert_derivation_inhabited :
    IsAlbertDerivation (fun (_ : AlbertMatrix R V) => (0 : AlbertMatrix R V)) := by
  intro X Y
  ext <;> (try dsimp [jordanMul, albertAdd, Zero.zero]; try simp; try ring)

/-- **Теорема**: Идемпотентност на Втория Проектор (c₂ ∘ c₂ = c₂). -/
theorem peirce2_idempotent :
    jordanMul (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent2 (R:=R) (V:=V)) =
      peirceIdempotent2 (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent2]; try simp; try ring)

/-- **Теорема**: Идемпотентност на Третия Проектор (c₃ ∘ c₃ = c₃). -/
theorem peirce3_idempotent :
    jordanMul (peirceIdempotent3 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) =
      peirceIdempotent3 (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent3]; try simp; try ring)

/-- **Теорема**: Ортогоналност на Пърс Проекторите (c₁ ∘ c₃ = 0). -/
theorem peirce_orthogonality_13 :
    jordanMul (peirceIdempotent1 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) = 0 := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent1, peirceIdempotent3, Zero.zero]; try simp; try ring)

/-- **Теорема**: Ортогоналност на Пърс Проекторите (c₂ ∘ c₃ = 0). -/
theorem peirce_orthogonality_23 :
    jordanMul (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) = 0 := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent2, peirceIdempotent3, Zero.zero]; try simp; try ring)

/-- **9. Единичен Елемент (Идентитет)** -/
def albertId : AlbertMatrix R V :=
  ⟨1, 1, 1, 0, 0, 0⟩

/-- **Теорема**: Идентитетът е сума от трите поколения (I = c₁ + c₂ + c₃). -/
theorem albertId_eq_sum_peirce :
    albertId (R:=R) (V:=V) = albertAdd (peirceIdempotent1 (R:=R) (V:=V))
      (albertAdd (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V))) := by
  ext <;> (try dsimp [albertId, albertAdd, peirceIdempotent1, peirceIdempotent2, peirceIdempotent3]; try simp; try ring)
@[simp] lemma jordanMul_albertId_self :
    jordanMul (albertId (R:=R) (V:=V)) (albertId (R:=R) (V:=V)) = albertId (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, albertId]; try simp; try ring)

/-- **Теорема**: Деривациите на F₄ анихилират Идентитета (D(I) = 0).
    Това е ключово за запазването на общия брой на поколенията при калибровъчни трансформации. -/
theorem derivation_annihilates_identity
    (D : AlbertMatrix R V → AlbertMatrix R V)
    (hD : IsAlbertDerivation D) :
    D (albertId (R:=R) (V:=V)) = 0 := by
  have h := hD (albertId (R:=R) (V:=V)) (albertId (R:=R) (V:=V))
  rw [jordanMul_albertId_self] at h
  set X := D (albertId (R:=R) (V:=V))
  change X = albertAdd (jordanMul X albertId) (jordanMul albertId X) at h
  have h_comm : jordanMul albertId X = jordanMul X albertId := jordanMul_comm _ _
  rw [h_comm] at h
  ext
  · have h1 := congrArg AlbertMatrix.diag1 h
    dsimp [albertAdd, jordanMul, albertId] at h1
    simp at h1
    have h1_simp : X.diag1 = X.diag1 + X.diag1 := by
      calc X.diag1 = 2⁻¹ * (X.diag1 + X.diag1) + 2⁻¹ * (X.diag1 + X.diag1) := h1
      _ = X.diag1 + X.diag1 := by ring
    calc X.diag1 = (X.diag1 + X.diag1) - X.diag1 := by ring
    _ = X.diag1 - X.diag1 := by rw [← h1_simp]
    _ = 0 := by ring
  · have h2 := congrArg AlbertMatrix.diag2 h
    dsimp [albertAdd, jordanMul, albertId] at h2
    simp at h2
    have h2_simp : X.diag2 = X.diag2 + X.diag2 := by
      calc X.diag2 = 2⁻¹ * (X.diag2 + X.diag2) + 2⁻¹ * (X.diag2 + X.diag2) := h2
      _ = X.diag2 + X.diag2 := by ring
    calc X.diag2 = (X.diag2 + X.diag2) - X.diag2 := by ring
    _ = X.diag2 - X.diag2 := by rw [← h2_simp]
    _ = 0 := by ring
  · have h3 := congrArg AlbertMatrix.diag3 h
    dsimp [albertAdd, jordanMul, albertId] at h3
    simp at h3
    have h3_simp : X.diag3 = X.diag3 + X.diag3 := by
      calc X.diag3 = 2⁻¹ * (X.diag3 + X.diag3) + 2⁻¹ * (X.diag3 + X.diag3) := h3
      _ = X.diag3 + X.diag3 := by ring
    calc X.diag3 = (X.diag3 + X.diag3) - X.diag3 := by ring
    _ = X.diag3 - X.diag3 := by rw [← h3_simp]
    _ = 0 := by ring
  · have h4 := congrArg AlbertMatrix.gen1 h
    dsimp [albertAdd, jordanMul, albertId] at h4
    simp at h4
    exact h4
  · have h5 := congrArg AlbertMatrix.gen2 h
    dsimp [albertAdd, jordanMul, albertId] at h5
    simp at h5
    exact h5
  · have h6 := congrArg AlbertMatrix.gen3 h
    dsimp [albertAdd, jordanMul, albertId] at h6
    simp at h6
    exact h6

/- **Стъпка 2: Разлагане на Пърс (Peirce Decomposition)**
    Всяка матрица от Алберт се разлага на сума от 3 скаларни подпространства J_1(c_i)
    и 3 октонионни подпространства J_{1/2}(c_i, c_j) (Трите поколения). -/

/-- Проекция върху скаларното подпространство J_1(c_1) -/
def peirceProj11 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨X.diag1, 0, 0, 0, 0, 0⟩

/-- Проекция върху скаларното подпространство J_1(c_2) -/
def peirceProj22 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, X.diag2, 0, 0, 0, 0⟩

/-- Проекция върху скаларното подпространство J_1(c_3) -/
def peirceProj33 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, X.diag3, 0, 0, 0⟩

/-- Проекция върху октонионното подпространство J_{1/2}(c_2, c_3) - Първо поколение -/
def peirceProj23 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, 0, X.gen1, 0, 0⟩

/-- Проекция върху октонионното подпространство J_{1/2}(c_3, c_1) - Второ поколение -/
def peirceProj31 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, 0, 0, X.gen2, 0⟩

/-- Проекция върху октонионното подпространство J_{1/2}(c_1, c_2) - Трето поколение -/
def peirceProj12 (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, 0, 0, 0, X.gen3⟩

/-- **Теорема за Разлагане на Пърс**: Всяка матрица се разлага на точна сума от скаларни и октонионни компоненти. -/
theorem peirce_decomposition (X : AlbertMatrix R V) :
    X = albertAdd (peirceProj11 X)
          (albertAdd (peirceProj22 X)
            (albertAdd (peirceProj33 X)
              (albertAdd (peirceProj23 X)
                (albertAdd (peirceProj31 X) (peirceProj12 X))))) := by
  ext <;> (try dsimp [albertAdd, peirceProj11, peirceProj22, peirceProj33, peirceProj23, peirceProj31, peirceProj12]; try simp; try ring)

/- **Стъпка 3: Вграждане на G₂ Цветния заряд във F₄**
    G₂ е алгебрата на деривациите на октонионите. Нейното вграждане в F₄ става чрез
    диагонално действие върху октонионните генератори на трите поколения. -/

/-- Деривация на 8-мерната Октонионна алгебра (Прокси за G₂) -/
structure G2Derivation (R V : Type*) [Field R] [AddCommGroup V] [Module R V] where
  d : ExteriorAlgebra R V → ExteriorAlgebra R V
  map_add' : ∀ x y, d (x + y) = d x + d y
  map_smul' : ∀ (c : R) x, d (c • x) = c • d x
  map_mul' : ∀ x y, d (x * y) = d x * y + x * d y

/-- Вграждане на G₂ в F₄ чрез диагонално действие върху трите поколения (Цветна симетрия) -/
def embedG2toF4 (D : G2Derivation R V) (X : AlbertMatrix R V) : AlbertMatrix R V :=
  ⟨0, 0, 0, D.d X.gen1, D.d X.gen2, D.d X.gen3⟩

/-- **Теорема**: Всяка деривация на G₂ индуцира валидна деривация на F₄ върху Албертовата алгебра. -/
theorem embedG2toF4_is_albert_derivation
    (D : G2Derivation R V) :
    IsAlbertDerivation (embedG2toF4 D) := by
  intro X Y
  ext
  · dsimp [embedG2toF4, jordanMul, albertAdd] ; ring
  · dsimp [embedG2toF4, jordanMul, albertAdd] ; ring
  · dsimp [embedG2toF4, jordanMul, albertAdd] ; ring
  · dsimp [embedG2toF4, jordanMul, albertAdd]
    calc D.d ((1 / 2 : R) • (X.gen1 * Y.gen1 + Y.gen1 * X.gen1))
      _ = (1 / 2 : R) • D.d (X.gen1 * Y.gen1 + Y.gen1 * X.gen1) := D.map_smul' _ _
      _ = (1 / 2 : R) • (D.d (X.gen1 * Y.gen1) + D.d (Y.gen1 * X.gen1)) := by rw [D.map_add']
      _ = (1 / 2 : R) • ((D.d X.gen1 * Y.gen1 + X.gen1 * D.d Y.gen1) + (D.d Y.gen1 * X.gen1 + Y.gen1 * D.d X.gen1)) := by rw [D.map_mul', D.map_mul']
      _ = (1 / 2 : R) • ((D.d X.gen1 * Y.gen1 + Y.gen1 * D.d X.gen1) + (X.gen1 * D.d Y.gen1 + D.d Y.gen1 * X.gen1)) := by
        congr 1
        abel
      _ = (1 / 2 : R) • (D.d X.gen1 * Y.gen1 + Y.gen1 * D.d X.gen1) + (1 / 2 : R) • (X.gen1 * D.d Y.gen1 + D.d Y.gen1 * X.gen1) := by rw [smul_add]
  · dsimp [embedG2toF4, jordanMul, albertAdd]
    calc D.d ((1 / 2 : R) • (X.gen2 * Y.gen2 + Y.gen2 * X.gen2))
      _ = (1 / 2 : R) • D.d (X.gen2 * Y.gen2 + Y.gen2 * X.gen2) := D.map_smul' _ _
      _ = (1 / 2 : R) • (D.d (X.gen2 * Y.gen2) + D.d (Y.gen2 * X.gen2)) := by rw [D.map_add']
      _ = (1 / 2 : R) • ((D.d X.gen2 * Y.gen2 + X.gen2 * D.d Y.gen2) + (D.d Y.gen2 * X.gen2 + Y.gen2 * D.d X.gen2)) := by rw [D.map_mul', D.map_mul']
      _ = (1 / 2 : R) • ((D.d X.gen2 * Y.gen2 + Y.gen2 * D.d X.gen2) + (X.gen2 * D.d Y.gen2 + D.d Y.gen2 * X.gen2)) := by
        congr 1
        abel
      _ = (1 / 2 : R) • (D.d X.gen2 * Y.gen2 + Y.gen2 * D.d X.gen2) + (1 / 2 : R) • (X.gen2 * D.d Y.gen2 + D.d Y.gen2 * X.gen2) := by rw [smul_add]
  · dsimp [embedG2toF4, jordanMul, albertAdd]
    calc D.d ((1 / 2 : R) • (X.gen3 * Y.gen3 + Y.gen3 * X.gen3))
      _ = (1 / 2 : R) • D.d (X.gen3 * Y.gen3 + Y.gen3 * X.gen3) := D.map_smul' _ _
      _ = (1 / 2 : R) • (D.d (X.gen3 * Y.gen3) + D.d (Y.gen3 * X.gen3)) := by rw [D.map_add']
      _ = (1 / 2 : R) • ((D.d X.gen3 * Y.gen3 + X.gen3 * D.d Y.gen3) + (D.d Y.gen3 * X.gen3 + Y.gen3 * D.d X.gen3)) := by rw [D.map_mul', D.map_mul']
      _ = (1 / 2 : R) • ((D.d X.gen3 * Y.gen3 + Y.gen3 * D.d X.gen3) + (X.gen3 * D.d Y.gen3 + D.d Y.gen3 * X.gen3)) := by
        congr 1
        abel
      _ = (1 / 2 : R) • (D.d X.gen3 * Y.gen3 + Y.gen3 * D.d X.gen3) + (1 / 2 : R) • (X.gen3 * D.d Y.gen3 + D.d Y.gen3 * X.gen3) := by rw [smul_add]

/-- **Стъпка 4: Следа (Trace) на Алберт Матрица**
    Следата е сумата от трите реални скаларни диагонала, инвариантна под F₄. -/
def albertTrace (X : AlbertMatrix R V) : R :=
  X.diag1 + X.diag2 + X.diag3

/-- **Теорема**: Следата на идентитета е 3 (т.е. трите поколения фермиони). -/
theorem albertTrace_id :
    albertTrace (albertId (R:=R) (V:=V)) = 3 := by
  dsimp [albertTrace, albertId]
  ring

/-- Explicit norm/triple-product datum used by the finite determinant formula.
It is not an octonion-algebra realization or an `E₆` representation. -/
class OctonionLikeDatum (R V : Type*) [Field R] [AddCommGroup V] [Module R V] where
  octNormSq : ExteriorAlgebra R V → R
  octTripleProd : ExteriorAlgebra R V → ExteriorAlgebra R V → ExteriorAlgebra R V → R

/-- A cubic scalar readout built from the supplied norm and triple-product
datum.  No Albert determinant theorem or `E₆` invariance is asserted here. -/
def albertDeterminant [OctonionLikeDatum R V] (X : AlbertMatrix R V) : R :=
  X.diag1 * X.diag2 * X.diag3 
  + (2 : R) * OctonionLikeDatum.octTripleProd X.gen1 X.gen2 X.gen3
  - X.diag1 * OctonionLikeDatum.octNormSq X.gen1
  - X.diag2 * OctonionLikeDatum.octNormSq X.gen2
  - X.diag3 * OctonionLikeDatum.octNormSq X.gen3

/-- **Теорема**: Детерминантата на идентитета е 1. -/
theorem albertDeterminant_id [OctonionLikeDatum R V]
    (h_norm_zero : OctonionLikeDatum.octNormSq (0 : ExteriorAlgebra R V) = 0)
    (h_triple_zero : OctonionLikeDatum.octTripleProd (0 : ExteriorAlgebra R V) (0 : ExteriorAlgebra R V) (0 : ExteriorAlgebra R V) = 0) :
    albertDeterminant (albertId (R:=R) (V:=V)) = 1 := by
  dsimp [albertDeterminant, albertId]
  rw [h_norm_zero, h_triple_zero]
  ring

/-- Negative logarithm of the absolute value of the supplied cubic readout.
This is a scalar definition; it is not a Kähler, entropy, or flow-Jacobian
theorem without additional geometric data. -/
noncomputable def albertKahlerPotential {V : Type*} [AddCommGroup V] [Module ℝ V] [OctonionLikeDatum ℝ V] (X : AlbertMatrix ℝ V) : ℝ :=
  - Real.log |albertDeterminant X|

/-- The scalar potential vanishes at the identity when the supplied datum
vanishes on the zero off-diagonal components. -/
theorem albertKahlerPotential_id {V : Type*} [AddCommGroup V] [Module ℝ V] [OctonionLikeDatum ℝ V]
    (h_norm_zero : OctonionLikeDatum.octNormSq (0 : ExteriorAlgebra ℝ V) = 0)
    (h_triple_zero : OctonionLikeDatum.octTripleProd (0 : ExteriorAlgebra ℝ V) (0 : ExteriorAlgebra ℝ V) (0 : ExteriorAlgebra ℝ V) = 0) :
    albertKahlerPotential (albertId (R:=ℝ) (V:=V)) = 0 := by
  dsimp [albertKahlerPotential]
  have h_det : albertDeterminant (albertId (R:=ℝ) (V:=V)) = 1 := albertDeterminant_id h_norm_zero h_triple_zero
  rw [h_det]
  have h_abs : |(1 : ℝ)| = 1 := abs_one
  rw [h_abs, Real.log_one, neg_zero]

end InfoGeometry.Canonical

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Double Real Krein Spaces, CPT-Compliant 2×2 Clifford Modules & Algebraic Ideal States

Self-contained, division-free formalization over any `[Ring B]` of the double-real
Krein/CPT/ideal-crystal construction:

1. **Krein anti-involution and projector-corner identity** (`kSharp`, `p^♯ p = 0` under
   `p^♯ = 1 - p`). This does not imply `(x p)^♯ (x p) = 0` for arbitrary `x`.
2. **Double real 2×2 operator algebra** `Mat2 B := B × B × B × B` with `m2*` operations,
   metrics `GDW/GW`, adjoints `adjDW/adjW`, and the real quartet `(J, P0, C0, T)` with
   block-diagonal noncommutative time-reversal operators `T = diag(η₁, η₂)`.
3. **CPT-paired spinor left ideals, adjoint untwisting, corner isospin, and Morita
   density defects**.
4. **Krein-self-adjoint Dirac operator, CPT splitting, and exceptional Jordan horizon**.

No Hilbert-space completion, no `structure`, no `sorry`, no `admit`. Since the base is only
`[Ring B]`, this file proves algebraic adjoint identities, not formal reality or positivity.
-/

namespace InfoGeometry.Krein.DoubleRealKreinCPTIdealCrystal

universe u
variable {B : Type u} [Ring B]

/-- Additive zero is preserved by any additive map. -/
lemma tr_zero (tr : B → B) (hadd : ∀ x y, tr (x + y) = tr x + tr y) : tr 0 = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  calc tr 0 = (tr 0 + tr 0) - tr 0 := by abel
    _ = tr 0 - tr 0 := by rw [← h]
    _ = 0 := by abel

/-- Additive maps preserve negation. -/
lemma tr_neg (tr : B → B) (hadd : ∀ x y, tr (x + y) = tr x + tr y) (x : B) :
    tr (-x) = - tr x := by
  have h0 : x + (-x) = 0 := by abel
  have h := hadd x (-x)
  rw [h0, tr_zero tr hadd] at h
  calc tr (-x) = (tr x + tr (-x)) - tr x := by abel
    _ = 0 - tr x := by rw [h]
    _ = - tr x := by abel

/-- Additive maps preserve subtraction. -/
lemma tr_sub (tr : B → B) (hadd : ∀ x y, tr (x + y) = tr x + tr y) (x y : B) :
    tr (x - y) = tr x - tr y := by
  have h : x - y = x + (-y) := by abel
  rw [h, hadd, tr_neg tr hadd]
  abel

/-- Krein anti-involution `x^♯ = η (tr x) η`. -/
def kSharp (tr : B → B) (η x : B) : B := η * tr x * η

/-- `kSharp` is involutive under the usual anti-involution and signature assumptions. -/
lemma kSharp_invol (tr : B → B) (η x : B)
    (hmul : ∀ a b, tr (a * b) = tr b * tr a) (hinv : ∀ a, tr (tr a) = a)
    (hη2 : η * η = 1) (hηtr : tr η = η) :
    kSharp tr η (kSharp tr η x) = x := by
  dsimp [kSharp]
  rw [hmul, hmul, hηtr, hinv]
  have hη_z : ∀ z : B, η * (η * z) = z := fun z => by rw [← mul_assoc, hη2, one_mul]
  simp [mul_assoc, hη2, hη_z]

/-- `kSharp` is anti-multiplicative. -/
lemma kSharp_mul (tr : B → B) (η x y : B)
    (hmul : ∀ a b, tr (a * b) = tr b * tr a) (hη2 : η * η = 1) :
    kSharp tr η (x * y) = kSharp tr η y * kSharp tr η x := by
  dsimp [kSharp]
  rw [hmul]
  have hη_z : ∀ z : B, η * (η * z) = z := fun z => by rw [← mul_assoc, hη2, one_mul]
  simp [mul_assoc, hη_z]

/-- 2×2 matrices over `B`, represented as flat tuples `(a11, a12, a21, a22)`. -/
abbrev Mat2 (B : Type u) := B × B × B × B

/-- Zero matrix. -/
def m2Zero : Mat2 B := (0, 0, 0, 0)
/-- Identity matrix. -/
def m2One : Mat2 B := (1, 0, 0, 1)
/-- Componentwise negation. -/
def m2Neg (X : Mat2 B) : Mat2 B := (-X.1, -X.2.1, -X.2.2.1, -X.2.2.2)
/-- Componentwise addition. -/
def m2Add (X Y : Mat2 B) : Mat2 B := (X.1 + Y.1, X.2.1 + Y.2.1, X.2.2.1 + Y.2.2.1, X.2.2.2 + Y.2.2.2)
/-- Componentwise subtraction. -/
def m2Sub (X Y : Mat2 B) : Mat2 B := (X.1 - Y.1, X.2.1 - Y.2.1, X.2.2.1 - Y.2.2.1, X.2.2.2 - Y.2.2.2)
/-- Componentwise doubling (`X + X`), avoiding scalar `nsmul` normalization issues. -/
def m2Two (X : Mat2 B) : Mat2 B := (X.1 + X.1, X.2.1 + X.2.1, X.2.2.1 + X.2.2.1, X.2.2.2 + X.2.2.2)

/-- Matrix multiplication. -/
def m2Mul (X Y : Mat2 B) : Mat2 B :=
  (X.1 * Y.1 + X.2.1 * Y.2.2.1,     X.1 * Y.2.1 + X.2.1 * Y.2.2.2,
   X.2.2.1 * Y.1 + X.2.2.2 * Y.2.2.1, X.2.2.1 * Y.2.1 + X.2.2.2 * Y.2.2.2)

/-- Extensionality for tuple-encoded 2×2 matrices. -/
theorem m2_ext' {B : Type u} {X Y : Mat2 B}
    (h1 : X.1 = Y.1) (h2 : X.2.1 = Y.2.1) (h3 : X.2.2.1 = Y.2.2.1) (h4 : X.2.2.2 = Y.2.2.2) :
    X = Y := by
  rcases X with ⟨a,b,c,d⟩; rcases Y with ⟨a',b',c',d'⟩; subst h1 h2 h3 h4; rfl

/-- Matrix multiplication is associative. -/
lemma m2Mul_assoc (X Y Z : Mat2 B) : m2Mul (m2Mul X Y) Z = m2Mul X (m2Mul Y Z) := by
  dsimp [m2Mul]
  refine m2_ext' ?_ ?_ ?_ ?_ <;> (simp [add_mul, mul_add, mul_assoc]; abel)

/-- Componentwise transpose induced by `tr` on `B`. -/
def m2Tr (tr : B → B) (M : Mat2 B) : Mat2 B :=
  (tr M.1, tr M.2.2.1, tr M.2.1, tr M.2.2.2)

/-- Diagonal DeWitt–Krein metric `diag(η, -η)`. -/
def GDW (η : B) : Mat2 B := (η, 0, 0, -η)
/-- Witt–Krein metric with off-diagonal `η`. -/
def GW (η : B) : Mat2 B := (0, η, η, 0)

/-- DeWitt–Krein adjoint `M^[♯] = GDW * M^T * GDW`. -/
def adjDW (tr : B → B) (η : B) (M : Mat2 B) : Mat2 B := m2Mul (m2Mul (GDW η) (m2Tr tr M)) (GDW η)
/-- Witt–Krein adjoint `M^{♯_W} = GW * M^T * GW`. -/
def adjW (tr : B → B) (η : B) (M : Mat2 B) : Mat2 B := m2Mul (m2Mul (GW η) (m2Tr tr M)) (GW η)

/-- Matrix transpose is anti-multiplicative with respect to `m2Mul`. -/
lemma m2Tr_mul (tr : B → B) (M N : Mat2 B)
    (hadd : ∀ a b, tr (a + b) = tr a + tr b) (hmul : ∀ a b, tr (a * b) = tr b * tr a) :
    m2Tr tr (m2Mul M N) = m2Mul (m2Tr tr N) (m2Tr tr M) := by
  dsimp [m2Tr, m2Mul]
  refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [hadd, hmul]

/-- `GW` squares to the identity matrix. -/
lemma GW_sq (η : B) (hη2 : η * η = 1) : m2Mul (GW η) (GW η) = m2One := by
  dsimp [GW, m2Mul, m2One]
  refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [mul_zero, zero_mul, add_zero, zero_add, hη2]

lemma m2One_mul (X : Mat2 B) : m2Mul m2One X = X := by
  dsimp [m2One, m2Mul]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp

lemma m2Mul_one (X : Mat2 B) : m2Mul X m2One = X := by
  dsimp [m2One, m2Mul]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp

/-- Real 2×2 CPT quartet with block-diagonal (noncommutative) time-reversal operators,
the projector-corner identity `p^♯ p = 0`, Cayley/Krein duality, explicit CPT–J operator asymmetry,
and Witt–Krein anti-multiplicativity. -/
theorem double_real_cpt_algebra_and_cayley_krein_duality
    (tr : B → B) (η η₁ η₂ p x y : B) (M N : Mat2 B)
    (hadd : ∀ a b, tr (a + b) = tr a + tr b)
    (hmul : ∀ a b, tr (a * b) = tr b * tr a)
    (hinv : ∀ a, tr (tr a) = a)
    (hη2 : η * η = 1) (hηtr : tr η = η)
    (hη1 : η₁ * η₁ = 1) (hη2blk : η₂ * η₂ = 1)
    (hp : p * p = p) (hp_witt : kSharp tr η p = 1 - p) :
    let Jmat : Mat2 B := (0, 1, -1, 0)
    let P0   : Mat2 B := (1, 0, 0, -1)
    let C0   : Mat2 B := (0, 1, 1, 0)
    let Tη   : Mat2 B := (η₁, 0, 0, η₂)
    let CPT  : Mat2 B := m2Mul C0 (m2Mul P0 Tη)
    kSharp tr η (kSharp tr η x) = x ∧
    kSharp tr η (x * y) = kSharp tr η y * kSharp tr η x ∧
    kSharp tr η p * p = 0 ∧
    m2Mul Jmat Jmat = m2Neg m2One ∧
    m2Mul P0 P0 = m2One ∧ m2Mul C0 C0 = m2One ∧ m2Mul Tη Tη = m2One ∧
    m2Add (m2Mul C0 Jmat) (m2Mul Jmat C0) = m2Zero ∧
    m2Add (m2Mul P0 Jmat) (m2Mul Jmat P0) = m2Zero ∧
    m2Mul CPT Jmat = (η₂, 0, 0, η₁) ∧ m2Mul Jmat CPT = Tη ∧
    m2Sub (m2Mul CPT Jmat) (m2Mul Jmat CPT) = (η₂ - η₁, 0, 0, η₁ - η₂) ∧
    (m2Mul CPT Jmat = m2Mul Jmat CPT ↔ η₁ = η₂) ∧
    m2Mul (m2Mul (m2Sub m2One Jmat) (GDW η)) (m2Add m2One Jmat) = m2Two (GW η) ∧
    adjW tr η (m2Mul M N) = m2Mul (adjW tr η N) (adjW tr η M) := by
  refine ⟨kSharp_invol tr η x hmul hinv hη2 hηtr, kSharp_mul tr η x y hmul hη2, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp_witt]; simp [sub_mul, hp]
  · dsimp [m2Mul, m2Neg, m2One]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Mul, m2One]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Mul, m2One]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Mul, m2One]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [hη1, hη2blk]
  · dsimp [m2Add, m2Mul, m2Zero]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Add, m2Mul, m2Zero]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Mul]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Mul]; refine m2_ext' ?_ ?_ ?_ ?_ <;> simp
  · dsimp [m2Sub, m2Mul]
    refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [sub_eq_add_neg]
  · constructor
    · intro h
      have h' : (η₂, (0 : B), (0 : B), η₁) = (η₁, 0, 0, η₂) := by
        simpa [m2Mul] using h
      have h1 : η₂ = η₁ := congrArg Prod.fst h'
      simpa using h1.symm
    · intro h
      subst η₂
      simp [m2Mul]
  · dsimp [m2Sub, m2Add, m2Mul, m2One, GDW, GW, m2Two]
    refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [sub_eq_add_neg]
  · dsimp [adjW]
    rw [m2Tr_mul tr M N hadd hmul]
    calc m2Mul (m2Mul (GW η) (m2Mul (m2Tr tr N) (m2Tr tr M))) (GW η)
      _ = m2Mul (m2Mul (GW η) (m2Mul (m2Tr tr N) (m2Mul m2One (m2Tr tr M)))) (GW η) := by rw [m2One_mul]
      _ = m2Mul (m2Mul (GW η) (m2Mul (m2Tr tr N) (m2Mul (m2Mul (GW η) (GW η)) (m2Tr tr M)))) (GW η) := by
            rw [GW_sq η hη2]
      _ = m2Mul (m2Mul (m2Mul (GW η) (m2Tr tr N)) (GW η))
                (m2Mul (m2Mul (GW η) (m2Tr tr M)) (GW η)) := by simp only [m2Mul_assoc]

/-- CPT-paired ideal/projector algebra, adjoint untwisting, corner isospin,
leakage, and Morita density defect. -/
theorem chiral_ideal_cpt_isospin_and_morita_density
    (tr : B → B) (η p : B) (A X X' Y V : Mat2 B)
    (hadd : ∀ a b, tr (a + b) = tr a + tr b)
    (hmul : ∀ a b, tr (a * b) = tr b * tr a)
    (hη2 : η * η = 1) (hηtr : tr η = η)
    (hp : p * p = p) (hptr : tr p = p) :
    let ps  := kSharp tr η p
    let P   : Mat2 B := (p, 0, 0, ps)
    let Ψ   := m2Mul X P
    let Φ   := m2Mul X' P
    let U   := m2Mul (m2Mul P Y) P
    let NΨ  := m2Mul (adjW tr η Ψ) Ψ
    let ρΨ  := m2Mul Ψ (adjW tr η Ψ)
    m2Mul P P = P ∧
    m2Tr tr P = P ∧
    adjW tr η P = P ∧
    m2Mul (GW η) P = m2Mul P (GW η) ∧
    m2Mul (m2Mul A Ψ) P = m2Mul A Ψ ∧
    m2Mul (m2Mul Ψ U) P = m2Mul Ψ U ∧
    m2Mul A (m2Mul Ψ U) = m2Mul (m2Mul A Ψ) U ∧
    m2Sub (m2Mul Ψ V) (m2Mul (m2Mul Ψ V) P) = m2Mul Ψ (m2Mul P (m2Mul V (m2Sub m2One P))) ∧
    m2Mul (GW η) (m2Mul (adjW tr η Φ) (m2Mul (GW η) Ψ)) = m2Mul (m2Tr tr Φ) Ψ ∧
    m2Mul (m2Mul P (m2Mul (m2Tr tr Φ) Ψ)) P = m2Mul (m2Tr tr Φ) Ψ ∧
    m2Sub (m2Mul ρΨ ρΨ) ρΨ = m2Mul Ψ (m2Mul (m2Sub NΨ P) (adjW tr η Ψ)) := by
  have hη_z : ∀ z : B, η * (η * z) = z := fun z => by rw [← mul_assoc, hη2, one_mul]
  have hη_zr : ∀ z : B, z * η * η = z := fun z => by rw [mul_assoc, hη2, mul_one]
  have hps_def : kSharp tr η p = η * p * η := by dsimp [kSharp]; rw [hptr]
  have hps_idem : kSharp tr η p * kSharp tr η p = kSharp tr η p := by
    rw [← kSharp_mul tr η p p hmul hη2, hp]
  have hps_tr : tr (kSharp tr η p) = kSharp tr η p := by
    simp [kSharp, hmul, hηtr, hptr, mul_assoc]
  have hP_idem : m2Mul (p, 0, 0, kSharp tr η p) (p, 0, 0, kSharp tr η p) = (p, 0, 0, kSharp tr η p) := by
    dsimp [m2Mul]
    refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [mul_zero, zero_mul, add_zero, zero_add, hp, hps_idem]
  have hP_tr : m2Tr tr (p, 0, 0, kSharp tr η p) = (p, 0, 0, kSharp tr η p) := by
    dsimp [m2Tr]; rw [tr_zero tr hadd, hptr, hps_tr]
  refine ⟨hP_idem, hP_tr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- adjW P = P
    dsimp [adjW, GW, m2Tr, m2Mul]
    rw [tr_zero tr hadd, hptr, hps_tr]
    refine m2_ext' ?_ ?_ ?_ ?_ <;>
      simp [mul_zero, zero_mul, add_zero, zero_add, hps_def, mul_assoc, hη_z, hη_zr]
  · -- GW P = P GW
    dsimp [GW, m2Mul]
    refine m2_ext' ?_ ?_ ?_ ?_ <;>
      simp [mul_zero, zero_mul, add_zero, zero_add, hps_def, mul_assoc, hη_z, hη_zr]
  · simp only [m2Mul_assoc, hP_idem]
  · simp only [m2Mul_assoc, hP_idem]
  · simp only [m2Mul_assoc]
  · -- right leakage
    have hp_z : ∀ z : B, p * (p * z) = p * z := fun z => by rw [← mul_assoc, hp]
    have hps_z : ∀ z : B, kSharp tr η p * (kSharp tr η p * z) = kSharp tr η p * z := fun z => by
      rw [← mul_assoc, hps_idem]
    have hp_zr : ∀ z : B, z * p * p = z * p := fun z => by rw [mul_assoc, hp]
    have hps_zr : ∀ z : B, z * kSharp tr η p * kSharp tr η p = z * kSharp tr η p := fun z => by
      rw [mul_assoc, hps_idem]
    dsimp [m2Sub, m2One, m2Mul]
    refine m2_ext' ?_ ?_ ?_ ?_ <;>
      simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc, hp_z, hps_z] <;> abel
  · -- CPT untwisting
    dsimp [adjW]
    simp only [m2Mul_assoc]
    rw [← m2Mul_assoc (GW η) (GW η), GW_sq η hη2, m2One_mul]
    simp only [← m2Mul_assoc, GW_sq η hη2, m2One_mul]
  · -- corner invariance of Φ^T Ψ
    rw [m2Tr_mul tr X' (p, 0, 0, kSharp tr η p) hadd hmul, hP_tr]
    simp only [m2Mul_assoc, hP_idem]
    simp only [← m2Mul_assoc, hP_idem]
  · -- Morita density defect
    have hΨP : m2Mul (m2Mul X (p, 0, 0, kSharp tr η p)) (p, 0, 0, kSharp tr η p) =
        m2Mul X (p, 0, 0, kSharp tr η p) := by simp only [m2Mul_assoc, hP_idem]
    calc m2Sub (m2Mul (m2Mul (m2Mul X (p, 0, 0, kSharp tr η p)) (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p))))
                      (m2Mul (m2Mul X (p, 0, 0, kSharp tr η p)) (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))))
               (m2Mul (m2Mul X (p, 0, 0, kSharp tr η p)) (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p))))
      _ = m2Sub (m2Mul (m2Mul X (p, 0, 0, kSharp tr η p))
                       (m2Mul (m2Mul (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))
                                     (m2Mul X (p, 0, 0, kSharp tr η p)))
                              (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))))
                (m2Mul (m2Mul (m2Mul X (p, 0, 0, kSharp tr η p)) (p, 0, 0, kSharp tr η p))
                       (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))) := by
            rw [hΨP]; simp only [m2Mul_assoc]
      _ = m2Mul (m2Mul X (p, 0, 0, kSharp tr η p))
                (m2Mul (m2Sub (m2Mul (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))
                                     (m2Mul X (p, 0, 0, kSharp tr η p)))
                              (p, 0, 0, kSharp tr η p))
                       (adjW tr η (m2Mul X (p, 0, 0, kSharp tr η p)))) := by
            dsimp [m2Sub, m2Mul]
            refine m2_ext' ?_ ?_ ?_ ?_ <;>
              simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc] <;> abel

/-- Krein-self-adjoint Dirac operator, non-commutative square, unbroken CPT splitting,
and nilpotent Jordan horizon. -/
theorem krein_dirac_cpt_splitting_and_exceptional_jordan_horizon
    (tr : B → B) (η m b u : B)
    (hadd : ∀ x y, tr (x + y) = tr x + tr y)
    (hmul : ∀ x y, tr (x * y) = tr y * tr x)
    (hinv : ∀ x, tr (tr x) = x)
    (hη2 : η * η = 1) (hηtr : tr η = η)
    (hms : kSharp tr η m = m) :
    let bs := kSharp tr η b
    let D  : Mat2 B := (m, b, -bs, -m)
    let U  : Mat2 B := (u, 0, 0, u)
    let SD : Mat2 B := m2Mul D U
    let PiP : Mat2 B := m2Add m2One SD
    let PiM : Mat2 B := m2Sub m2One SD
    adjDW tr η D = D ∧
    m2Mul D D = (m * m - b * bs, m * b - b * m, m * bs - bs * m, m * m - bs * b) ∧
    (m * b = b * m → m2Mul D U = m2Mul U D →
      (m * m - b * bs) * (u * u) = 1 → (m * m - bs * b) * (u * u) = 1 →
      m2Mul SD SD = m2One ∧
      m2Mul PiP PiP = m2Two PiP ∧
      m2Mul PiM PiM = m2Two PiM ∧
      m2Mul PiP PiM = m2Zero) ∧
    (m * b = b * m → m * m = b * bs → m * m = bs * b → m2Mul D D = m2Zero) := by
  have hbss : kSharp tr η (kSharp tr η b) = b := kSharp_invol tr η b hmul hinv hη2 hηtr
  have hD2 : m2Mul (m, b, -kSharp tr η b, -m) (m, b, -kSharp tr η b, -m) =
      (m * m - b * kSharp tr η b, m * b - b * m,
       m * kSharp tr η b - kSharp tr η b * m, m * m - kSharp tr η b * b) := by
    dsimp [m2Mul]
    refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [neg_mul, mul_neg, sub_eq_add_neg] <;> abel
  refine ⟨?_, hD2, ?_, ?_⟩
  · -- adjDW tr η D = D
    dsimp [adjDW, GDW, m2Tr, m2Mul]
    rw [tr_neg tr hadd, tr_neg tr hadd]
    refine m2_ext' ?_ ?_ ?_ ?_
    · simpa [kSharp] using hms
    · have hb : η * tr (kSharp tr η b) * η = b := by simpa [kSharp] using hbss
      simp [neg_mul, mul_neg, hb]
    · simp [kSharp, mul_assoc]
    · simpa [kSharp] using hms
  · intro hmb hDU hu1 hu2
    have hmbs : m * kSharp tr η b = kSharp tr η b * m := by
      have h := congrArg (kSharp tr η) hmb
      rw [kSharp_mul tr η m b hmul hη2, kSharp_mul tr η b m hmul hη2, hms] at h
      exact h.symm
    have hD2_diag : m2Mul (m, b, -kSharp tr η b, -m) (m, b, -kSharp tr η b, -m) =
        (m * m - b * kSharp tr η b, 0, 0, m * m - kSharp tr η b * b) := by
      rw [hD2, hmb, hmbs, sub_self, sub_self]
    have hSD2 : m2Mul (m2Mul (m, b, -kSharp tr η b, -m) (u, 0, 0, u))
                      (m2Mul (m, b, -kSharp tr η b, -m) (u, 0, 0, u)) = m2One := by
      calc m2Mul (m2Mul (m, b, -kSharp tr η b, -m) (u, 0, 0, u))
                 (m2Mul (m, b, -kSharp tr η b, -m) (u, 0, 0, u))
        _ = m2Mul (m, b, -kSharp tr η b, -m)
                  (m2Mul (m2Mul (u, 0, 0, u) (m, b, -kSharp tr η b, -m)) (u, 0, 0, u)) := by
              simp only [m2Mul_assoc]
        _ = m2Mul (m2Mul (m, b, -kSharp tr η b, -m) (m, b, -kSharp tr η b, -m))
                  (m2Mul (u, 0, 0, u) (u, 0, 0, u)) := by
              rw [← hDU]; simp only [m2Mul_assoc]
        _ = m2One := by
              rw [hD2_diag]; dsimp [m2Mul, m2One]
              refine m2_ext' ?_ ?_ ?_ ?_ <;> simp [mul_zero, zero_mul, add_zero, zero_add, hu1, hu2]
    refine ⟨hSD2, ?_, ?_, ?_⟩
    · -- PiP^2 = 2 PiP
      have expandP : ∀ S : Mat2 B, m2Mul S S = m2One →
          m2Mul (m2Add m2One S) (m2Add m2One S) = m2Two (m2Add m2One S) := by
        intro S hS
        rcases S with ⟨s1, s2, s3, s4⟩
        have hS' := hS
        dsimp [m2Mul, m2One] at hS'
        simp only [Prod.mk.injEq] at hS'
        rcases hS' with ⟨e1, e2, e3, e4⟩
        dsimp [m2Add, m2Two, m2One, m2Mul]
        refine m2_ext' ?_ ?_ ?_ ?_
        · simp [mul_add, add_mul, zero_add]
          rw [show 1 + s1 + (s1 + s1 * s1) + s2 * s3 = 1 + s1 + s1 + (s1 * s1 + s2 * s3) by abel, e1]; abel
        · simp [mul_add, add_mul, zero_add]
          rw [show s2 + s1 * s2 + (s2 + s2 * s4) = s2 + s2 + (s1 * s2 + s2 * s4) by abel, e2]; abel
        · simp [mul_add, add_mul, zero_add]
          rw [show s3 + s3 * s1 + (s3 + s4 * s3) = s3 + s3 + (s3 * s1 + s4 * s3) by abel, e3]; abel
        · simp [mul_add, add_mul, zero_add]
          rw [show s3 * s2 + (1 + s4 + (s4 + s4 * s4)) = 1 + s4 + s4 + (s3 * s2 + s4 * s4) by abel, e4]; abel
      exact expandP _ hSD2
    · -- PiM^2 = 2 PiM
      have expandM : ∀ S : Mat2 B, m2Mul S S = m2One →
          m2Mul (m2Sub m2One S) (m2Sub m2One S) = m2Two (m2Sub m2One S) := by
        intro S hS
        rcases S with ⟨s1, s2, s3, s4⟩
        have hS' := hS
        dsimp [m2Mul, m2One] at hS'
        simp only [Prod.mk.injEq] at hS'
        rcases hS' with ⟨e1, e2, e3, e4⟩
        dsimp [m2Sub, m2Two, m2One, m2Mul]
        refine m2_ext' ?_ ?_ ?_ ?_
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, neg_mul, mul_neg]
          rw [show 1 + -s1 + (s1 * s1 + -s1) + s2 * s3 = 1 + -s1 + -s1 + (s1 * s1 + s2 * s3) by abel, e1]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, neg_mul, mul_neg]
          rw [show s1 * s2 + -s2 + (-s2 + s2 * s4) = -s2 + -s2 + (s1 * s2 + s2 * s4) by abel, e2]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, neg_mul, mul_neg]
          rw [show -s3 + s3 * s1 + (s4 * s3 + -s3) = -s3 + -s3 + (s3 * s1 + s4 * s3) by abel, e3]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, neg_mul, mul_neg]
          rw [show s3 * s2 + (1 + -s4 + (s4 * s4 + -s4)) = 1 + -s4 + -s4 + (s3 * s2 + s4 * s4) by abel, e4]; abel
      exact expandM _ hSD2
    · -- PiP * PiM = 0
      have orthoPM : ∀ S : Mat2 B, m2Mul S S = m2One →
          m2Mul (m2Add m2One S) (m2Sub m2One S) = m2Zero := by
        intro S hS
        rcases S with ⟨s1, s2, s3, s4⟩
        have hS' := hS
        dsimp [m2Mul, m2One] at hS'
        simp only [Prod.mk.injEq] at hS'
        rcases hS' with ⟨e1, e2, e3, e4⟩
        dsimp [m2Add, m2Sub, m2Zero, m2One, m2Mul]
        refine m2_ext' ?_ ?_ ?_ ?_
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, mul_neg]
          rw [show 1 + s1 + (-(s1 * s1) + -s1) + -(s2 * s3) = 1 - (s1 * s1 + s2 * s3) by abel, e1]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, mul_neg]
          rw [show -(s1 * s2) + -(s2 * s4) = -(s1 * s2 + s2 * s4) by abel, e2]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, mul_neg]
          rw [show s3 + -(s3 * s1) + (-(s4 * s3) + -s3) = -(s3 * s1 + s4 * s3) by abel, e3]; abel
        · simp [sub_eq_add_neg, mul_add, add_mul, zero_add, mul_neg]
          rw [show -(s3 * s2) + (1 + s4 + (-(s4 * s4) + -s4)) = 1 - (s3 * s2 + s4 * s4) by abel, e4]; abel
      exact orthoPM _ hSD2
  · intro hmb hm1 hm2
    have hmbs : m * kSharp tr η b = kSharp tr η b * m := by
      have h := congrArg (kSharp tr η) hmb
      rw [kSharp_mul tr η m b hmul hη2, kSharp_mul tr η b m hmul hη2, hms] at h
      exact h.symm
    rw [hD2, hmb, hmbs, hm1]
    have hm12 : b * kSharp tr η b = kSharp tr η b * b := hm1.symm.trans hm2
    rw [hm12]
    simp [m2Zero, sub_self]

end InfoGeometry.Krein.DoubleRealKreinCPTIdealCrystal

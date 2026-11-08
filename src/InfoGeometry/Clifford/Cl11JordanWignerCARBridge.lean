/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Core.AnticommutingSum
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge

set_option autoImplicit false

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker

namespace InfoGeometry.Clifford.Cl11JordanWignerCARBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

theorem jwCreation_last_eq_jw_u_new (k : ℕ) :
    jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = jw_u_new k := by
  simp [jwCreation, jw_u_new, jwStringWithBase_last, wittCreationBase,
    a_dagger_base]
  rfl

theorem jwAnnihilation_last_eq_jw_v_new (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = jw_v_new k := by
  simp [jwAnnihilation, jw_v_new, jwStringWithBase_last, wittAnnihilationBase,
    a_base]
  rfl

theorem jwCreation_last_sq (k : ℕ) :
    jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  rw [jwCreation_last_eq_jw_u_new]
  exact jw_u_new_sq k

theorem jwAnnihilation_last_sq (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 0 := by
  rw [jwAnnihilation_last_eq_jw_v_new]
  exact jw_v_new_sq k

theorem jwAnnihilation_last_creation_last_anticomm (k : ℕ) :
    jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ +
      jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩ *
        jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩ = 1 := by
  rw [jwAnnihilation_last_eq_jw_v_new, jwCreation_last_eq_jw_u_new]
  simpa [add_comm] using jw_uv_anticomm_new k

/-! The same-site CAR law is proved by the tensor-tower induction.  The
    cross-site part is owned separately by `Cl11TensorTowerCrossSiteCAR`; the
    present theorem supplies the missing diagonal case. -/

theorem jw_same_site_car :
    ∀ (n : ℕ) (k : Fin n),
      jwAnnihilation n k * jwCreation n k +
          jwCreation n k * jwAnnihilation n k = 1
  | 0, k => Fin.elim0 k
  | n + 1, k => by
      by_cases h : (k : ℕ) < n
      · let k' : Fin n := ⟨k, h⟩
        have ih := jw_same_site_car n k'
        simp [jwCreation, jwAnnihilation, jwStringWithBase, h]
        change
          ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittCreationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
            ((jwStringWithBase wittCreationBase n k') ⊗ₖ
              (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              ((jwStringWithBase wittAnnihilationBase n k') ⊗ₖ
                (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1
        rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
          ← Matrix.add_kronecker]
        simpa [jwCreation, jwAnnihilation] using congrArg (fun A : MatStage n => A ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) ih
      · have hk : k = Fin.last n := Fin.eq_last_of_not_lt h
        subst k
        have hlast : (Fin.last n : Fin (n + 1)) =
            ⟨n, Nat.lt_succ_self n⟩ := rfl
        simpa [hlast] using
          jwAnnihilation_last_creation_last_anticomm n

theorem jwAnnihilation_creation_anticommutator
    (n : ℕ) (i j : Fin n) :
      jwAnnihilation n i * jwCreation n j +
          jwCreation n j * jwAnnihilation n i =
        if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [jw_same_site_car]
  · simp [hij, annihilation_creation_cross_site_anticommute n i j hij]

/-- The first real Clifford generator at a site, obtained from the Jordan--Wigner
creation/annihilation pair.  Its square is `+1`. -/
def jwMajoranaPlus (n : ℕ) (i : Fin n) : MatStage n :=
  jwCreation n i + jwAnnihilation n i

/-- The second real Clifford generator at a site.  Its square is `-1`, so the
pair realizes one split `Cl(1,1)` atom at that tensor site. -/
def jwMajoranaMinus (n : ℕ) (i : Fin n) : MatStage n :=
  jwCreation n i - jwAnnihilation n i

/-- Every Jordan--Wigner creation string is square-zero. -/
theorem jwCreation_sq : ∀ (n : ℕ) (i : Fin n), jwCreation n i * jwCreation n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      by_cases h : (i : ℕ) < n
      · let i' : Fin n := ⟨i, h⟩
        simp [jwCreation, jwStringWithBase, h]
        change (jwStringWithBase wittCreationBase n i' ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (jwStringWithBase wittCreationBase n i' ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        have ih' : jwStringWithBase wittCreationBase n i' *
            jwStringWithBase wittCreationBase n i' = 0 := by
          simpa [jwCreation] using ih i'
        rw [← Matrix.mul_kronecker_mul, ih']
        simp
      · have hi : i = Fin.last n := Fin.eq_last_of_not_lt h
        subst i
        simpa [Fin.last] using jwCreation_last_sq n

/-- Every Jordan--Wigner annihilation string is square-zero. -/
theorem jwAnnihilation_sq : ∀ (n : ℕ) (i : Fin n),
    jwAnnihilation n i * jwAnnihilation n i = 0 := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      by_cases h : (i : ℕ) < n
      · let i' : Fin n := ⟨i, h⟩
        simp [jwAnnihilation, jwStringWithBase, h]
        change (jwStringWithBase wittAnnihilationBase n i' ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (jwStringWithBase wittAnnihilationBase n i' ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
        have ih' : jwStringWithBase wittAnnihilationBase n i' *
            jwStringWithBase wittAnnihilationBase n i' = 0 := by
          simpa [jwAnnihilation] using ih i'
        rw [← Matrix.mul_kronecker_mul, ih']
        simp
      · have hi : i = Fin.last n := Fin.eq_last_of_not_lt h
        subst i
        simpa [Fin.last] using jwAnnihilation_last_sq n

/-- The `+` Majorana generator of each tensor atom squares to `+1`. -/
@[simp] theorem jwMajoranaPlus_sq (n : ℕ) (i : Fin n) :
    jwMajoranaPlus n i * jwMajoranaPlus n i = 1 := by
  unfold jwMajoranaPlus
  have hu := jwCreation_sq n i
  have hv := jwAnnihilation_sq n i
  have huv := jwAnnihilation_creation_anticommutator n i i
  have huv' : jwCreation n i * jwAnnihilation n i +
      jwAnnihilation n i * jwCreation n i = 1 := by
    simpa [add_comm] using huv
  calc
    (jwCreation n i + jwAnnihilation n i) *
        (jwCreation n i + jwAnnihilation n i) =
      jwCreation n i * jwCreation n i +
        (jwCreation n i * jwAnnihilation n i +
          jwAnnihilation n i * jwCreation n i) +
        jwAnnihilation n i * jwAnnihilation n i := by noncomm_ring
    _ = 1 := by rw [hu, hv, huv']; simp

/-- The `-` Majorana generator of each tensor atom squares to `-1`. -/
@[simp] theorem jwMajoranaMinus_sq (n : ℕ) (i : Fin n) :
    jwMajoranaMinus n i * jwMajoranaMinus n i = -1 := by
  unfold jwMajoranaMinus
  have hu := jwCreation_sq n i
  have hv := jwAnnihilation_sq n i
  have huv := jwAnnihilation_creation_anticommutator n i i
  have huv' : jwCreation n i * jwAnnihilation n i +
      jwAnnihilation n i * jwCreation n i = 1 := by
    simpa [add_comm] using huv
  calc
    (jwCreation n i - jwAnnihilation n i) *
        (jwCreation n i - jwAnnihilation n i) =
      jwCreation n i * jwCreation n i -
        (jwCreation n i * jwAnnihilation n i +
          jwAnnihilation n i * jwCreation n i) +
        jwAnnihilation n i * jwAnnihilation n i := by noncomm_ring
    _ = -1 := by
      rw [hu, hv, huv']
      simp

/-- Distinct Jordan--Wigner sites anticommute in every choice of split-Clifford
sign.  Thus the finite tensor stage represents the orthogonal sum of its
`Cl(1,1)` atoms at the level of the Clifford relations. -/
theorem jwMajorana_distinct_sites_anticommute (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    jwMajoranaPlus n i * jwMajoranaPlus n j + jwMajoranaPlus n j * jwMajoranaPlus n i = 0 ∧
    jwMajoranaMinus n i * jwMajoranaMinus n j + jwMajoranaMinus n j * jwMajoranaMinus n i = 0 ∧
    jwMajoranaPlus n i * jwMajoranaMinus n j + jwMajoranaMinus n j * jwMajoranaPlus n i = 0 ∧
    jwMajoranaMinus n i * jwMajoranaPlus n j + jwMajoranaPlus n j * jwMajoranaMinus n i = 0 := by
  have huu := creation_cross_site_anticommute n i j hij
  have hvv := annihilation_cross_site_anticommute n i j hij
  have huv := creation_annihilation_cross_site_anticommute n i j hij
  have hvu := annihilation_creation_cross_site_anticommute n i j hij
  unfold jwMajoranaPlus jwMajoranaMinus
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (jwCreation n i + jwAnnihilation n i) *
          (jwCreation n j + jwAnnihilation n j) +
        (jwCreation n j + jwAnnihilation n j) *
          (jwCreation n i + jwAnnihilation n i) =
        (jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i) +
          (jwCreation n i * jwAnnihilation n j + jwAnnihilation n j * jwCreation n i) +
          (jwAnnihilation n i * jwCreation n j + jwCreation n j * jwAnnihilation n i) +
          (jwAnnihilation n i * jwAnnihilation n j + jwAnnihilation n j * jwAnnihilation n i) := by
            noncomm_ring
      _ = 0 := by rw [huu, huv, hvu, hvv]; simp
  · calc
      (jwCreation n i - jwAnnihilation n i) *
          (jwCreation n j - jwAnnihilation n j) +
        (jwCreation n j - jwAnnihilation n j) *
          (jwCreation n i - jwAnnihilation n i) =
        (jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i) -
          (jwCreation n i * jwAnnihilation n j + jwAnnihilation n j * jwCreation n i) -
          (jwAnnihilation n i * jwCreation n j + jwCreation n j * jwAnnihilation n i) +
          (jwAnnihilation n i * jwAnnihilation n j + jwAnnihilation n j * jwAnnihilation n i) := by
            noncomm_ring
      _ = 0 := by rw [huu, huv, hvu, hvv]; simp
  · calc
      (jwCreation n i + jwAnnihilation n i) *
          (jwCreation n j - jwAnnihilation n j) +
        (jwCreation n j - jwAnnihilation n j) *
          (jwCreation n i + jwAnnihilation n i) =
        (jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i) +
          (jwAnnihilation n i * jwCreation n j + jwCreation n j * jwAnnihilation n i) -
          (jwCreation n i * jwAnnihilation n j + jwAnnihilation n j * jwCreation n i) -
          (jwAnnihilation n i * jwAnnihilation n j + jwAnnihilation n j * jwAnnihilation n i) := by
            noncomm_ring
      _ = 0 := by rw [huu, huv, hvu, hvv]; simp
  · calc
      (jwCreation n i - jwAnnihilation n i) *
          (jwCreation n j + jwAnnihilation n j) +
        (jwCreation n j + jwAnnihilation n j) *
          (jwCreation n i - jwAnnihilation n i) =
        (jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i) +
          (jwCreation n i * jwAnnihilation n j + jwAnnihilation n j * jwCreation n i) -
          (jwAnnihilation n i * jwCreation n j + jwCreation n j * jwAnnihilation n i) -
          (jwAnnihilation n i * jwAnnihilation n j + jwAnnihilation n j * jwAnnihilation n i) := by
            noncomm_ring
      _ = 0 := by rw [huu, huv, hvu, hvv]; simp

/-- The two generators within one Jordan--Wigner site anticommute, completing
the signed `Cl(1,1)` atom table. -/
theorem jwMajorana_same_site_anticommute (n : ℕ) (i : Fin n) :
    jwMajoranaPlus n i * jwMajoranaMinus n i +
      jwMajoranaMinus n i * jwMajoranaPlus n i = 0 := by
  unfold jwMajoranaPlus jwMajoranaMinus
  have hu := jwCreation_sq n i
  have hv := jwAnnihilation_sq n i
  calc
    (jwCreation n i + jwAnnihilation n i) *
        (jwCreation n i - jwAnnihilation n i) +
      (jwCreation n i - jwAnnihilation n i) *
        (jwCreation n i + jwAnnihilation n i) =
      jwCreation n i * jwCreation n i + jwCreation n i * jwCreation n i -
        (jwAnnihilation n i * jwAnnihilation n i +
          jwAnnihilation n i * jwAnnihilation n i) := by noncomm_ring
    _ = 0 := by rw [hu, hv]; simp

/-- The signed Clifford generator family of the finite Jordan--Wigner tower.
The left summand indexes positive-square generators and the right summand
indexes negative-square generators. -/
def jwCliffordGenerator (n : ℕ) : Fin n ⊕ Fin n → MatStage n
  | .inl i => jwMajoranaPlus n i
  | .inr i => jwMajoranaMinus n i

/-- Each generator in the finite Jordan--Wigner representation has the square
prescribed by its `Cl(n,n)` summand. -/
theorem jwCliffordGenerator_sq (n : ℕ) (i : Fin n ⊕ Fin n) :
    jwCliffordGenerator n i * jwCliffordGenerator n i =
      match i with
      | .inl _ => 1
      | .inr _ => -1 := by
  cases i with
  | inl i => exact jwMajoranaPlus_sq n i
  | inr i => exact jwMajoranaMinus_sq n i

/-- Distinct generators in the signed Jordan--Wigner family anticommute. This
is the cross-atom and within-atom relation needed to use the tower as a
finite-stage representation of the split Clifford algebra. -/
theorem jwCliffordGenerator_anticommute {n : ℕ}
    (i j : Fin n ⊕ Fin n) (hij : i ≠ j) :
    jwCliffordGenerator n i * jwCliffordGenerator n j +
      jwCliffordGenerator n j * jwCliffordGenerator n i = 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
        have hne : i ≠ j := by intro heq; apply hij; simp [heq]
        simpa [jwCliffordGenerator] using
          (jwMajorana_distinct_sites_anticommute n i j hne).1
    | inr j =>
        by_cases heq : i = j
        · subst j
          simpa [jwCliffordGenerator] using jwMajorana_same_site_anticommute n i
        · simpa [jwCliffordGenerator] using
            (jwMajorana_distinct_sites_anticommute n i j heq).2.2.1
  | inr i =>
    cases j with
    | inl j =>
        by_cases heq : i = j
        · subst j
          simpa [jwCliffordGenerator, add_comm] using
            jwMajorana_same_site_anticommute n i
        · simpa [jwCliffordGenerator] using
            (jwMajorana_distinct_sites_anticommute n i j heq).2.2.2
    | inr j =>
        have hne : i ≠ j := by intro heq; apply hij; simp [heq]
        simpa [jwCliffordGenerator] using
          (jwMajorana_distinct_sites_anticommute n i j hne).2.1

/-- The diagonal quadratic form for the finite split Clifford algebra, with
positive directions indexed by the first summand and negative directions by
the second. -/
def jwCliffordWeight {n : ℕ} (i : Fin n ⊕ Fin n) : ℝ :=
  match i with
  | .inl _ => 1
  | .inr _ => -1

/-- The finite Jordan--Wigner tower as a genuine representation of the
weighted split Clifford algebra `Cl(n,n)`. This uses the Clifford universal
property and the concrete tower matrices as the target algebra. -/
def jwCliffordRepresentation (n : ℕ) :
    CliffordAlgebra (QuadraticMap.weightedSumSquares ℝ (jwCliffordWeight (n := n)))
      →ₐ[ℝ] MatStage n := by
  classical
  exact CliffordAlgebra.lift _
    ⟨(Pi.basisFun ℝ (Fin n ⊕ Fin n)).constr ℝ (jwCliffordGenerator n),
      InfoGeometry.Core.AnticommutingSum.basis_square
        (jwCliffordGenerator n) (jwCliffordWeight (n := n))
        (by
          intro i j hij
          exact jwCliffordGenerator_anticommute i j hij)
        (by
          intro i
          rw [jwCliffordGenerator_sq]
          cases i <;> simp [jwCliffordWeight])⟩

/-- The concrete Clifford representation sends each canonical generator to
the corresponding Jordan--Wigner Majorana matrix. -/
@[simp] theorem jwCliffordRepresentation_ι (n : ℕ)
    (x : (Fin n ⊕ Fin n) → ℝ) :
    jwCliffordRepresentation n (CliffordAlgebra.ι _ x) =
      ∑ i, x i • jwCliffordGenerator n i := by
  classical
  rw [jwCliffordRepresentation, CliffordAlgebra.lift_ι_apply]
  simp [Module.Basis.constr_apply_fintype]

/-- On a basis vector, the Clifford representation is exactly the indexed
positive- or negative-square Jordan--Wigner generator. -/
@[simp] theorem jwCliffordRepresentation_basis (n : ℕ)
    (i : Fin n ⊕ Fin n) :
    jwCliffordRepresentation n (CliffordAlgebra.ι _ (Pi.single i 1)) =
      jwCliffordGenerator n i := by
  rw [jwCliffordRepresentation_ι]
  simp [Pi.single_apply]

/-- The finite Jordan--Wigner representation sends the Clifford commutator
of two canonical vectors to the corresponding matrix commutator. This is the
transport law needed to interpret Clifford bivectors as endomorphisms in the
tensor tower; it makes no claim that a separately chosen matrix coordinate
table is already identified with those vectors. -/
theorem jwCliffordRepresentation_vector_commutator (n : ℕ)
    (x y : (Fin n ⊕ Fin n) → ℝ) :
    jwCliffordRepresentation n
        (CliffordAlgebra.ι _ x * CliffordAlgebra.ι _ y -
          CliffordAlgebra.ι _ y * CliffordAlgebra.ι _ x) =
      (∑ i, x i • jwCliffordGenerator n i) *
          (∑ i, y i • jwCliffordGenerator n i) -
        (∑ i, y i • jwCliffordGenerator n i) *
          (∑ i, x i • jwCliffordGenerator n i) := by
  simp only [map_sub, map_mul, jwCliffordRepresentation_ι]

/-- On basis directions, the represented Clifford bivector is exactly the
commutator of the two Jordan--Wigner Majorana generators. -/
theorem jwCliffordRepresentation_basis_bivector (n : ℕ)
    (i j : Fin n ⊕ Fin n) :
    jwCliffordRepresentation n
        (CliffordAlgebra.ι _ (Pi.single i 1) *
            CliffordAlgebra.ι _ (Pi.single j 1) -
          CliffordAlgebra.ι _ (Pi.single j 1) *
            CliffordAlgebra.ι _ (Pi.single i 1)) =
      jwCliffordGenerator n i * jwCliffordGenerator n j -
        jwCliffordGenerator n j * jwCliffordGenerator n i := by
  simp

/-! ## Two-site Tetraktys frame in the Wigner--Jordan tower -/

/-- A product of two anticommuting factors anticommutes with `x` when the
first factor anticommutes with `x` and the second commutes with it. -/
private theorem product_anticomm_left_of_right_commute
    {R : Type*} [Ring R] (u v x : R)
    (hu : u * x + x * u = 0) (hv : v * x = x * v) :
    (u * v) * x + x * (u * v) = 0 := by
  calc
    (u * v) * x + x * (u * v) = u * (v * x) + (x * u) * v := by noncomm_ring
    _ = u * (x * v) + (x * u) * v := by rw [hv]
    _ = (u * x + x * u) * v := by noncomm_ring
    _ = 0 := by rw [hu]; simp

/-- A product of two anticommuting factors anticommutes with `x` when the
first factor commutes with `x` and the second anticommutes with it. -/
private theorem product_anticomm_right_of_left_commute
    {R : Type*} [Ring R] (u v x : R)
    (hu : u * x = x * u) (hv : v * x + x * v = 0) :
    (u * v) * x + x * (u * v) = 0 := by
  calc
    (u * v) * x + x * (u * v) = u * (v * x) + (x * u) * v := by noncomm_ring
    _ = u * (-(x * v)) + (u * x) * v := by rw [eq_neg_of_add_eq_zero_left hv, hu]
    _ = 0 := by noncomm_ring

/-- Exact Clifford relations for the ordered volume product of four pairwise
anticommuting generators. The proof uses only the abstract ring relations. -/
private theorem volume4_relations
    {R : Type*} [Ring R] (a b c d : R)
    (hab : a * b + b * a = 0) (hac : a * c + c * a = 0)
    (had : a * d + d * a = 0) (hbc : b * c + c * b = 0)
    (hbd : b * d + d * b = 0) (hcd : c * d + d * c = 0) :
    (((a * b) * (c * d)) * ((a * b) * (c * d)) =
      (a * a) * (b * b) * (c * c) * (d * d)) ∧
    ((a * b) * (c * d)) * a + a * ((a * b) * (c * d)) = 0 ∧
    ((a * b) * (c * d)) * b + b * ((a * b) * (c * d)) = 0 ∧
    ((a * b) * (c * d)) * c + c * ((a * b) * (c * d)) = 0 ∧
    ((a * b) * (c * d)) * d + d * ((a * b) * (c * d)) = 0 := by
  let u := a * b
  let v := c * d
  have hua : u * a + a * u = 0 := by
    dsimp [u]
    calc
      (a * b) * a + a * (a * b) = a * (b * a + a * b) := by noncomm_ring
      _ = 0 := by rw [eq_neg_of_add_eq_zero_left hab]; simp
  have hub : u * b + b * u = 0 := by
    dsimp [u]
    calc
      (a * b) * b + b * (a * b) = a * (b * b) + (b * a) * b := by noncomm_ring
      _ = 0 := by
        have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
        rw [hba]
        noncomm_ring
  have hvc : v * c + c * v = 0 := by
    dsimp [v]
    calc
      (c * d) * c + c * (c * d) = c * (d * c + c * d) := by noncomm_ring
      _ = 0 := by rw [eq_neg_of_add_eq_zero_left hcd]; simp
  have hvd : v * d + d * v = 0 := by
    dsimp [v]
    calc
      (c * d) * d + d * (c * d) = c * (d * d) + (d * c) * d := by noncomm_ring
      _ = 0 := by
        have hdc : d * c = -(c * d) := eq_neg_of_add_eq_zero_right hcd
        rw [hdc]
        noncomm_ring
  have huc0 := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_comm_orth
    a b c hac hbc
  have hud0 := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_comm_orth
    a b d had hbd
  have huc : u * c = c * u := sub_eq_zero.mp (by simpa [u,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using huc0)
  have hud : u * d = d * u := sub_eq_zero.mp (by simpa [u,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hud0)
  have hca : c * a + a * c = 0 := by simpa [add_comm] using hac
  have hda : d * a + a * d = 0 := by simpa [add_comm] using had
  have hcb : c * b + b * c = 0 := by simpa [add_comm] using hbc
  have hdb : d * b + b * d = 0 := by simpa [add_comm] using hbd
  have hva0 := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_comm_orth
    c d a hca hda
  have hvb0 := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_comm_orth
    c d b hcb hdb
  have hva : v * a = a * v := sub_eq_zero.mp (by simpa [v,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hva0)
  have hvb : v * b = b * v := sub_eq_zero.mp (by simpa [v,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using hvb0)
  have huv : u * v = v * u := by
    dsimp [u, v]
    calc
      (a * b) * (c * d) = ((a * b) * c) * d := by noncomm_ring
      _ = (c * (a * b)) * d := by rw [huc]
      _ = c * ((a * b) * d) := by noncomm_ring
      _ = c * (d * (a * b)) := by rw [hud]
      _ = (c * d) * (a * b) := by noncomm_ring
  have huSq := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_sq
    a b hab
  have hvSq := InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.clifford_bivector_sq
    c d hcd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      ((a * b) * (c * d)) * ((a * b) * (c * d)) =
          ((a * b) * ((c * d) * (a * b))) * (c * d) := by
            simp only [mul_assoc]
      _ = ((a * b) * ((a * b) * (c * d))) * (c * d) := by rw [huv]
      _ = ((a * b) * (a * b)) * ((c * d) * (c * d)) := by
            simp only [mul_assoc]
      _ = (-((a * a) * (b * b))) * (-((c * c) * (d * d))) := by rw [huSq, hvSq]
      _ = (a * a) * (b * b) * (c * c) * (d * d) := by noncomm_ring
  · exact product_anticomm_left_of_right_commute u v a hua hva
  · exact product_anticomm_left_of_right_commute u v b hub hvb
  · exact product_anticomm_right_of_left_commute u v c huc hvc
  · exact product_anticomm_right_of_left_commute u v d hud hvd

/-- The first tetraktys Dirac generator is the negative-square atom at the
first Wigner--Jordan site. -/
def jwTetraktysGamma0 : MatStage 2 := jwMajoranaMinus 2 0

/-- The second tetraktys Dirac generator is the positive-square atom at the
first Wigner--Jordan site. -/
def jwTetraktysGamma1 : MatStage 2 := jwMajoranaPlus 2 0

/-- The third tetraktys Dirac generator is the positive-square atom at the
second Wigner--Jordan site. -/
def jwTetraktysGamma2 : MatStage 2 := jwMajoranaPlus 2 1

/-- The fourth tetraktys direction is the ordered volume product of both
`Cl(1,1)` atoms. -/
def jwTetraktysGamma3 : MatStage 2 :=
  jwMajoranaPlus 2 0 * jwMajoranaMinus 2 0 *
    jwMajoranaPlus 2 1 * jwMajoranaMinus 2 1

/-- The two-site Wigner--Jordan tensor stage contains the tetraktys
`Cl(3,1)` frame: its fourth positive direction is the volume element of the
four signed `Cl(2,2)` tower generators. -/
theorem jwTetraktys_clifford_relations :
    jwTetraktysGamma0 * jwTetraktysGamma0 = -1 ∧
    jwTetraktysGamma1 * jwTetraktysGamma1 = 1 ∧
    jwTetraktysGamma2 * jwTetraktysGamma2 = 1 ∧
    jwTetraktysGamma3 * jwTetraktysGamma3 = 1 ∧
    jwTetraktysGamma0 * jwTetraktysGamma1 + jwTetraktysGamma1 * jwTetraktysGamma0 = 0 ∧
    jwTetraktysGamma0 * jwTetraktysGamma2 + jwTetraktysGamma2 * jwTetraktysGamma0 = 0 ∧
    jwTetraktysGamma0 * jwTetraktysGamma3 + jwTetraktysGamma3 * jwTetraktysGamma0 = 0 ∧
    jwTetraktysGamma1 * jwTetraktysGamma2 + jwTetraktysGamma2 * jwTetraktysGamma1 = 0 ∧
    jwTetraktysGamma1 * jwTetraktysGamma3 + jwTetraktysGamma3 * jwTetraktysGamma1 = 0 ∧
    jwTetraktysGamma2 * jwTetraktysGamma3 + jwTetraktysGamma3 * jwTetraktysGamma2 = 0 := by
  let a : MatStage 2 := jwMajoranaPlus 2 0
  let b : MatStage 2 := jwMajoranaMinus 2 0
  let c : MatStage 2 := jwMajoranaPlus 2 1
  let d : MatStage 2 := jwMajoranaMinus 2 1
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hCross := jwMajorana_distinct_sites_anticommute 2 0 1 hne
  have hab : a * b + b * a = 0 := by
    simpa [a, b] using jwMajorana_same_site_anticommute 2 0
  have hcd : c * d + d * c = 0 := by
    simpa [c, d] using jwMajorana_same_site_anticommute 2 1
  have hac : a * c + c * a = 0 := by simpa [a, c] using hCross.1
  have had : a * d + d * a = 0 := by simpa [a, d] using hCross.2.2.1
  have hbc : b * c + c * b = 0 := by simpa [b, c] using hCross.2.2.2
  have hbd : b * d + d * b = 0 := by simpa [b, d] using hCross.2.1
  have ha := jwMajoranaPlus_sq 2 0
  have hb := jwMajoranaMinus_sq 2 0
  have hc := jwMajoranaPlus_sq 2 1
  have hd := jwMajoranaMinus_sq 2 1
  have hv := volume4_relations a b c d hab hac had hbc hbd hcd
  have hba : b * a + a * b = 0 := by simpa [add_comm] using hab
  have hbc' : b * c + c * b = 0 := hbc
  have h0 : jwTetraktysGamma0 * jwTetraktysGamma0 = -1 := by
    simpa [jwTetraktysGamma0] using hb
  have h1 : jwTetraktysGamma1 * jwTetraktysGamma1 = 1 := by
    simpa [jwTetraktysGamma1] using ha
  have h2 : jwTetraktysGamma2 * jwTetraktysGamma2 = 1 := by
    simpa [jwTetraktysGamma2] using hc
  have h3 : jwTetraktysGamma3 * jwTetraktysGamma3 = 1 := by
    calc
      jwTetraktysGamma3 * jwTetraktysGamma3 =
          ((a * b) * (c * d)) * ((a * b) * (c * d)) := by
            simp [jwTetraktysGamma3, a, b, c, d, mul_assoc]
      _ = (a * a) * (b * b) * (c * c) * (d * d) := hv.1
      _ = 1 := by rw [ha, hb, hc, hd]; norm_num
  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [jwTetraktysGamma0, jwTetraktysGamma1, a, b] using hba
  · simpa [jwTetraktysGamma0, jwTetraktysGamma2, b, c] using hbc'
  · simpa [jwTetraktysGamma0, jwTetraktysGamma3, a, b, c, d, mul_assoc, add_comm] using hv.2.2.1
  · simpa [jwTetraktysGamma1, jwTetraktysGamma2, a, c] using hac
  · simpa [jwTetraktysGamma1, jwTetraktysGamma3, a, b, c, d, mul_assoc, add_comm] using hv.2.1
  · simpa [jwTetraktysGamma2, jwTetraktysGamma3, a, b, c, d, mul_assoc, add_comm] using hv.2.2.2.1

/-- The tetraktys frame is the image under the concrete Clifford-algebra
representation of the ordered Wigner--Jordan generators; the fourth frame
element is the represented volume word. -/
theorem jwTetraktys_frame_is_jwClifford_image :
    jwCliffordRepresentation 2 (CliffordAlgebra.ι _ (Pi.single (Sum.inr (0 : Fin 2)) 1)) =
        jwTetraktysGamma0 ∧
    jwCliffordRepresentation 2 (CliffordAlgebra.ι _ (Pi.single (Sum.inl (0 : Fin 2)) 1)) =
        jwTetraktysGamma1 ∧
    jwCliffordRepresentation 2 (CliffordAlgebra.ι _ (Pi.single (Sum.inl (1 : Fin 2)) 1)) =
        jwTetraktysGamma2 ∧
    jwCliffordRepresentation 2
        (CliffordAlgebra.ι _ (Pi.single (Sum.inl (0 : Fin 2)) 1) *
          CliffordAlgebra.ι _ (Pi.single (Sum.inr (0 : Fin 2)) 1) *
          CliffordAlgebra.ι _ (Pi.single (Sum.inl (1 : Fin 2)) 1) *
          CliffordAlgebra.ι _ (Pi.single (Sum.inr (1 : Fin 2)) 1)) = jwTetraktysGamma3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [jwTetraktysGamma0, jwCliffordGenerator] using
      jwCliffordRepresentation_basis 2 (Sum.inr (0 : Fin 2))
  · simpa [jwTetraktysGamma1, jwCliffordGenerator] using
      jwCliffordRepresentation_basis 2 (Sum.inl (0 : Fin 2))
  · simpa [jwTetraktysGamma2, jwCliffordGenerator] using
      jwCliffordRepresentation_basis 2 (Sum.inl (1 : Fin 2))
  · simp [map_mul, jwCliffordRepresentation_basis, jwTetraktysGamma3,
      jwCliffordGenerator]

/-- The finite Wigner--Jordan tower's six bivectors act on the tetraktys
four-vector module by the standard real `so(3,1)` rotation and boost laws. -/
theorem jwTetraktys_so31_bivector_action (p0 p1 p2 p3 : ℤ) :
    (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma12
        jwTetraktysGamma1 jwTetraktysGamma2 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma12
          jwTetraktysGamma1 jwTetraktysGamma2 = -1 ∧
     InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma23
        jwTetraktysGamma2 jwTetraktysGamma3 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma23
          jwTetraktysGamma2 jwTetraktysGamma3 = -1 ∧
     InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma31
        jwTetraktysGamma3 jwTetraktysGamma1 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma31
          jwTetraktysGamma3 jwTetraktysGamma1 = -1 ∧
     InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost01
        jwTetraktysGamma0 jwTetraktysGamma1 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost01
          jwTetraktysGamma0 jwTetraktysGamma1 = 1 ∧
     InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost02
        jwTetraktysGamma0 jwTetraktysGamma2 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost02
          jwTetraktysGamma0 jwTetraktysGamma2 = 1 ∧
     InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost03
        jwTetraktysGamma0 jwTetraktysGamma3 *
        InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost03
          jwTetraktysGamma0 jwTetraktysGamma3 = 1) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma12
        jwTetraktysGamma1 jwTetraktysGamma2)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 0 p2 (-p1) 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma23
        jwTetraktysGamma2 jwTetraktysGamma3)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 0 0 p3 (-p2) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.sigma31
        jwTetraktysGamma3 jwTetraktysGamma1)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 0 (-p3) 0 p1 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost01
        jwTetraktysGamma0 jwTetraktysGamma1)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p1 p0 0 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost02
        jwTetraktysGamma0 jwTetraktysGamma2)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p2 0 p0 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.boost03
        jwTetraktysGamma0 jwTetraktysGamma3)
      (InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p0 p1 p2 p3) =
      (2 : ℤ) • InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.diracVector
        jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3 p3 0 0 p0 := by
  rcases jwTetraktys_clifford_relations with
    ⟨h0, h1, h2, h3, h01, h02, h03, h12, h13, h23⟩
  exact InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.so31_bivector_squares_and_diracVector_action
    jwTetraktysGamma0 jwTetraktysGamma1 jwTetraktysGamma2 jwTetraktysGamma3
    p0 p1 p2 p3 h0 h1 h2 h3 h01 h02 h03 h12 h13 h23

end InfoGeometry.Clifford.Cl11JordanWignerCARBridge

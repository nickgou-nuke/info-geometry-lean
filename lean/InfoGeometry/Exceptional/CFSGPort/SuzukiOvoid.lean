/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCatalog

public noncomputable section

open scoped LinearAlgebra.Projectivization
open scoped Pointwise

namespace InfoGeometry.Exceptional.CFSGPort.Suzuki

open InfoGeometry.Exceptional.CFSGPort.Chevalley

variable {K : Type} [Field K]

/-- The distinguished point at infinity in the Suzuki projective ovoid. -/
def ovoidInfinity : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![1, 0, 0, 0] (by simp)

/-- The normalized finite-point chart of the Suzuki projective ovoid. -/
def ovoidPoint (pi : K ≃+* K) (x y : K) : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)

/-- The Suzuki ovoid carrier in projective three-space. -/
def ovoid (pi : K ≃+* K) : Set (ℙ K (Fin 4 → K)) :=
  {ovoidInfinity} ∪ Set.range fun z : K × K => ovoidPoint pi z.1 z.2

/-- The normalized finite-point chart is injective: the last projective
coordinate fixes its scalar, and the next two coordinates recover the pair. -/
theorem ovoidPoint_injective (pi : K ≃+* K) :
    Function.Injective (fun z : K × K => ovoidPoint pi z.1 z.2) := by
  intro z w hzw
  change Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1] _ =
    Projectivization.mk K
      ![w.1 * w.2 + pi w.1 * w.1 ^ 2 + pi w.2, w.2, w.1, 1] _ at hzw
  rw [Projectivization.mk_eq_mk_iff] at hzw
  rcases hzw with ⟨c, hc⟩
  have hc_one : (c : K) = 1 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simpa [Units.smul_def] using hc3
  apply Prod.ext
  · have hc2 := congrFun hc (2 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc2.symm
  · have hc1 := congrFun hc (1 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc1.symm

/-- The distinguished point at infinity is not in the finite-point chart. -/
theorem ovoidInfinity_not_mem_range (pi : K ≃+* K) :
    ovoidInfinity (K := K) ∉ Set.range (fun z : K × K => ovoidPoint pi z.1 z.2) := by
  rintro ⟨z, hz⟩
  change Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1] _ =
    Projectivization.mk K ![1, 0, 0, 0] _ at hz
  rw [Projectivization.mk_eq_mk_iff] at hz
  rcases hz with ⟨c, hc⟩
  have hc_zero : (c : K) = 0 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simp at hc3
  exact c.ne_zero hc_zero

/-- The finite Suzuki ovoid carrier has cardinality `|K|^2 + 1`. -/
theorem ovoid_card (pi : K ≃+* K) [Finite K] :
    Nat.card {z // z ∈ ovoid pi} = Nat.card K ^ 2 + 1 := by
  let toO : Option (K × K) → {z // z ∈ ovoid pi}
    | none => ⟨ovoidInfinity (K := K), Or.inl (Set.mem_singleton _)⟩
    | some z => ⟨ovoidPoint pi z.1 z.2, Or.inr ⟨z, rfl⟩⟩
  have htoO_inj : Function.Injective toO := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        exfalso
        exact ovoidInfinity_not_mem_range pi ⟨v, (congrArg Subtype.val huv).symm⟩
    | some u =>
      cases v with
      | none =>
        exfalso
        exact ovoidInfinity_not_mem_range pi ⟨u, congrArg Subtype.val huv⟩
      | some v =>
        exact congrArg Option.some (ovoidPoint_injective pi (congrArg Subtype.val huv))
  have htoO_surj : Function.Surjective toO := by
    intro z
    rcases z with ⟨z, hz⟩
    change z ∈ {ovoidInfinity} ∪ Set.range (fun z : K × K => ovoidPoint pi z.1 z.2) at hz
    rcases hz with hz | ⟨w, hw⟩
    · have hz_eq : z = ovoidInfinity (K := K) := by simpa using hz
      subst z
      exact ⟨none, rfl⟩
    · subst z
      exact ⟨some w, rfl⟩
  let e : Option (K × K) ≃ {z // z ∈ ovoid pi} :=
    Equiv.ofBijective toO ⟨htoO_inj, htoO_surj⟩
  calc
    Nat.card {z // z ∈ ovoid pi} = Nat.card (Option (K × K)) :=
      Nat.card_congr e.symm
    _ = Nat.card (K × K) + 1 := Finite.card_option
    _ = Nat.card K * Nat.card K + 1 := by rw [Nat.card_prod]
    _ = Nat.card K ^ 2 + 1 := by rw [pow_two]

/-- The upper-root Suzuki generator as an invertible linear operator. Its
matrix is the transpose presentation of the locally owned lower-root matrix. -/
def upperRootOperator (a : ℕ) (u v : K) : Matrix.GeneralLinearGroup (Fin 4) K :=
  suzukiSGL a u v

/-- The antidiagonal Suzuki Weyl matrix on the four-dimensional carrier. -/
def suzukiWeylMatrix : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

/-- The antidiagonal Weyl generator as an invertible linear operator. -/
def suzukiWeylOperator : Matrix.GeneralLinearGroup (Fin 4) K :=
  { val := suzukiWeylMatrix
    inv := suzukiWeylMatrix
    val_inv := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] }

/-- The torus generator of the full Suzuki operator group, represented on the
same four-dimensional carrier as its root and Weyl generators. -/
def suzukiTorusOperator (a : ℕ) (l : Kˣ) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l) (by
    rw [suzukiD_det]
    exact one_ne_zero)

/-- Multiplication of torus operators follows multiplication in `Kˣ`. -/
theorem suzukiTorusOperator_mul (a : ℕ) (l m : Kˣ) :
    suzukiTorusOperator a l * suzukiTorusOperator a m =
      suzukiTorusOperator a (l * m) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change suzukiD a l * suzukiD a m = suzukiD a (l * m)
  exact suzukiD_mul a l m

/-- The identity parameter gives the identity torus operator. -/
theorem suzukiTorusOperator_one (a : ℕ) :
    suzukiTorusOperator a (1 : Kˣ) = 1 := by
  apply Units.ext
  change suzukiD a (1 : Kˣ) = 1
  exact suzukiD_one a

/-- Inversion of torus operators agrees with inversion of their parameters. -/
theorem suzukiTorusOperator_inv (a : ℕ) (l : Kˣ) :
    (suzukiTorusOperator a l)⁻¹ = suzukiTorusOperator a l⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  rw [suzukiTorusOperator_mul, mul_inv_cancel, suzukiTorusOperator_one]

set_option maxHeartbeats 1600000
/-- Conjugation by a Suzuki torus operator rescales the two parameters of the
upper-root operator by `l` and `l * pi l`. This is the local operator-carrier
form of the torus/root relation used in the external Huppert proof. -/
theorem suzukiTorusOperator_conj_upperRoot
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (u v : K) :
    suzukiTorusOperator a l * upperRootOperator a u v *
        (suzukiTorusOperator a l)⁻¹ =
      upperRootOperator a ((l : K) * u) ((l : K) * pi (l : K) * v) := by
  apply Units.ext
  rw [suzukiTorusOperator_inv, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul]
  change suzukiD a l * (suzukiS a u v).transpose * suzukiD a l⁻¹ =
    (suzukiS a ((l : K) * u) ((l : K) * pi (l : K) * v)).transpose
  rw [suzukiD_eq, suzukiD_eq]
  let x : K := l
  have hratio : x ^ (1 + 2 ^ a) * (x ^ (2 ^ a))⁻¹ = x := by
    rw [pow_add, pow_one]
    simp [x, pow_ne_zero _ l.ne_zero]
  have hsigma_sq : x ^ (2 ^ a) * x ^ (2 ^ a) = x ^ (2 ^ (a + 1)) := by
    rw [← pow_two, ← pow_mul, pow_succ]
  have hmiddle : x ^ (2 ^ a) * x ^ (1 + 2 ^ a) =
      x * x ^ (2 ^ (a + 1)) := by
    calc
      x ^ (2 ^ a) * x ^ (1 + 2 ^ a) = x ^ (2 ^ a + (1 + 2 ^ a)) :=
        (pow_add _ _ _).symm
      _ = x ^ (1 + 2 ^ (a + 1)) := by
        congr 1
        rw [pow_succ]
        omega
      _ = x * x ^ (2 ^ (a + 1)) := by rw [pow_add, pow_one]
  have houter_sq : x ^ (1 + 2 ^ a) * x ^ (1 + 2 ^ a) =
      x ^ (2 + 2 ^ (a + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ]
    omega
  have hsigma_inv : x ^ (2 ^ a) * (x⁻¹) ^ (2 ^ a) = 1 := by
    rw [← mul_pow]
    simp [x, l.ne_zero]
  have hpi_iter : (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) = x ^ 2 := by
    calc
      (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) = pi (pi x) := by
        rw [hpi_formula, hpi_formula]
      _ = x ^ 2 := hpi_sq x
  have hexp : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (a * 2) * 4 := by
    calc
      2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ ((a + 1) + (a + 1)) := by
        rw [← pow_add]
      _ = 2 ^ (a * 2 + 2) := by congr 1 <;> omega
      _ = 2 ^ (a * 2) * 4 := by rw [pow_add]; norm_num
  have hpi_iter' : x ^ 2 = x ^ (2 ^ (a * 2) * 4) := by
    calc
      x ^ 2 = (x ^ (2 ^ (a + 1))) ^ (2 ^ (a + 1)) := hpi_iter.symm
      _ = x ^ (2 ^ (a + 1) * 2 ^ (a + 1)) := by rw [← pow_mul]
      _ = x ^ (2 ^ (a * 2) * 4) := by rw [hexp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, suzukiN, Matrix.mul_apply, Matrix.diagonal_apply,
      hpi_formula, hratio, hsigma_sq, hmiddle, houter_sq, hpi_iter,
      hsigma_inv, mul_pow, inv_pow, mul_comm, mul_left_comm] <;> ring_nf
  all_goals
    try simp [mul_comm]
    try rw [hpi_iter']
    try simp [x, mul_comm]
    try ring
set_option maxHeartbeats 200000

/-- The subgroup generated by the Suzuki torus operators on the actual
four-dimensional operator carrier. It is one component of the ovoid point
stabilizer used in the simplicity argument. -/
def suzukiTorusOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure (Set.range (suzukiTorusOperator a))

/-- The torus operators commute as endomorphism units, since their matrices
are diagonal in the same operator basis. -/
theorem suzukiTorusOperator_commute (a : ℕ) (l m : Kˣ) :
    Commute (suzukiTorusOperator a l) (suzukiTorusOperator a m) := by
  rw [commute_iff_eq]
  apply Units.ext
  change Matrix.diagonal ![
      ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
      ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
      ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
      ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] *
      Matrix.diagonal ![
        ((m ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
        ((m ^ (2 ^ a : ℤ) : Kˣ) : K),
        ((m ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
        ((m ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] =
    Matrix.diagonal ![
      ((m ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
      ((m ^ (2 ^ a : ℤ) : Kˣ) : K),
      ((m ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
      ((m ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)] *
      Matrix.diagonal ![
        ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K),
        ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
        ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K),
        ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)]
  exact (Matrix.commute_diagonal _ _).eq

/-- The generated Suzuki torus is an abelian subgroup of the operator group. -/
theorem suzukiTorusOperatorGroup_isMulCommutative (a : ℕ) :
    IsMulCommutative (suzukiTorusOperatorGroup (K := K) a) := by
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy _
  obtain ⟨l, rfl⟩ := Set.mem_range.mp hx
  obtain ⟨m, rfl⟩ := Set.mem_range.mp hy
  exact suzukiTorusOperator_commute a l m

/-- The operator torus is solvable, as an abelian subgroup of the
noncommutative Suzuki operator carrier. -/
theorem suzukiTorusOperatorGroup_isSolvable (a : ℕ) :
    Group.IsSolvable (suzukiTorusOperatorGroup (K := K) a) := by
  letI : IsMulCommutative (suzukiTorusOperatorGroup (K := K) a) :=
    suzukiTorusOperatorGroup_isMulCommutative (K := K) a
  infer_instance

/-- The torus operator is one of the generators of the full Suzuki group. -/
theorem suzukiTorusOperator_mem_suzukiMatrixGroup (a : ℕ) (l : Kˣ) :
    suzukiTorusOperator a l ∈ Chevalley.suzukiMatrixGroup a K := by
  change Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l)
      (by rw [suzukiD_det]; exact one_ne_zero) ∈ Chevalley.suzukiMatrixGroup a K
  exact Chevalley.suzukiD_mem_suzukiMatrixGroup a K l

/-- The generated torus subgroup stays inside the full Suzuki operator
group, including after taking subgroup closure. -/
theorem suzukiTorusOperatorGroup_le_suzukiMatrixGroup (a : ℕ) :
    suzukiTorusOperatorGroup (K := K) a ≤ Chevalley.suzukiMatrixGroup a K := by
  apply (Subgroup.closure_le (Chevalley.suzukiMatrixGroup a K)).2
  rintro _ ⟨l, rfl⟩
  exact suzukiTorusOperator_mem_suzukiMatrixGroup a l

/-- The torus generator lies in the full Suzuki group acting on the
four-dimensional endomorphism carrier. -/
theorem suzukiTorusOperator_mem_suzukiGroup (a : ℕ) (l : Kˣ) :
    Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
      (suzukiTorusOperator a l) ∈ Chevalley.suzukiGroup a K := by
  change Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
      (suzukiTorusOperator a l) ∈
        (Chevalley.suzukiMatrixGroup a K).map
          (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).toMonoidHom
  rw [Subgroup.mem_map]
  exact ⟨suzukiTorusOperator a l, suzukiTorusOperator_mem_suzukiMatrixGroup a l, rfl⟩

/-- The torus subgroup also sits in the full group of endomorphism units on
the four-dimensional function module. -/
theorem suzukiTorusOperatorGroup_map_le_suzukiGroup (a : ℕ) :
    (suzukiTorusOperatorGroup (K := K) a).map
        (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))).toMonoidHom ≤
      Chevalley.suzukiGroup a K := by
  rw [Chevalley.suzukiGroup]
  exact Subgroup.map_mono
    (suzukiTorusOperatorGroup_le_suzukiMatrixGroup (K := K) a)

/-- A torus operator rescales the finite Suzuki ovoid chart by `l` and
`l * pi l`, matching the action of the full Suzuki operator group. -/
theorem suzukiTorusOperator_smul_finite
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (x y : K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
        ovoidPoint pi x y =
      ovoidPoint pi ((l : K) * x) ((l : K) * pi (l : K) * y) := by
  change (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![((l : K) * x) * ((l : K) * pi (l : K) * y) +
          pi ((l : K) * x) * ((l : K) * x) ^ 2 +
          pi ((l : K) * pi (l : K) * y),
        (l : K) * pi (l : K) * y, (l : K) * x, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((l : K) ^ (1 + 2 ^ a))⁻¹, ?_⟩
  have hu : (l : K) ≠ 0 := l.ne_zero
  let s : K := (l : K) ^ (2 ^ a)
  have hs : (l : K) ^ (2 ^ a) = s := rfl
  have hs_ne : s ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ hu
  have huouter : (l : K) ^ (1 + 2 ^ a) ≠ 0 := pow_ne_zero _ hu
  have hpi_l : pi (l : K) = s ^ 2 := by
    calc
      pi (l : K) = ((l : K) ^ (2 ^ a)) ^ 2 := by
        rw [hpi_formula, pow_succ, pow_mul]
      _ = s ^ 2 := by rw [hs]
  have huouter_formula : (l : K) ^ (1 + 2 ^ a) = (l : K) * s := by
    rw [pow_add, pow_one, hs]
  have hexp2 : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) := by
    norm_cast
  have hs_zpow : (l : K) ^ ((2 : ℤ) ^ a) = s := by
    rw [hexp2, zpow_natCast, hs]
  have huouter_formula_zpow :
      (l : K) ^ (1 + (2 : ℤ) ^ a) = (l : K) * s := by
    have hexp : 1 + (2 : ℤ) ^ a = ((1 + 2 ^ a : ℕ) : ℤ) := by
      rw [hexp2, Nat.cast_add, Nat.cast_one]
    rw [hexp, zpow_natCast, huouter_formula]
  funext i
  fin_cases i <;>
    simp [suzukiTorusOperator, suzukiD, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, map_mul, hpi_sq]
  · rw [hpi_l, huouter_formula]
    have hus_ne : (l : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    have hinner :
        (l : K) * x * ((l : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((l : K) * x) ^ 2 +
            s ^ 2 * (l : K) ^ 2 * pi y =
          ((l : K) * s) ^ 2 * (x * y + pi x * x ^ 2 + pi y) := by
      ring
    calc
      ((l : K) * s)⁻¹ *
          ((l : K) * x * ((l : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((l : K) * x) ^ 2 +
            s ^ 2 * (l : K) ^ 2 * pi y) =
          ((l : K) * s)⁻¹ * (((l : K) * s) ^ 2 *
            (x * y + pi x * x ^ 2 + pi y)) := by rw [hinner]
      _ = ((l : K) * s) * (x * y + pi x * x ^ 2 + pi y) := by
        rw [pow_two, mul_assoc]
        exact inv_mul_cancel_left₀ hus_ne _
    rw [← huouter_formula]
    rw [← zpow_natCast]
    congr 1
  · rw [hpi_l, huouter_formula]
    have hus_ne : (l : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    rw [show (l : K) * s ^ 2 * y = ((l : K) * s) * (s * y) by ring]
    field_simp [hus_ne]
    rw [hs_zpow]
    exact mul_comm s y
  · field_simp [hu, hs_ne]
    rw [huouter_formula, ← hs]
    rw [← zpow_natCast, hexp2]
    ac_rfl
  · rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring

/-- The torus operator fixes the distinguished point at infinity. -/
theorem suzukiTorusOperator_smul_infinity (a : ℕ) (l : Kˣ) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity := by
  change (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv •
      Projectivization.mk K ![1, 0, 0, 0] (by simp) =
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), ?_⟩
  funext i
  fin_cases i <;>
    simp [suzukiTorusOperator, suzukiD, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- Every element of the generated Suzuki torus fixes the ovoid point at
infinity. -/
theorem suzukiTorusOperatorGroup_smul_infinity (a : ℕ)
    (g : suzukiTorusOperatorGroup (K := K) a) :
    (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K))).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hclosure : suzukiTorusOperatorGroup (K := K) a ≤ S := by
    rw [suzukiTorusOperatorGroup, Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    change Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact suzukiTorusOperator_smul_infinity a l
  have hg : g.1 ∈ S := hclosure g.2
  change Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K)) at hg
  exact MulAction.mem_stabilizer_iff.mp hg

/-- Each torus operator preserves the full projective Suzuki ovoid. -/
theorem suzukiTorusOperator_maps_ovoid
    (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1)))
    (l : Kˣ) (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (suzukiTorusOperator a l)).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [suzukiTorusOperator_smul_infinity]
    exact Or.inl (by simp)
  · exact Or.inr ⟨((l : K) * w.1, (l : K) * pi (l : K) * w.2),
      (suzukiTorusOperator_smul_finite a pi hpi_sq hpi_formula l w.1 w.2).symm⟩

/-- The upper-root Suzuki operator fixes the distinguished ovoid point at
infinity. -/
theorem upperRootOperator_smul_infinity (a : ℕ) (u v : K) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidInfinity := by
  change (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      Projectivization.mk K ![1, 0, 0, 0] (by simp) =
        Projectivization.mk K ![1, 0, 0, 0] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [upperRootOperator, suzukiSGL, suzukiS, suzukiN]

/-- The antidiagonal Weyl operator sends infinity to the zero chart point. -/
theorem suzukiWeylOperator_smul_infinity (pi : K ≃+* K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidInfinity (K := K) = ovoidPoint pi 0 0 := by
  have h : (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K (![1, 0, 0, 0] : Fin 4 → K) (by simp) =
    Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) (by simp) := by
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
  simpa [ovoidInfinity, ovoidPoint] using h

/-- The antidiagonal Weyl operator sends the zero chart point to infinity. -/
theorem suzukiWeylOperator_smul_zero (pi : K ≃+* K) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidPoint pi 0 0 = ovoidInfinity := by
  have h : (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K (![0, 0, 0, 1] : Fin 4 → K) (by simp) =
    Projectivization.mk K (![1, 0, 0, 0] : Fin 4 → K) (by simp) := by
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
  simpa [ovoidInfinity, ovoidPoint] using h

/-- The reciprocal coordinates of a finite ovoid point have reciprocal norm.
This is the field calculation used by the Weyl operator action. -/
theorem suzukiOvoidNorm_inv [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2) (x y : K) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
        pi (n⁻¹ * x) = n⁻¹ := by
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
      pi (n⁻¹ * x) = n⁻¹
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have hpi_n : pi n = pi x * pi y + x ^ 2 * (pi x) ^ 2 + y ^ 2 := by
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hcore :
      pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 = pi n * n := by
    rw [hpi_n]
    dsimp only [n]
    linear_combination
      (pi x * pi y * x * y + (pi x) ^ 2 * x ^ 3 * y) * htwo
  simp only [map_mul, map_inv₀]
  have hd : pi n * n ^ 2 ≠ 0 := mul_ne_zero hpin (pow_ne_zero _ hn)
  apply mul_left_cancel₀ hd
  calc
    (pi n * n ^ 2) *
        ((n⁻¹ * y) * (n⁻¹ * x) +
          (pi n)⁻¹ * pi y * (n⁻¹ * y) ^ 2 + (pi n)⁻¹ * pi x) =
        pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 := by
      field_simp [hn, hpin]
    _ = pi n * n := hcore
    _ = (pi n * n ^ 2) * n⁻¹ := by field_simp [hn, hpin]

/-- Away from the zero chart point, the antidiagonal Weyl operator acts on
the finite Suzuki ovoid coordinates by reciprocal norm coordinates. -/
theorem suzukiWeylOperator_smul_finite_of_norm_ne_zero [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (x y : K) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
        ovoidPoint pi x y = ovoidPoint pi (n⁻¹ * y) (n⁻¹ * x) := by
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      ovoidPoint pi x y = ovoidPoint pi (n⁻¹ * y) (n⁻¹ * x)
  intro hn
  have hnorm_inv :
      (n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
        pi (n⁻¹ * x) = n⁻¹ := by
    exact suzukiOvoidNorm_inv pi hpi_sq x y hn
  change (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv •
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![(n⁻¹ * y) * (n⁻¹ * x) + pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 +
          pi (n⁻¹ * x), n⁻¹ * x, n⁻¹ * y, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨n, ?_⟩
  have hncancel (z : K) : n * (n⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  funext i
  fin_cases i
  · rw [hnorm_inv]
    simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    exact mul_inv_cancel₀ hn
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, hncancel]
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, hncancel]
  · simp [suzukiWeylOperator, suzukiWeylMatrix, Matrix.mulVec, dotProduct,
      n]

/-- The antidiagonal Weyl operator preserves the Suzuki ovoid when the
Suzuki norm vanishes only at the zero coordinate pair. -/
theorem suzukiWeylOperator_maps_ovoid [CharP K 2]
    (pi : K ≃+* K) (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (suzukiWeylOperator (K := K))).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [suzukiWeylOperator_smul_infinity]
    exact Or.inr ⟨(0, 0), rfl⟩
  · rcases w with ⟨x, y⟩
    let n : K := x * y + pi x * x ^ 2 + pi y
    by_cases hn : n = 0
    · have hxy := hnorm_zero x y (by simpa [n] using hn)
      rcases hxy with ⟨rfl, rfl⟩
      rw [suzukiWeylOperator_smul_zero]
      exact Or.inl (by simp)
    · rw [suzukiWeylOperator_smul_finite_of_norm_ne_zero pi hpi_sq x y hn]
      exact Or.inr ⟨(n⁻¹ * y, n⁻¹ * x), rfl⟩

/-- The upper-root Suzuki operator acts on the normalized finite ovoid chart
by the root-group multiplication formula. -/
theorem upperRootOperator_smul_finite
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (u v x y : K) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      ovoidPoint pi x y =
        ovoidPoint pi (x + u) (y + v + pi u * (x + u)) := by
  change (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv •
      Projectivization.mk K ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp) =
    Projectivization.mk K
      ![(x + u) * (y + v + pi u * (x + u)) +
          pi (x + u) * (x + u) ^ 2 + pi (y + v + pi u * (x + u)),
        y + v + pi u * (x + u), x + u, 1] (by simp)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  have hpow (z : K) : z ^ (2 ^ (a + 1)) = pi z := (hpi_formula z).symm
  have hpow_one (z : K) : z ^ (1 + 2 ^ (a + 1)) = z * pi z := by
    rw [pow_add, hpow, pow_one]
  have hpow_one' (z : K) : z ^ (2 ^ (a + 1) + 1) = z * pi z := by
    rw [Nat.add_comm (2 ^ (a + 1)) 1, hpow_one]
  have hpow_two (z : K) : z ^ (2 + 2 ^ (a + 1)) = z ^ 2 * pi z := by
    rw [pow_add, hpow]
  have hpow_two' (z : K) : z ^ (2 ^ (a + 1) + 2) = z ^ 2 * pi z := by
    rw [Nat.add_comm (2 ^ (a + 1)) 2, hpow_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  funext i
  fin_cases i <;>
    simp [upperRootOperator, suzukiSGL, suzukiS, suzukiN,
      hpow, hpow_one', hpow_two', map_add, map_mul, hpi_sq]
  linear_combination
    (x ^ 2 * pi u + 2 * x * u * pi u + x * u * pi x +
      u ^ 2 * pi u + u ^ 2 * pi x) * htwo
  ring

/-- Every upper-root Suzuki operator preserves the projective ovoid. -/
theorem upperRootOperator_maps_ovoid
    [CharP K 2] (a : ℕ) (pi : K ≃+* K) (u v : K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    (Matrix.GeneralLinearGroup.toLin (upperRootOperator a u v)).toLinearEquiv • z ∈
      ovoid pi := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨w, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    rw [upperRootOperator_smul_infinity]
    exact Or.inl (by simp)
  · exact Or.inr ⟨(w.1 + u, w.2 + v + pi u * (w.1 + u)),
      (upperRootOperator_smul_finite a pi hpi_sq hpi_formula u v w.1 w.2).symm⟩

/-- The subgroup generated by the actual upper-root Suzuki operators. -/
def upperRootMatrixGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure {g | ∃ u v : K, g = upperRootOperator a u v}

/-- Under the Suzuki field-cardinality condition, the closure defining the
upper-root group is already the set of its two-parameter operators. The
parameter law, identity, and inverse formulas make that range a subgroup on
the same four-dimensional general-linear carrier. -/
theorem upperRootMatrixGroup_eq_paramRange [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (upperRootMatrixGroup (K := K) a :
      Set (Matrix.GeneralLinearGroup (Fin 4) K)) =
      {g | ∃ u v : K, g = upperRootOperator a u v} := by
  let H : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) := {
    carrier := {g | ∃ u v : K, g = upperRootOperator a u v}
    one_mem' := by
      refine ⟨0, 0, ?_⟩
      simpa [upperRootOperator] using
        (suzukiSGL_zero_zero (a := a) (K := K)).symm
    mul_mem' := by
      rintro g h ⟨u, v, rfl⟩ ⟨c, d, rfl⟩
      exact ⟨u + c, v + d + c ^ 2 ^ (a + 1) * u,
        (suzukiSGL_mul a hK u v c d)⟩
    inv_mem' := by
      rintro g ⟨u, v, rfl⟩
      exact ⟨u, v + u ^ (2 ^ (a + 1) + 1), suzukiSGL_inv a hK u v⟩
  }
  have hEq : upperRootMatrixGroup (K := K) a = H := by
    apply le_antisymm
    · rw [upperRootMatrixGroup, Subgroup.closure_le]
      intro g hg
      exact hg
    · intro g hg
      rcases hg with ⟨u, v, rfl⟩
      exact Subgroup.subset_closure ⟨u, v, rfl⟩
  change (upperRootMatrixGroup (K := K) a :
    Set (Matrix.GeneralLinearGroup (Fin 4) K)) = _
  rw [hEq]
  rfl

/-- The commutator of two upper-root Suzuki operators is a central root
operator. Its central parameter is the alternating part of the twisted
bilinear term in the root multiplication law. This is the local matrix
operator form of the root-commutator identity used by the external
Bender--Suzuki simplicity proof. -/
theorem upperRootOperator_commutator [Finite K] [CharP K 2] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v c d : K) :
    upperRootOperator a u v * upperRootOperator a c d *
        (upperRootOperator a u v)⁻¹ * (upperRootOperator a c d)⁻¹ =
      upperRootOperator a 0
        (c ^ (2 ^ (a + 1)) * u + u ^ (2 ^ (a + 1)) * c) := by
  apply suzukiSGL_injective a
  simp only [upperRootOperator, suzukiSGL_mul a hK, suzukiSGL_inv a hK]
  apply Prod.ext
  · simp [CharP.cast_eq_zero (K := K) 2]
  · have htwo : (2 : K) = 0 := CharP.cast_eq_zero (K := K) 2
    linear_combination
      (v + d + c ^ (2 ^ (a + 1)) * u +
        v + u ^ (2 ^ (a + 1) + 1) +
        u ^ (2 ^ (a + 1)) * (u + c) +
        d + c ^ (2 ^ (a + 1) + 1) +
        c ^ (2 ^ (a + 1)) * c +
        c ^ (2 ^ (a + 1)) * (c + u)) * htwo

/-- The two field parameters give a bijective coordinate system on the
upper-root subgroup. -/
noncomputable def upperRootParamEquiv [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    K × K ≃ ↥(upperRootMatrixGroup (K := K) a) := by
  let f : K × K → ↥(upperRootMatrixGroup (K := K) a) := fun p =>
    ⟨upperRootOperator a p.1 p.2, by
      exact Subgroup.subset_closure ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      apply suzukiSGL_injective a
      simpa [f, upperRootOperator] using congrArg Subtype.val hpq
    · intro g
      have hg : (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
          ({x | ∃ u v : K, x = upperRootOperator a u v} :
            Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
        rw [← upperRootMatrixGroup_eq_paramRange (K := K) a hK]
        exact g.property
      rcases hg with ⟨u, v, h⟩
      exact ⟨(u, v), Subtype.ext h.symm⟩
  exact Equiv.ofBijective f hf

/-- The local upper-root Suzuki subgroup has the expected `|K|²` elements,
counted on its actual matrix-operator carrier. -/
theorem upperRootMatrixGroup_card [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (upperRootMatrixGroup (K := K) a) = Nat.card K ^ 2 := by
  calc
    Nat.card (upperRootMatrixGroup (K := K) a) = Nat.card (K × K) :=
      Nat.card_congr (upperRootParamEquiv (K := K) a hK).symm
    _ = Nat.card K * Nat.card K := by rw [Nat.card_prod]
    _ = Nat.card K ^ 2 := by rw [pow_two]

/-- The local upper-root Suzuki subgroup is solvable: its faithful parameter
count makes it a finite 2-group, hence nilpotent and solvable. -/
theorem upperRootMatrixGroup_isSolvable [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Group.IsSolvable (upperRootMatrixGroup (K := K) a) := by
  have hcard : Nat.card (upperRootMatrixGroup (K := K) a) =
      2 ^ (2 * (2 * a + 1)) := by
    rw [upperRootMatrixGroup_card (K := K) a hK, hK, ← pow_mul]
    congr 1
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (upperRootMatrixGroup (K := K) a) :=
    IsPGroup.of_card hcard
  letI : Group.IsNilpotent (upperRootMatrixGroup (K := K) a) := hp.isNilpotent
  infer_instance

/-- Every upper-root translation fixes the distinguished ovoid point at
infinity, and this fixed-point property passes to the subgroup they generate.
This identifies the translation subgroup as a candidate point stabilizer
component for the Suzuki ovoid action. -/
theorem upperRootMatrixGroup_smul_infinity (a : ℕ)
    (g : upperRootMatrixGroup (K := K) a) :
    (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity := by
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K))).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hclosure : upperRootMatrixGroup (K := K) a ≤ S := by
    rw [upperRootMatrixGroup, Subgroup.closure_le]
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    rcases hA with ⟨u, v, rfl⟩
    exact upperRootOperator_smul_infinity a u v
  have hg : g.1 ∈ S := hclosure g.2
  change Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K))
      (ovoidInfinity (K := K)) at hg
  exact (MulAction.mem_stabilizer_iff.mp hg)

/-- The local Suzuki point-stabilizer carrier generated by the upper-root
operators and the torus operators. This is the operator analogue of the
root-torus subgroup appearing in the external Suzuki simplicity proof. -/
def suzukiPointStabilizerOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  upperRootMatrixGroup (K := K) a ⊔ suzukiTorusOperatorGroup (K := K) a

/-- Each torus operator normalizes the generated upper-root subgroup. The
finite Suzuki field hypothesis identifies that closure with its two-parameter
operator range. -/
theorem suzukiTorusOperator_mem_normalizer_upperRoot [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) (l : Kˣ) :
    suzukiTorusOperator a l ∈ Subgroup.normalizer
      (upperRootMatrixGroup (K := K) a : Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  have hforward (m : Kˣ) (y : Matrix.GeneralLinearGroup (Fin 4) K)
      (hy : y ∈ upperRootMatrixGroup (K := K) a) :
      suzukiTorusOperator a m * y * (suzukiTorusOperator a m)⁻¹ ∈
        upperRootMatrixGroup (K := K) a := by
    change y ∈ (upperRootMatrixGroup (K := K) a :
      Set (Matrix.GeneralLinearGroup (Fin 4) K)) at hy
    rw [upperRootMatrixGroup_eq_paramRange (K := K) a hK] at hy
    rcases hy with ⟨u, v, rfl⟩
    rw [suzukiTorusOperator_conj_upperRoot a pi hpi_sq hpi_formula m u v]
    exact Subgroup.subset_closure
      ⟨(m : K) * u, (m : K) * pi (m : K) * v, rfl⟩
  constructor
  · intro hx
    exact hforward l x hx
  · intro hx
    have hback := hforward l⁻¹
      (suzukiTorusOperator a l * x * (suzukiTorusOperator a l)⁻¹) hx
    have htorus_inv : suzukiTorusOperator a l⁻¹ =
        (suzukiTorusOperator a l)⁻¹ := (suzukiTorusOperator_inv a l).symm
    simpa [htorus_inv, mul_assoc] using hback

/-- The torus normalizes the generated upper-root subgroup, by closure from
the individual conjugation laws. -/
theorem suzukiTorusOperatorGroup_le_normalizer_upperRoot [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    suzukiTorusOperatorGroup (K := K) a ≤
      Subgroup.normalizer
        (upperRootMatrixGroup (K := K) a : Set (Matrix.GeneralLinearGroup (Fin 4) K)) := by
  rw [suzukiTorusOperatorGroup]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨l, rfl⟩
  exact suzukiTorusOperator_mem_normalizer_upperRoot
    (K := K) a hK pi hpi_sq hpi_formula l

/-- The upper-root subgroup is normal in the local root-torus point-stabilizer
candidate. -/
theorem upperRoot_subgroupOf_pointStabilizer_normal [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    ((upperRootMatrixGroup (K := K) a).subgroupOf
      (suzukiPointStabilizerOperatorGroup (K := K) a)).Normal := by
  rw [suzukiPointStabilizerOperatorGroup, sup_comm]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (H := suzukiTorusOperatorGroup (K := K) a)
    (N := upperRootMatrixGroup (K := K) a)
    (suzukiTorusOperatorGroup_le_normalizer_upperRoot
      (K := K) a hK pi hpi_sq hpi_formula)

/-- The local root-torus subgroup is solvable: its normal upper-root subgroup
is solvable, and the quotient is a surjective image of the abelian torus. -/
theorem suzukiPointStabilizerOperatorGroup_isSolvable [Finite K] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (pi : K ≃+* K)
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (a + 1))) :
    Group.IsSolvable (suzukiPointStabilizerOperatorGroup (K := K) a) := by
  let T := suzukiTorusOperatorGroup (K := K) a
  let U := upperRootMatrixGroup (K := K) a
  let B := suzukiPointStabilizerOperatorGroup (K := K) a
  letI : IsMulCommutative T := suzukiTorusOperatorGroup_isMulCommutative (K := K) a
  letI : Group.IsSolvable T := inferInstance
  letI : (U.subgroupOf B).Normal := by
    change ((upperRootMatrixGroup (K := K) a).subgroupOf
      (suzukiPointStabilizerOperatorGroup (K := K) a)).Normal
    exact upperRoot_subgroupOf_pointStabilizer_normal
      (K := K) a hK pi hpi_sq hpi_formula
  letI : Group.IsSolvable U := upperRootMatrixGroup_isSolvable (K := K) a hK
  let eU : U.subgroupOf B ≃* U := Subgroup.subgroupOfEquivOfLe le_sup_left
  letI : Group.IsSolvable (U.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := eU.toMonoidHom) eU.injective
  have hjoin : (U.subgroupOf B) ⊔ (T.subgroupOf B) = ⊤ := by
    change (U.subgroupOf (U ⊔ T)) ⊔ (T.subgroupOf (U ⊔ T)) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (U ⊔ T)
  let f : T →* B ⧸ U.subgroupOf B :=
    (QuotientGroup.mk' (U.subgroupOf B)).comp
      ((T.subgroupOf B).subtype.comp (Subgroup.subgroupOfEquivOfLe le_sup_right).symm.toMonoidHom)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) y
    have hb : b ∈ (U.subgroupOf B) ⊔ (T.subgroupOf B) := by
      rw [hjoin]
      exact Subgroup.mem_top b
    rcases (Subgroup.mem_sup_of_normal_left
      (s := U.subgroupOf B) (t := T.subgroupOf B) (x := b)).mp hb with
      ⟨u, hu, t, ht, hut⟩
    refine ⟨⟨t.1, ht⟩, ?_⟩
    change QuotientGroup.mk' (U.subgroupOf B) t =
      QuotientGroup.mk' (U.subgroupOf B) b
    rw [← hut]
    simp [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      QuotientGroup.eq_one_iff, hu]
  letI : Group.IsSolvable (B ⧸ U.subgroupOf B) := Group.isSolvable_of_surjective hf
  apply Group.isSolvable_of_ker_le_range (U.subgroupOf B).subtype
    (QuotientGroup.mk' (U.subgroupOf B))
  rw [QuotientGroup.ker_mk']
  rw [Subgroup.range_subtype]

/-- The root-torus operator subgroup fixes infinity, so it is contained in
the point stabilizer of the actual projective-space action. -/
theorem suzukiPointStabilizerOperatorGroup_le_stabilizer (a : ℕ) :
    suzukiPointStabilizerOperatorGroup (K := K) a ≤
      (MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))).comap
          Matrix.GeneralLinearGroup.toLin.toMonoidHom := by
  apply sup_le
  · intro g hg
    change Matrix.GeneralLinearGroup.toLin g ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact upperRootMatrixGroup_smul_infinity (K := K) a ⟨g, hg⟩
  · intro g hg
    change Matrix.GeneralLinearGroup.toLin g ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K))
        (ovoidInfinity (K := K))
    rw [MulAction.mem_stabilizer_iff]
    exact suzukiTorusOperatorGroup_smul_infinity (K := K) a ⟨g, hg⟩

/-- The upper-root operator subgroup acts transitively on the finite chart of
the Suzuki ovoid. In characteristic two, choose the two root parameters to
translate the input coordinates to the desired output coordinates. -/
theorem upperRootMatrixGroup_transitive_on_finite_chart
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (x y x' y' : K) :
    ∃ g : upperRootMatrixGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ovoidPoint pi x y = ovoidPoint pi x' y' := by
  let u : K := x + x'
  let v : K := y + y' + pi u * x'
  have hzero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hxx : x + x = 0 := by linear_combination x * hzero
  have hyy : y + y = 0 := by linear_combination y * hzero
  have hcross : pi u * x' + pi u * x' = 0 := by
    linear_combination (pi u * x') * hzero
  have hu : x + u = x' := by
    dsimp [u]
    calc
      x + (x + x') = (x + x) + x' := by ac_rfl
      _ = x' := by rw [hxx, zero_add]
  have hv : y + v + pi u * (x + u) = y' := by
    rw [hu]
    dsimp [v]
    linear_combination hyy + hcross
  refine ⟨⟨upperRootOperator a u v,
    Subgroup.subset_closure ⟨u, v, rfl⟩⟩, ?_⟩
  change (Matrix.GeneralLinearGroup.toLin
    (upperRootOperator a u v)).toLinearEquiv • ovoidPoint pi x y = _
  rw [upperRootOperator_smul_finite a pi hpi_sq hpi_formula]
  exact congrArg₂ (ovoidPoint pi) hu hv

/-- Every element of the upper-root operator subgroup preserves the Suzuki
ovoid. The finite-field hypothesis lets the generator's injective action on
the finite ovoid be upgraded from inclusion to equality, hence to membership
in the set stabilizer. -/
theorem upperRootMatrixGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1))) :
    ∀ g : upperRootMatrixGroup (K := K) a, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈
        ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens :
      {g : Matrix.GeneralLinearGroup (Fin 4) K |
        ∃ u v : K, g = upperRootOperator a u v} ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, rfl⟩
    exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
  have hclosure : upperRootMatrixGroup (K := K) a ≤ S := by
    rw [upperRootMatrixGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

/-- The subgroup generated by upper-root and antidiagonal Weyl operators,
both acting on the same four-dimensional module carrier. -/
def rootWeylOperatorGroup (a : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure
    ({g | ∃ u v : K, g = upperRootOperator a u v} ∪
      {suzukiWeylOperator (K := K)})

/-- The upper-root translations form a subgroup of the root-plus-Weyl
operator group. This makes their finite-chart transitivity available inside
the same noncommutative carrier used for the transitive ovoid action. -/
theorem upperRootMatrixGroup_le_rootWeylOperatorGroup (a : ℕ) :
    upperRootMatrixGroup (K := K) a ≤ rootWeylOperatorGroup (K := K) a := by
  rw [upperRootMatrixGroup, rootWeylOperatorGroup, Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

/-- The local root-plus-Weyl operator subgroup sends every Suzuki ovoid point
to the distinguished point at infinity. An upper-root translation sends a
finite chart point to `(0,0)`, and the Weyl operator sends that point to
infinity. This is an action result, not a simplicity claim. -/
theorem rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z =
          ovoidInfinity := by
  change z ∈ {ovoidInfinity} ∪
    Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz
  rcases hz with hz | ⟨⟨x, y⟩, rfl⟩
  · have hz' : z = ovoidInfinity := by simpa using hz
    subst z
    exact ⟨1, by simp [ovoidInfinity]⟩
  · let r : rootWeylOperatorGroup (K := K) a :=
      ⟨upperRootOperator a x y,
        Subgroup.subset_closure (Or.inl ⟨x, y, rfl⟩)⟩
    let w : rootWeylOperatorGroup (K := K) a :=
      ⟨suzukiWeylOperator (K := K),
        Subgroup.subset_closure (Or.inr rfl)⟩
    have hxx : x + x = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination x * htwo
    have hyy : y + y = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination y * htwo
    have hroot :
        (Matrix.GeneralLinearGroup.toLin
          (upperRootOperator a x y)).toLinearEquiv • ovoidPoint pi x y =
            ovoidPoint pi 0 0 := by
      simpa [hxx, hyy] using
        upperRootOperator_smul_finite a pi hpi_sq hpi_formula x y x y
    refine ⟨w * r, ?_⟩
    calc
      (Matrix.GeneralLinearGroup.toLin
          ((w * r : rootWeylOperatorGroup (K := K) a) :
            Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ovoidPoint pi x y =
        (Matrix.GeneralLinearGroup.toLin
            (w : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
              (r : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
            ovoidPoint pi x y) := by
          change (Matrix.GeneralLinearGroup.toLin
            ((w : Matrix.GeneralLinearGroup (Fin 4) K) *
              (r : Matrix.GeneralLinearGroup (Fin 4) K))).toLinearEquiv • _ = _
          rw [(Matrix.GeneralLinearGroup.toLin).map_mul,
            LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]
      _ = (Matrix.GeneralLinearGroup.toLin
            (suzukiWeylOperator (K := K))).toLinearEquiv •
          ovoidPoint pi 0 0 := by
            rw [hroot]
      _ = ovoidInfinity := suzukiWeylOperator_smul_zero pi

/-- The root-plus-Weyl subgroup acts transitively on the Suzuki ovoid under
the same field and automorphism hypotheses: move each of two points to
infinity, then compose one transporter with the inverse of the other. -/
theorem rootWeylOperatorGroup_transitive_on_ovoid
    [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (z z' : ℙ K (Fin 4 → K)) (hz : z ∈ ovoid pi) (hz' : z' ∈ ovoid pi) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z = z' := by
  obtain ⟨g, hg⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z hz
  obtain ⟨g', hg'⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z' hz'
  refine ⟨g'⁻¹ * g, ?_⟩
  calc
    (Matrix.GeneralLinearGroup.toLin
        ((g'⁻¹ * g : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z =
      (Matrix.GeneralLinearGroup.toLin
          (g'⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
            (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z) := by
        change (Matrix.GeneralLinearGroup.toLin
          (((g' : rootWeylOperatorGroup (K := K) a) :
            Matrix.GeneralLinearGroup (Fin 4) K)⁻¹ *
            (g : Matrix.GeneralLinearGroup (Fin 4) K))).toLinearEquiv • _ = _
        rw [(Matrix.GeneralLinearGroup.toLin).map_mul,
          LinearMap.GeneralLinearGroup.toLinearEquiv_mul, mul_smul]
    _ = (Matrix.GeneralLinearGroup.toLin
          (g'⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity := by rw [hg]
    _ = z' := by
      rw [← hg', (Matrix.GeneralLinearGroup.toLin).map_inv,
        LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
      exact inv_smul_smul _ _

/-- Every element in the root-plus-Weyl operator subgroup preserves the
projective ovoid over finite fields, under the explicit Suzuki norm-zero
property. -/
theorem rootWeylOperatorGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0) :
    ∀ g : rootWeylOperatorGroup (K := K) a, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens :
      ({g : Matrix.GeneralLinearGroup (Fin 4) K |
        ∃ u v : K, g = upperRootOperator a u v} ∪
        {suzukiWeylOperator (K := K)}) ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, rfl⟩ | hweyl
    · exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
    · have hA' : A = suzukiWeylOperator (K := K) := by simpa using hweyl
      subst A
      exact suzukiWeylOperator_maps_ovoid pi hpi_sq hnorm_zero z hz
  have hclosure : rootWeylOperatorGroup (K := K) a ≤ S := by
    rw [rootWeylOperatorGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

/-- The root-plus-Weyl operator group acts two-transitively on the Suzuki
ovoid, provided the explicit finite-field norm condition makes the ovoid
stable. The proof uses upper-root transitivity on the finite chart inside
the stabilizer of infinity, together with transitivity of the full group. -/
theorem rootWeylOperatorGroup_two_transitive_on_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z₁ z₂ z₃ z₄ : ℙ K (Fin 4 → K))
    (hz₁ : z₁ ∈ ovoid pi) (hz₂ : z₂ ∈ ovoid pi)
    (hz₃ : z₃ ∈ ovoid pi) (hz₄ : z₄ ∈ ovoid pi)
    (hne₁ : z₁ ≠ z₂) (hne₂ : z₃ ≠ z₄) :
    ∃ g : rootWeylOperatorGroup (K := K) a,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = z₃ ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ = z₄ := by
  let ρ : rootWeylOperatorGroup (K := K) a →*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
      (rootWeylOperatorGroup (K := K) a).subtype
  letI : MulAction (rootWeylOperatorGroup (K := K) a)
      (ℙ K (Fin 4 → K)) := MulAction.compHom _ ρ
  obtain ⟨g, hg₁⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z₁ hz₁
  obtain ⟨g', hg₃⟩ := rootWeylOperatorGroup_exists_map_ovoid_to_infinity
    a pi hpi_sq hpi_formula z₃ hz₃
  have hg₁' : g • z₁ = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = _
    exact hg₁
  have hg₃' : g' • z₃ = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (g' : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₃ = _
    exact hg₃
  have hz₂g : g • z₂ ∈ ovoid pi := by
    change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ ∈ ovoid pi
    exact rootWeylOperatorGroup_smul_mem_ovoid a pi hpi_sq hpi_formula
      hnorm_zero g z₂ hz₂
  have hz₄g' : g' • z₄ ∈ ovoid pi := by
    change (Matrix.GeneralLinearGroup.toLin
      (g' : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₄ ∈ ovoid pi
    exact rootWeylOperatorGroup_smul_mem_ovoid a pi hpi_sq hpi_formula
      hnorm_zero g' z₄ hz₄
  have hne₂g : g • z₂ ≠ ovoidInfinity := by
    intro h
    apply hne₁
    have heq : g • z₁ = g • z₂ := hg₁.trans h.symm
    have heq' := congrArg (fun z => g⁻¹ • z) heq
    simpa using heq'
  have hne₄g' : g' • z₄ ≠ ovoidInfinity := by
    intro h
    apply hne₂
    have heq : g' • z₃ = g' • z₄ := hg₃.trans h.symm
    have heq' := congrArg (fun z => g'⁻¹ • z) heq
    simpa using heq'
  have hcoord₂ : ∃ x y : K, g • z₂ = ovoidPoint pi x y := by
    change g • z₂ ∈ {ovoidInfinity} ∪
      Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz₂g
    rcases hz₂g with hi | ⟨⟨x, y⟩, h⟩
    · exact (hne₂g hi).elim
    · exact ⟨x, y, h.symm⟩
  have hcoord₄ : ∃ x y : K, g' • z₄ = ovoidPoint pi x y := by
    change g' • z₄ ∈ {ovoidInfinity} ∪
      Set.range (fun w : K × K => ovoidPoint pi w.1 w.2) at hz₄g'
    rcases hz₄g' with hi | ⟨⟨x, y⟩, h⟩
    · exact (hne₄g' hi).elim
    · exact ⟨x, y, h.symm⟩
  obtain ⟨x, y, hxy⟩ := hcoord₂
  obtain ⟨x', y', hx'y'⟩ := hcoord₄
  obtain ⟨k₀, hk₀⟩ := upperRootMatrixGroup_transitive_on_finite_chart
    a pi hpi_sq hpi_formula x y x' y'
  let k : rootWeylOperatorGroup (K := K) a :=
    ⟨(k₀ : Matrix.GeneralLinearGroup (Fin 4) K),
      upperRootMatrixGroup_le_rootWeylOperatorGroup (K := K) a k₀.property⟩
  have hk : k • (g • z₂) = g' • z₄ := by
    change (Matrix.GeneralLinearGroup.toLin
      (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        (g • z₂) = g' • z₄
    calc
      _ = (Matrix.GeneralLinearGroup.toLin
          (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
            ovoidPoint pi x y := congrArg _ hxy
      _ = ovoidPoint pi x' y' := hk₀
      _ = g' • z₄ := hx'y'.symm
  have hkinf : k • ovoidInfinity (K := K) = ovoidInfinity (K := K) := by
    change (Matrix.GeneralLinearGroup.toLin
      (k₀ : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv •
        ovoidInfinity (K := K) = ovoidInfinity (K := K)
    exact upperRootMatrixGroup_smul_infinity (K := K) a k₀
  refine ⟨g'⁻¹ * k * g, ?_, ?_⟩
  · change (g'⁻¹ * k * g) • z₁ = z₃
    rw [mul_smul, mul_smul, hg₁', hkinf]
    rw [← hg₃']
    exact inv_smul_smul g' z₃
  · change (g'⁻¹ * k * g) • z₂ = z₄
    rw [mul_smul, mul_smul, hk]
    exact inv_smul_smul g' z₄

/-- The root-plus-Weyl subgroup is genuinely noncommutative: the upper-root
operator at `(1,0)` and the antidiagonal Weyl operator differ in their
`(0,0)` matrix entries after multiplication in the two orders. -/
theorem suzukiUpperMatrixGroup_smul_mem_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0) :
    ∀ g : Chevalley.suzukiUpperMatrixGroup a K, ∀ z, z ∈ ovoid pi →
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ ovoid pi := by
  let O := ovoid pi
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hfinite : O.Finite := Set.toFinite O
  have hgens : Chevalley.suzukiUpperMatrixGenerators a K ⊆ S := by
    intro A hA
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K} at hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite]
    apply Set.smul_set_subset_iff.2
    rintro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    rcases hA with ⟨u, v, hroot⟩ | ⟨l, htorus⟩ | hw
    · have hAeq : A = upperRootOperator a u v := by
        apply Units.ext
        apply Matrix.transpose_injective
        simpa [upperRootOperator, suzukiSGL] using hroot
      rw [hAeq]
      exact upperRootOperator_maps_ovoid a pi u v hpi_sq hpi_formula z hz
    · have hAeq : A = suzukiTorusOperator a l := by
        have hmat : (A : Matrix (Fin 4) (Fin 4) K) = suzukiD a l := by
          calc
            (A : Matrix (Fin 4) (Fin 4) K) =
                ((A : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
            _ = (suzukiD a l).transpose := congrArg Matrix.transpose htorus
            _ = suzukiD a l := by simp [suzukiD]
        apply Units.ext
        simpa [suzukiTorusOperator] using hmat
      rw [hAeq]
      exact suzukiTorusOperator_maps_ovoid a pi hpi_sq hpi_formula l z hz
    · have hAeq : A = suzukiWeylOperator (K := K) := by
        have hmat : (A : Matrix (Fin 4) (Fin 4) K) = Chevalley.suzukiW K := by
          calc
            (A : Matrix (Fin 4) (Fin 4) K) =
                ((A : Matrix (Fin 4) (Fin 4) K).transpose).transpose := by simp
            _ = (Chevalley.suzukiW K).transpose := congrArg Matrix.transpose hw
            _ = Chevalley.suzukiW K := by
              ext i j
              simp [Chevalley.suzukiW, Nat.add_comm]
        apply Units.ext
        simpa [suzukiWeylOperator, suzukiWeylMatrix, Chevalley.suzukiW] using hmat
      rw [hAeq]
      exact suzukiWeylOperator_maps_ovoid pi hpi_sq hnorm_zero z hz
  have hclosure : Chevalley.suzukiUpperMatrixGroup a K ≤ S := by
    rw [Chevalley.suzukiUpperMatrixGroup, Subgroup.closure_le]
    exact hgens
  intro g z hz
  have hgS : Matrix.GeneralLinearGroup.toLin (g : Matrix.GeneralLinearGroup (Fin 4) K) ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O := hclosure g.property
  have hsubset : Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hfinite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
      (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

theorem rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (a : ℕ) :
    rootWeylOperatorGroup (K := K) a ≤ Chevalley.suzukiUpperMatrixGroup a K := by
  rw [rootWeylOperatorGroup, Subgroup.closure_le]
  intro A hA
  rcases hA with ⟨u, v, hA⟩ | hA
  · apply Subgroup.subset_closure
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
    subst A
    left
    exact ⟨u, v, by simp [upperRootOperator, suzukiSGL]⟩
  · apply Subgroup.subset_closure
    change ((A : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).transpose ∈
      {M : Matrix (Fin 4) (Fin 4) K |
        (∃ u v : K, M = suzukiS a u v) ∨
          (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
    have hAeq : A = suzukiWeylOperator (K := K) := by simpa using hA
    subst A
    right
    right
    ext i j
    simp [suzukiWeylOperator, suzukiWeylMatrix, Chevalley.suzukiW,
      Nat.add_comm]

/-- Two-transitivity transfers from the root-plus-Weyl subgroup to the full
upper-orientation Suzuki operator group, which also contains the torus. -/
theorem suzukiUpperMatrixGroup_two_transitive_on_ovoid
    [Finite K] [CharP K 2] (a : ℕ) (pi : K ≃+* K)
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (hnorm_zero : ∀ x y : K,
      x * y + pi x * x ^ 2 + pi y = 0 → x = 0 ∧ y = 0)
    (z₁ z₂ z₃ z₄ : ℙ K (Fin 4 → K))
    (hz₁ : z₁ ∈ ovoid pi) (hz₂ : z₂ ∈ ovoid pi)
    (hz₃ : z₃ ∈ ovoid pi) (hz₄ : z₄ ∈ ovoid pi)
    (hne₁ : z₁ ≠ z₂) (hne₂ : z₃ ≠ z₄) :
    ∃ g : Chevalley.suzukiUpperMatrixGroup a K,
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₁ = z₃ ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : Matrix.GeneralLinearGroup (Fin 4) K)).toLinearEquiv • z₂ = z₄ := by
  obtain ⟨g, hg₁, hg₂⟩ := rootWeylOperatorGroup_two_transitive_on_ovoid
    (K := K) a pi hpi_sq hpi_formula hnorm_zero
    z₁ z₂ z₃ z₄ hz₁ hz₂ hz₃ hz₄ hne₁ hne₂
  let g' : Chevalley.suzukiUpperMatrixGroup a K :=
    ⟨g, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a g.property⟩
  refine ⟨g', ?_, ?_⟩
  · simpa [g'] using hg₁
  · simpa [g'] using hg₂

theorem rootWeylOperatorGroup_noncommuting_pair (a : ℕ) :
    ∃ g h : rootWeylOperatorGroup (K := K) a, g * h ≠ h * g := by
  let g : rootWeylOperatorGroup (K := K) a :=
    ⟨upperRootOperator a 1 0,
      Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)⟩
  let h : rootWeylOperatorGroup (K := K) a :=
    ⟨suzukiWeylOperator (K := K), Subgroup.subset_closure (Or.inr rfl)⟩
  refine ⟨g, h, ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g :=
    congrArg (fun x : rootWeylOperatorGroup (K := K) a =>
      (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  have hmat :
      ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((h : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((h : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((g : rootWeylOperatorGroup (K := K) a) :
          Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    congrArg (fun x : Matrix.GeneralLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hGL
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hmat
  norm_num [g, h, upperRootOperator, suzukiSGL, suzukiS, suzukiN,
    suzukiWeylOperator, suzukiWeylMatrix, Matrix.mul_apply,
    Fin.sum_univ_four] at h00

/-- The full upper-orientation Suzuki operator group is noncommutative. The
root/Weyl witness embeds into the group that also contains the torus. -/
theorem suzukiUpperMatrixGroup_noncommuting_pair (a : ℕ) :
    ∃ g h : ↥(Chevalley.suzukiUpperMatrixGroup a K), g * h ≠ h * g := by
  obtain ⟨g, h, hgh⟩ := rootWeylOperatorGroup_noncommuting_pair (K := K) a
  let g' : ↥(Chevalley.suzukiUpperMatrixGroup a K) :=
    ⟨g, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a g.property⟩
  let h' : ↥(Chevalley.suzukiUpperMatrixGroup a K) :=
    ⟨h, rootWeylOperatorGroup_le_suzukiUpperMatrixGroup (K := K) a h.property⟩
  refine ⟨g', h', ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g := by
    simpa [g', h'] using congrArg
      (fun x : ↥(Chevalley.suzukiUpperMatrixGroup a K) =>
        (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  apply hgh
  apply Subtype.ext
  exact hGL

/-- The upper-root operator subgroup is genuinely noncommutative: the
operators with parameters `(1,0)` and `(c,0)` have different `(0,2)` entries
after multiplication in the two orders whenever `pi c ≠ c`. -/
theorem upperRootMatrixGroup_noncommuting_pair [CharP K 2] (a : ℕ)
    (pi : K ≃+* K) (hpi_formula : ∀ x, pi x = x ^ (2 ^ (a + 1)))
    (c : K) (hc : pi c ≠ c) :
    ∃ g h : upperRootMatrixGroup (K := K) a, g * h ≠ h * g := by
  let g : upperRootMatrixGroup (K := K) a :=
    ⟨upperRootOperator a 1 0, Subgroup.subset_closure ⟨1, 0, rfl⟩⟩
  let h : upperRootMatrixGroup (K := K) a :=
    ⟨upperRootOperator a c 0, Subgroup.subset_closure ⟨c, 0, rfl⟩⟩
  refine ⟨g, h, ?_⟩
  intro hcomm
  have hGL : (g : Matrix.GeneralLinearGroup (Fin 4) K) * h =
      (h : Matrix.GeneralLinearGroup (Fin 4) K) * g :=
    congrArg (fun x : upperRootMatrixGroup (K := K) a =>
      (x : Matrix.GeneralLinearGroup (Fin 4) K)) hcomm
  have hmat : ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((h : upperRootMatrixGroup (K := K) a) :
        Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((h : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((g : upperRootMatrixGroup (K := K) a) :
        Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    exact congrArg (fun x : Matrix.GeneralLinearGroup (Fin 4) K =>
      (x : Matrix (Fin 4) (Fin 4) K)) hGL
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 2) hmat
  have hpi_c_eq_c : pi c = c := by
    simpa [g, h, upperRootOperator, suzukiSGL, suzukiS, suzukiN,
      Matrix.mul_apply, Fin.sum_univ_four, hpi_formula] using h02
  exact hc hpi_c_eq_c

end InfoGeometry.Exceptional.CFSGPort.Suzuki

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. Module and namespace paths are
adapted for this repository's Lean 4.34.1 / mathlib pin.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroupsTriangular
public import InfoGeometry.Exceptional.CFSGPort.MatrixInverseTranspose

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- Exceptional Ree/Tits group families present in the CFSG catalog. -/
inductive ExceptionalReeTag
  | twistedG2 | twistedF4 | tits
  deriving DecidableEq, Repr

/-- Exceptional finite groups of Lie type represented in the CFSG catalog. -/
inductive ExceptionalLieFamily
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | tits
  deriving DecidableEq, Repr

/-- The adjoint Chevalley group modulo its center. -/
abbrev AdjointQuotient (τ : Tag) (K : Type) [Field K] : Type :=
  ↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)

/-- The derived subgroup of `H` modulo its center. -/
abbrev DerivedCentralQuotient {M : Type} [Group M] (H : Subgroup M) : Type :=
  ↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆

/-- The fixed subgroup of a Chevalley group under a diagram and field twist. -/
def twistedFixedGroup (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (ModGL t.tag K) :=
  adjointGroup t.tag K ⊓ MonoidHom.eqLocus (twistHom t K σ) (MonoidHom.id _)

/-- The finite-field adjoint Chevalley group for any root tag in the port. -/
abbrev UntwistedChevalleyGroup (τ : Tag) (K : Type) [Field K] :=
  AdjointQuotient τ K

/-- The central derived quotient used in a diagram-twisted Chevalley model. -/
abbrev TwistedChevalleyGroup (t : TwistTag) (K : Type) [Field K]
    (σ : K →+* K) :=
  DerivedCentralQuotient (twistedFixedGroup t K σ)

/-- A finite-field adjoint Chevalley model of cardinality `q`. -/
@[expose] def UntwistedChevalleyModel (G : Type) [Group G] (τ : Tag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (G ≃* AdjointQuotient τ K)

/-- A finite-field diagram/Frobenius-twisted Chevalley model. -/
@[expose] def TwistedChevalleyModel (G : Type) [Group G] (t : TwistTag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ t.order ∧
    ∃ σ : K →+* K, (∀ c, σ c = c ^ q) ∧
      Nonempty (G ≃* TwistedChevalleyGroup t K σ)

/-- The untwisted and diagram-twisted exceptional Chevalley families. -/
@[expose] def ChevalleyExceptionalModel (G : Type) [Group G] (family : ExceptionalLieFamily)
    (p f : ℕ) : Prop :=
  match family with
  | .G2 => UntwistedChevalleyModel G .G2 (p ^ f)
  | .F4 => UntwistedChevalleyModel G .F4 (p ^ f)
  | .E6 => UntwistedChevalleyModel G .E6 (p ^ f)
  | .E7 => UntwistedChevalleyModel G .E7 (p ^ f)
  | .E8 => UntwistedChevalleyModel G .E8 (p ^ f)
  | .twistedE6 => TwistedChevalleyModel G .E6 (p ^ f)
  | .trialityD4 => TwistedChevalleyModel G .D4 (p ^ f)
  | _ => False

/-- The paired root-generator relation subgroup used for Ree and Tits groups. -/
def reeRelationGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K × ModGL τ K) :=
  Subgroup.closure {gh | ∃ (i : Fin τ.rank) (c : K),
    ((gh.1 : Module.End K (RootModule τ K)) = xOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = xOp τ K (ρ i) (c ^ e i)) ∨
      ((gh.1 : Module.End K (RootModule τ K)) = yOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = yOp τ K (ρ i) (c ^ e i))}

/-- The fixed subgroup extracted from the paired Ree/Tits root relations. -/
def reeFixedGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓
    (reeRelationGroup τ K ρ e).comap ((MonoidHom.id _).prod (MonoidHom.id _))

@[expose] def reeG2Perm : Equiv.Perm (Fin Tag.G2.rank) :=
  (Equiv.swap 0 1 : Equiv.Perm (Fin 2))

@[expose] def reeF4Perm : Equiv.Perm (Fin Tag.F4.rank) :=
  (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))

@[expose] def reeG2Long : Finset (Fin Tag.G2.rank) :=
  ({0} : Finset (Fin 2))

@[expose] def reeF4Long : Finset (Fin Tag.F4.rank) :=
  ({0, 1} : Finset (Fin 4))

/-- A concrete quotient model for the exceptional Ree/Tits construction. -/
@[expose] def ReeTitsRelationModel (G : Type) [Group G] (τ : Tag)
    (ρ : Equiv.Perm (Fin τ.rank)) (longRoots : Finset (Fin τ.rank))
    (p f a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
    Nonempty (G ≃* DerivedCentralQuotient
      (reeFixedGroup τ K ρ fun i => if i ∈ longRoots then p ^ a else p ^ (a + 1)))

-- Suzuki's three root-generator matrices over a field of characteristic two.
section Suzuki

variable (a : ℕ) {K : Type} [Field K]

@[expose] def suzukiN (u v : K) : K :=
  u ^ (2 ^ (a + 1) + 2) + u * v + v ^ 2 ^ (a + 1)

@[expose] def suzukiS (u v : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
    u, 1, 0, 0;
    v, u ^ 2 ^ (a + 1), 1, 0;
    suzukiN a u v, u ^ (2 ^ (a + 1) + 1) + v, u, 1]

/-- Frobenius identities for the Suzuki parameter exponent in a finite field
of the required cardinality. Ported from
`CFSG.LieType.Ree.suzuki_frob_data`. -/
theorem suzukiFrobData [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (2 : K) = 0 ∧
      (∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1)) ∧
      ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have h2 : (2 : K) = 0 := by
    exact_mod_cast CharP.cast_eq_zero K 2
  have hadd : ∀ x y : K,
      (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) := by
    intro x y
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact add_pow_char_pow x y 2 (a + 1)
  have hpow : ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := by
    intro x
    have hq : ∀ x : K, x ^ 2 ^ (2 * a + 1) = x := by
      intro x
      rw [← hcard, FiniteField.pow_card]
    rw [← pow_mul,
      show 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (2 * a + 1) * 2 by ring,
      pow_mul, hq]
  exact ⟨h2, hadd, hpow⟩

/-- Multiplication of the local Suzuki lower-root matrices. This is the
parameter law underlying the noncommutative root subgroup; it is ported from
`CFSG.LieType.Ree.suzukiS_mul`. -/
theorem suzukiS_mul [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u v c d : K) :
    suzukiS a u v * suzukiS a c d =
      suzukiS a (u + c) (v + d + u ^ 2 ^ (a + 1) * c) := by
  obtain ⟨h2, hadd, hθθ⟩ := suzukiFrobData a hK
  have hF2 : (v + d + u ^ 2 ^ (a + 1) * c) ^ 2 ^ (a + 1) =
      v ^ 2 ^ (a + 1) + d ^ 2 ^ (a + 1) + u ^ 2 * c ^ 2 ^ (a + 1) := by
    rw [hadd, hadd, mul_pow, hθθ]
  have hN : suzukiN a (u + c) (v + d + u ^ 2 ^ (a + 1) * c) =
      suzukiN a u v + (u ^ (2 ^ (a + 1) + 1) + v) * c + u * d + suzukiN a c d := by
    rw [suzukiN, suzukiN, suzukiN, hF2, pow_add (u + c), hadd]
    linear_combination (u ^ 2 ^ (a + 1) * u * c + u ^ 2 ^ (a + 1) * c ^ 2 +
      c ^ 2 ^ (a + 1) * u ^ 2 + c ^ 2 ^ (a + 1) * c * u) * h2
  have h31 : (u + c) ^ (2 ^ (a + 1) + 1) +
      (v + d + u ^ 2 ^ (a + 1) * c) =
      u ^ (2 ^ (a + 1) + 1) + v + u * c ^ 2 ^ (a + 1) +
        (c ^ (2 ^ (a + 1) + 1) + d) := by
    rw [pow_succ, hadd]
    linear_combination u ^ 2 ^ (a + 1) * c * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, Matrix.mul_apply, Fin.sum_univ_four, hadd, hN, h31]
  ring

/-- The noncommutative upper-root Suzuki matrix as an invertible operator. -/
@[expose] public def suzukiSGL (u v : K) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v).transpose (by
    have htri : (suzukiS a u v).IsLowerTriangular := by
      intro i j hij
      change i < j at hij
      fin_cases i <;> fin_cases j <;> simp_all [suzukiS, suzukiN]
    rw [Matrix.det_transpose, Matrix.det_of_isLowerTriangular _ htri]
    simp [suzukiS, Fin.prod_univ_four])

/-- Multiplication law for the actual upper-root general-linear operators.
The reversed cross-term is forced by transposing the external lower-root
presentation. -/
theorem suzukiSGL_mul [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u v c d : K) :
    suzukiSGL a u v * suzukiSGL a c d =
      suzukiSGL a (u + c) (v + d + c ^ 2 ^ (a + 1) * u) := by
  apply Units.ext
  change (suzukiS a u v).transpose * (suzukiS a c d).transpose =
    (suzukiS a (u + c) (v + d + c ^ 2 ^ (a + 1) * u)).transpose
  rw [← Matrix.transpose_mul, suzukiS_mul a hK c d u v]
  congr 2
  · exact add_comm c u
  · exact congrArg (fun x : K => x + c ^ 2 ^ (a + 1) * u) (add_comm d v)

/-- The upper-root operator parameters are recovered from matrix entries
`(0,1)` and `(0,2)`, so this parameterization is faithful. -/
theorem suzukiSGL_injective : Function.Injective
    (fun p : K × K => suzukiSGL a p.1 p.2) := by
  intro p q hpq
  have hmat := congrArg
    (fun g : Matrix.GeneralLinearGroup (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hpq
  have h01 := congrFun (congrFun hmat 0) 1
  have h02 := congrFun (congrFun hmat 0) 2
  simp [suzukiSGL, Matrix.transpose_apply, suzukiS] at h01 h02
  exact Prod.ext h01 h02

/-- The zero-parameter upper-root operator is the identity. -/
theorem suzukiSGL_zero_zero : suzukiSGL a (0 : K) 0 = 1 := by
  apply Units.ext
  change (suzukiS a 0 0).transpose = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN]

/-- Inverse formula for the transpose-presentation Suzuki root operators. -/
theorem suzukiSGL_inv [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u v : K) :
    (suzukiSGL a u v)⁻¹ =
      suzukiSGL a u (v + u ^ (2 ^ (a + 1) + 1)) := by
  rw [inv_eq_iff_mul_eq_one, suzukiSGL_mul a hK]
  rw [← suzukiSGL_zero_zero (a := a)]
  have hparam :
      (u + u, v + (v + u ^ (2 ^ (a + 1) + 1)) +
        u ^ (2 ^ (a + 1)) * u) = (0, 0) := by
    apply Prod.ext
    · have h2 := (suzukiFrobData a hK).1
      linear_combination u * h2
    · have h2 := (suzukiFrobData a hK).1
      rw [pow_succ]
      linear_combination (v + u ^ (2 ^ (a + 1)) * u) * h2
  change (fun p : K × K => suzukiSGL a p.1 p.2)
      (u + u, v + (v + u ^ (2 ^ (a + 1) + 1)) +
        u ^ (2 ^ (a + 1)) * u) =
    (fun p : K × K => suzukiSGL a p.1 p.2) (0, 0)
  rw [hparam]

@[expose] def suzukiD (l : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)]

/-- Convert the integral Suzuki torus exponent to its natural-number form. -/
theorem zpow_two_pow_eq (l : Kˣ) :
    l ^ (2 ^ a : ℤ) = l ^ (2 ^ a : ℕ) := by
  rw [show (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]

/-- Diagonal form of the Suzuki torus operator. This exposes its four weights
in natural-power coordinates for the local root-conjugation calculation. -/
theorem suzukiD_eq (l : Kˣ) :
    suzukiD a l = Matrix.diagonal
      ![(l : K) * (l : K) ^ 2 ^ a, (l : K) ^ 2 ^ a,
        ((l : K) ^ 2 ^ a)⁻¹, ((l : K) * (l : K) ^ 2 ^ a)⁻¹] := by
  rw [suzukiD]
  congr 1
  ext i
  have h1 : l ^ (1 + (2 ^ a : ℤ)) = l * l ^ (2 ^ a : ℕ) := by
    rw [_root_.zpow_add, zpow_one, zpow_two_pow_eq]
  have h2 : l ^ (-(2 ^ a : ℤ)) = (l ^ (2 ^ a : ℕ))⁻¹ := by
    rw [_root_.zpow_neg, zpow_two_pow_eq]
  have h3 : l ^ (-1 - (2 ^ a : ℤ)) = (l * l ^ (2 ^ a : ℕ))⁻¹ := by
    rw [show -1 - (2 ^ a : ℤ) = -(1 + 2 ^ a) by ring,
      _root_.zpow_neg, h1]
  fin_cases i <;> simp [h1, h2, h3, zpow_two_pow_eq]

/-- The Suzuki torus parameterization is multiplicative. -/
theorem suzukiD_mul (l μ : Kˣ) :
    suzukiD a l * suzukiD a μ = suzukiD a (l * μ) := by
  rw [suzukiD, suzukiD, suzukiD, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_zpow, mul_comm]

/-- The identity parameter gives the identity Suzuki torus matrix. -/
theorem suzukiD_one : suzukiD a (1 : Kˣ) = 1 := by
  rw [suzukiD, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def suzukiW (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

private def suzukiSUnit (a : ℕ) (K : Type) [Field K] :
    Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a (1 : K) 0) (by
    have htri : (suzukiS a (1 : K) 0).IsLowerTriangular := by
      intro i j hij
      change i < j at hij
      fin_cases i <;> fin_cases j <;> simp_all [suzukiS, suzukiN]
    rw [Matrix.det_of_isLowerTriangular _ htri]
    simp [suzukiS, Fin.prod_univ_four])

private def suzukiWUnit (K : Type) [Field K] :
    Matrix.GeneralLinearGroup (Fin 4) K :=
  { val := suzukiW K
    inv := suzukiW K
    val_inv := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [suzukiW, Matrix.mul_apply, Fin.sum_univ_four] }

@[expose] def suzukiMatrixGenerators (a : ℕ) (K : Type) [Field K] :
    Set (Matrix.GeneralLinearGroup (Fin 4) K) :=
  {g | (∃ u v : K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v) ∨
    (∃ l : Kˣ, (g : Matrix (Fin 4) (Fin 4) K) = suzukiD a l) ∨
    (g : Matrix (Fin 4) (Fin 4) K) = suzukiW K}

@[expose] def suzukiUpperMatrixGenerators (a : ℕ) (K : Type) [Field K] :
    Set (Matrix.GeneralLinearGroup (Fin 4) K) :=
  {g | ((g : Matrix (Fin 4) (Fin 4) K).transpose) ∈
    {A : Matrix (Fin 4) (Fin 4) K |
      (∃ u v : K, A = suzukiS a u v) ∨
        (∃ l : Kˣ, A = suzukiD a l) ∨ A = suzukiW K}}

@[expose] def suzukiMatrixGroup (a : ℕ) (K : Type) [Field K] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure (suzukiMatrixGenerators a K)

@[expose] def suzukiUpperMatrixGroup (a : ℕ) (K : Type) [Field K] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
  Subgroup.closure (suzukiUpperMatrixGenerators a K)

/-- The diagonal Suzuki torus generator has determinant one. -/
theorem suzukiD_det (a : ℕ) (K : Type) [Field K] (l : Kˣ) :
    (suzukiD a l).det = 1 := by
  have h : l ^ (1 + (2 ^ a : ℤ)) * l ^ (2 ^ a : ℤ) * l ^ (-(2 ^ a : ℤ)) *
      l ^ (-1 - (2 ^ a : ℤ)) = 1 := by
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    ring_nf
    exact zpow_zero l
  rw [suzukiD, Matrix.det_diagonal, Fin.prod_univ_four]
  change ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (2 ^ a : ℤ) : Kˣ) : K) *
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h, Units.val_one]

/-- Every Suzuki torus matrix is a generator of the full Suzuki matrix group.
This keeps the diagonal torus inside the same noncommutative operator group
as the root and Weyl generators. -/
theorem suzukiD_mem_suzukiMatrixGroup (a : ℕ) (K : Type) [Field K] (l : Kˣ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l)
        (by rw [suzukiD_det]; exact one_ne_zero) ∈ suzukiMatrixGroup a K := by
  apply Subgroup.subset_closure
  right
  left
  refine ⟨l, ?_⟩
  rfl

/-- The locally ported inverse-transpose equivalence transports the upper-root
Suzuki matrix presentation to the lower-root operator presentation. -/
theorem suzukiUpperMatrixGroup_inverseTranspose (a : ℕ) (K : Type) [Field K] :
    (suzukiUpperMatrixGroup a K).map
      Matrix.GeneralLinearGroup.inverseTranspose.toMonoidHom = suzukiMatrixGroup a K := by
  let e : Matrix.GeneralLinearGroup (Fin 4) K ≃*
      Matrix.GeneralLinearGroup (Fin 4) K := Matrix.GeneralLinearGroup.inverseTranspose
  let S := suzukiUpperMatrixGenerators a K
  let T := suzukiMatrixGenerators a K
  have hsets : e '' S⁻¹ = T := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [Set.mem_inv] at hA
      change (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).transpose) ∈
        {M : Matrix (Fin 4) (Fin 4) K |
          (∃ u v : K, M = suzukiS a u v) ∨
            (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K} at hA
      change ((e A : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) ∈
        {M : Matrix (Fin 4) (Fin 4) K |
          (∃ u v : K, M = suzukiS a u v) ∨
            (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
      dsimp only [e]
      rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
      simpa using hA
    · intro hB
      change (B : Matrix (Fin 4) (Fin 4) K) ∈
        {M : Matrix (Fin 4) (Fin 4) K |
          (∃ u v : K, M = suzukiS a u v) ∨
            (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K} at hB
      refine ⟨e.symm B, ?_, e.apply_symm_apply B⟩
      rw [Set.mem_inv]
      change ((((e.symm B)⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).transpose) ∈
        {M : Matrix (Fin 4) (Fin 4) K |
          (∃ u v : K, M = suzukiS a u v) ∨
            (∃ l : Kˣ, M = suzukiD a l) ∨ M = suzukiW K}
      rw [Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_inverseTranspose, e.apply_symm_apply]
      exact hB
  change (Subgroup.closure S).map e.toMonoidHom = Subgroup.closure T
  rw [← Subgroup.closure_inv S, MonoidHom.map_closure]
  exact congrArg Subgroup.closure hsets

/-- The root operator with parameters `(1,0)` and the antidiagonal Weyl
operator do not commute in the concrete Suzuki matrix subgroup. -/
private theorem suzukiMatrixGroup_noncommuting_pair (a : ℕ) (K : Type) [Field K] :
    ∃ g h : ↥(suzukiMatrixGroup a K), g * h ≠ h * g := by
  let g : ↥(suzukiMatrixGroup a K) :=
    ⟨suzukiSUnit a K, Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)⟩
  let h : ↥(suzukiMatrixGroup a K) :=
    ⟨suzukiWUnit K, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
  refine ⟨g, h, ?_⟩
  intro he
  have hmat := congrArg (fun x : ↥(suzukiMatrixGroup a K) =>
    ((x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) he
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hmat
  norm_num [g, h, suzukiSUnit, suzukiWUnit, suzukiS, suzukiW, suzukiN,
    Matrix.mul_apply, Fin.sum_univ_four] at h00

/-- The Suzuki group acting faithfully by noncommutative linear operators on
the four dimensional coordinate module. The displayed Suzuki generators are
matrix coordinates for these operators; the group carrier itself is the
general linear group of endomorphisms. -/
@[expose] def suzukiGroup (a : ℕ) (K : Type) [Field K] :
    Subgroup (LinearMap.GeneralLinearGroup K (Fin 4 → K)) :=
  (suzukiMatrixGroup a K).map
    (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4)))

/-- The Suzuki family has a noncommuting pair in its actual linear-operator
group on the four-dimensional module. -/
theorem suzukiGroup_noncommuting_pair (a : ℕ) (K : Type) [Field K] :
    ∃ g h : ↥(suzukiGroup a K), g * h ≠ h * g := by
  obtain ⟨g, h, hgh⟩ := suzukiMatrixGroup_noncommuting_pair a K
  let e := Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
  let g' : ↥(suzukiGroup a K) := ⟨e g, by
    change e g ∈ (suzukiMatrixGroup a K).map e.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨(g : Matrix.GeneralLinearGroup (Fin 4) K), g.property, rfl⟩⟩
  let h' : ↥(suzukiGroup a K) := ⟨e h, by
    change e h ∈ (suzukiMatrixGroup a K).map e.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨(h : Matrix.GeneralLinearGroup (Fin 4) K), h.property, rfl⟩⟩
  refine ⟨g', h', ?_⟩
  intro he'
  have hlin : e (g * h) = e (h * g) := by
    simpa [g', h'] using congrArg Subtype.val he'
  apply hgh
  apply Subtype.ext
  exact e.injective hlin

/-- The operator-carrier Suzuki group is isomorphic to its matrix-coordinate
generator subgroup. This records faithfulness of the coordinate realization
without exposing a second public group model. -/
theorem exists_suzuki_coordinate_equiv (a : ℕ) (K : Type) [Field K] :
    ∃ H : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K),
      Nonempty (↥(suzukiGroup a K) ≃* ↥H) := by
  let H := suzukiMatrixGroup a K
  let e := Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 4))
  refine ⟨H, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).symm

end Suzuki

/-- The finite-field Suzuki group model, with its defining parameter bounds. -/
@[expose] def SuzukiExceptionalModel (G : Type) [Group G] (p f : ℕ) : Prop :=
  p = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧ Nonempty (G ≃* suzukiGroup a K)

/-- Prime and characteristic restrictions used by the CFSG Ree/Tits catalog. -/
def ReeTitsAdmissible (kind : ExceptionalReeTag) (p f : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ f ∧
    match kind with
    | .twistedG2 => p = 3 ∧ Odd f ∧ 3 ≤ f
    | .twistedF4 => p = 2 ∧ Odd f ∧ 3 ≤ f
    | .tits => p = 2 ∧ f = 1

/-- Prime and field-size restrictions from CFSG's exceptional Lie catalog. -/
@[expose] def ChevalleyExceptionalAdmissible (family : ExceptionalLieFamily) (p f : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ f ∧
    match family with
    | .G2 => 3 ≤ p ^ f
    | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 => True
    | .twistedB2 => p = 2 ∧ Odd f ∧ 3 ≤ f
    | .twistedG2 => p = 3 ∧ Odd f ∧ 3 ≤ f
    | .twistedF4 => p = 2 ∧ Odd f ∧ 3 ≤ f
    | .tits => p = 2 ∧ f = 1

/-- The exceptional finite group models used in CFSG's Lie-type catalog. -/
@[expose] def ExceptionalLieModel (G : Type) [Group G] (family : ExceptionalLieFamily)
    (p f : ℕ) : Prop :=
  ChevalleyExceptionalAdmissible family p f ∧
    match family with
    | .G2 | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 =>
        ChevalleyExceptionalModel G family p f
    | .twistedG2 =>
        ∃ a : ℕ, f = 2 * a + 1 ∧
          ReeTitsRelationModel G .G2 reeG2Perm reeG2Long p f a
    | .twistedF4 =>
        ∃ a : ℕ, f = 2 * a + 1 ∧
          ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | .tits =>
        ∃ a : ℕ, f = 2 * a + 1 ∧
          ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | .twistedB2 => SuzukiExceptionalModel G p f

/-- A group is modeled by one of the exceptional finite Lie-type families. -/
def ExceptionalLieCatalog (G : Type) [Group G] : Prop :=
  ∃ family p f, ExceptionalLieModel G family p f

/-- The standard `²G₂`, `²F₄`, and Tits-group parameterized models. -/
def ReeTitsExceptionalModel (G : Type) [Group G] (kind : ExceptionalReeTag)
    (p f : ℕ) : Prop :=
  ReeTitsAdmissible kind p f ∧ ∃ a : ℕ, f = 2 * a + 1 ∧
    match kind with
    | .twistedG2 => ReeTitsRelationModel G .G2 reeG2Perm reeG2Long p f a
    | .twistedF4 => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | .tits => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end

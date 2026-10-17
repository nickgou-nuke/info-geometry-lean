/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.QuantumContext.MarkovDrazinSemisimplicity

/-!
# Group inverses of finite stochastic Markov Laplacians

The bounded-orbit argument for a finite row-stochastic matrix rules out
nonzero length-two generalized zero-vector chains for `1 - P`. Rank-nullity
then makes the kernel and range complementary. This module constructs the
resulting group inverse using the repository's canonical `IsGroupInverse`
interface. It makes no irreducibility or aperiodicity assumption.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A complement of `ker A` and `range A` yields a group inverse. -/
theorem exists_groupInverse_of_isCompl_ker_range [FiniteDimensional ℝ V]
    (A : Module.End ℝ V)
    (hcomp : IsCompl A.ker A.range) :
    ∃ D : Module.End ℝ V, IsGroupInverse A D := by
  let Ran : Submodule ℝ V := A.range
  have hcompl : IsCompl A.ker Ran := hcomp
  let πRan : V →ₗ[ℝ] Ran := Ran.projectionOnto A.ker hcompl.symm
  have hA_map_Ran : ∀ x : Ran, A x.1 ∈ Ran := by
    intro x
    exact ⟨x.1, rfl⟩
  let AR : Ran →ₗ[ℝ] Ran :=
    LinearMap.codRestrict Ran (A ∘ₗ Ran.subtype) hA_map_Ran
  have hAR_inj : Function.Injective AR := by
    intro x y hxy
    apply Subtype.ext
    have hAxy : A (x.1 - y.1) = 0 := by
      have hval' := congrArg Subtype.val hxy
      change A x.1 = A y.1 at hval'
      rw [map_sub, hval', sub_self]
    have hxker : (x.1 - y.1) ∈ A.ker := by
      simpa [LinearMap.mem_ker] using hAxy
    have hxrange : (x.1 - y.1) ∈ Ran := Ran.sub_mem x.2 y.2
    have hzero : (x.1 - y.1) ∈ (⊥ : Submodule ℝ V) := by
      have hint : (x.1 - y.1) ∈ A.ker ⊓ Ran := ⟨hxker, hxrange⟩
      simpa [hcompl.inf_eq_bot] using hint
    have hxyval : x.1 = y.1 := sub_eq_zero.mp (by simpa using hzero)
    exact hxyval
  let eRan : Ran ≃ₗ[ℝ] Ran := LinearEquiv.ofInjectiveEndo AR hAR_inj
  let D : Module.End ℝ V :=
    Ran.subtype ∘ₗ (eRan.symm : Ran →ₗ[ℝ] Ran) ∘ₗ πRan
  let P : Module.End ℝ V := Ran.subtype ∘ₗ πRan
  have hAD : A * D = P := by
    ext x
    have hright : AR (eRan.symm (πRan x)) = πRan x := by
      change eRan (eRan.symm (πRan x)) = πRan x
      exact eRan.apply_symm_apply (πRan x)
    change A ((eRan.symm (πRan x) : Ran) : V) = P x
    change ((AR (eRan.symm (πRan x)) : Ran) : V) = P x
    rw [hright]
    rfl
  have hDA : D * A = P := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hcompl x with
      ⟨xK, xR, hsum, _⟩
    have hπK : πRan xK = 0 :=
      Submodule.projectionOnto_apply_right hcompl.symm xK
    have hπR : πRan xR = xR :=
      Submodule.projectionOnto_apply_left hcompl.symm xR
    have hAK : A (xK : V) = 0 := xK.2
    have hπAK : πRan (A (xK : V)) = 0 := by simp [hAK]
    have hARxR : A (xR : V) ∈ Ran := hA_map_Ran xR
    have hπARxR : πRan (A (xR : V)) = ⟨A xR, hARxR⟩ :=
      Submodule.projectionOnto_apply_left hcompl.symm ⟨A xR, hARxR⟩
    have hARxR_eq : (⟨A xR, hARxR⟩ : Ran) = AR xR := by
      apply Subtype.ext
      rfl
    have hleftInv : eRan.symm (AR xR) = xR := by
      change eRan.symm (eRan xR) = xR
      exact eRan.symm_apply_apply xR
    have hPsum : P ((xK : V) + xR) = (xR : V) := by
      change (πRan ((xK : V) + xR) : V) = (xR : V)
      simp [map_add, hπK, hπR]
    calc
      (D * A) x = D (A ((xK : V) + xR)) := by simp [hsum]
      _ = D (A (xK : V) + A xR) := by simp [map_add]
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V) + A xR))) := rfl
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V)) + πRan (A xR))) := by
        rw [map_add]
      _ = Ran.subtype (eRan.symm (0 + ⟨A xR, hARxR⟩)) := by
        rw [hπAK, hπARxR]
      _ = Ran.subtype (eRan.symm (AR xR)) := by rw [hARxR_eq]; simp
      _ = (xR : V) := by simp [hleftInv]
      _ = P ((xK : V) + xR) := by rw [hPsum]
      _ = P x := by rw [hsum]
  have hPD : P * D = D := by
    ext x
    have hDx : D x ∈ Ran := by
      unfold D
      exact (eRan.symm (πRan x)).2
    calc
      (P * D) x = Ran.subtype (πRan (D x)) := rfl
      _ = Ran.subtype ⟨D x, hDx⟩ := by
        rw [Submodule.projectionOnto_apply_left hcompl.symm ⟨D x, hDx⟩]
      _ = D x := rfl
  have hPA : P * A = A := by
    ext x
    change (πRan (A x) : V) = A x
    exact congrArg Subtype.val
      (Submodule.projectionOnto_apply_left hcompl.symm ⟨A x, ⟨x, rfl⟩⟩)
  have hADA : A * D * A = A := by
    calc
      A * D * A = (A * D) * A := by simp [mul_assoc]
      _ = P * A := by rw [hAD]
      _ = A := hPA
  have hDAD : D * A * D = D := by
    calc
      D * A * D = (D * A) * D := by simp [mul_assoc]
      _ = P * D := by rw [hDA]
      _ = D := hPD
  exact ⟨D, hADA, hDAD, hAD.trans hDA.symm⟩

/-- If no nonzero vector lies in both `range A` and `ker A`, rank-nullity
makes these subspaces complementary in finite dimension. -/
theorem isCompl_ker_range_of_no_length_two_chain (A : Module.End ℝ V)
    [FiniteDimensional ℝ V]
    (hchain : ¬ ∃ x y : V, A x = y ∧ A y = 0 ∧ y ≠ 0) :
    IsCompl A.ker A.range := by
  have hdisjoint : Disjoint A.ker A.range := by
    apply disjoint_iff_inf_le.mpr
    intro y hy
    rcases hy with ⟨hker, hrange⟩
    rcases hrange with ⟨x, hxy⟩
    have hyzero : y = 0 := by
      by_contra hyne
      exact hchain ⟨x, y, hxy, hker, hyne⟩
    simp [hyzero]
  have hdim : Module.finrank ℝ V ≤
      Module.finrank ℝ A.ker + Module.finrank ℝ A.range := by
    calc
      Module.finrank ℝ V = Module.finrank ℝ A.range + Module.finrank ℝ A.ker :=
        (LinearMap.finrank_range_add_finrank_ker A).symm
      _ = Module.finrank ℝ A.ker + Module.finrank ℝ A.range := Nat.add_comm _ _
      _ ≤ Module.finrank ℝ A.ker + Module.finrank ℝ A.range := le_rfl
  exact (Submodule.isCompl_iff_disjoint A.ker A.range hdim).mpr hdisjoint

/-- Every finite row-stochastic matrix has a group inverse for its Markov
Laplacian `1 - P`, obtained from the bounded-orbit semisimplicity theorem. -/
theorem exists_stochastic_laplacian_groupInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - P)) D := by
  have hNoChain :
      ¬ ∃ x y : ι → ℝ,
        Matrix.toLin' (1 - P) x = y ∧ Matrix.toLin' (1 - P) y = 0 ∧ y ≠ 0 := by
    rintro ⟨x, y, hxy, hyy, hyne⟩
    have hxy' : (1 - P) *ᵥ x = y := by
      simpa only [Matrix.toLin'_apply] using hxy
    have hyy' : (1 - P) *ᵥ y = 0 := by
      simpa only [Matrix.toLin'_apply] using hyy
    exact hyne (no_length_two_generalized_fixed_vector P hP x y hxy' hyy')
  have hcomp := isCompl_ker_range_of_no_length_two_chain
    (Matrix.toLin' (1 - P)) hNoChain
  exact exists_groupInverse_of_isCompl_ker_range (Matrix.toLin' (1 - P)) hcomp

/-- A finite row-stochastic Markov Laplacian has an invertible group-inverse
shift. This is the algebraic resolvent identity; no stationary-distribution or
mean-first-passage interpretation is asserted here. -/
theorem exists_stochastic_laplacian_groupInverse_shift_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - P)) D ∧
      groupInverseShift (Matrix.toLin' (1 - P)) D *
          groupInverseShiftInverse (Matrix.toLin' (1 - P)) D = 1 ∧
      groupInverseShiftInverse (Matrix.toLin' (1 - P)) D *
          groupInverseShift (Matrix.toLin' (1 - P)) D = 1 := by
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  exact ⟨D, hD, groupInverseShift_mul_inverse hD,
    groupInverseShift_inverse_mul hD⟩

/-- The zero-root projector associated to a group inverse, `E₀ = 1 - L L#`.
This is the same complementary idempotent as Hartwig's `principalIdempotent`. -/
def markovKernelProj {A : Type*} [Ring A] (L L_sharp : A) : A :=
  1 - L * L_sharp

/-- The group-inverse kernel projector is idempotent and annihilates the
operator on both sides. -/
theorem markovKernelProj_idempotent_and_annihilates
    {A : Type*} [Ring A] (L L_sharp : A)
    (hD : IsGroupInverse L L_sharp) :
    markovKernelProj L L_sharp * markovKernelProj L L_sharp =
        markovKernelProj L L_sharp ∧
      L * markovKernelProj L L_sharp = 0 ∧
      markovKernelProj L L_sharp * L = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [markovKernelProj, principalIdempotent, regularIdempotent] using
      principalIdempotent_idempotent hD
  · simpa [markovKernelProj, principalIdempotent, regularIdempotent] using
      mul_principalIdempotent_eq_zero hD
  · simpa [markovKernelProj, principalIdempotent, regularIdempotent] using
      principalIdempotent_mul_eq_zero hD

/-- The Kemeny–Snell-style algebraic shift of a group-invertible operator and
its group inverse are two-sided inverses on the whole carrier, with
`E₀ = 1 - L L#`. This statement alone asserts no first-passage interpretation. -/
theorem kemeny_snell_fundamental_invertible
    {A : Type*} [Ring A] (L L_sharp : A)
    (hD : IsGroupInverse L L_sharp) :
    (L + markovKernelProj L L_sharp) *
        (L_sharp + markovKernelProj L L_sharp) = 1 ∧
      (L_sharp + markovKernelProj L L_sharp) *
        (L + markovKernelProj L L_sharp) = 1 := by
  constructor
  · simpa [groupInverseShift, groupInverseShiftInverse,
      markovKernelProj, principalIdempotent, regularIdempotent] using
      groupInverseShift_inverse_mul hD
  · simpa [groupInverseShift, groupInverseShiftInverse,
      markovKernelProj, principalIdempotent, regularIdempotent] using
      groupInverseShift_mul_inverse hD

/-- Unit packaging of the algebraic group-inverse shift. Its inverse is the
shifted group inverse; both inverse equations follow from the canonical
Hartwig group-inverse shift lemmas. -/
def kemenySnellUnit {A : Type*} [Ring A] (L L_sharp : A)
    (hD : IsGroupInverse L L_sharp) : Aˣ where
  val := L + markovKernelProj L L_sharp
  inv := L_sharp + markovKernelProj L L_sharp
  val_inv := (kemeny_snell_fundamental_invertible L L_sharp hD).1
  inv_val := (kemeny_snell_fundamental_invertible L L_sharp hD).2

/-- A group inverse maps every vector into the range of the original endomorphism. -/
theorem groupInverse_apply_mem_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) (x : V) :
    D x ∈ A.range := by
  have hcomm : A (D (D x)) = D (A (D x)) :=
    congrArg (fun f : Module.End ℝ V => f (D x)) hD.2.2
  have hDAD : D (A (D x)) = D x :=
    congrArg (fun f : Module.End ℝ V => f x) hD.2.1
  exact ⟨D (D x), hcomm.trans hDAD⟩

/-- The range of the regular group-inverse projector `A * D` is exactly
`range A`. -/
theorem groupInverse_regularProjector_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) :
    LinearMap.range (A * D) = A.range := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨D x, ?_⟩
    simpa [Module.End.mul_apply] using hx
  · rintro ⟨x, rfl⟩
    refine ⟨A x, ?_⟩
    simpa [Module.End.mul_apply] using
      congrArg (fun f : Module.End ℝ V => f x) hD.1

/-- On `A.range`, applying `A` after its group inverse recovers the input. -/
theorem apply_groupInverse_eq_of_mem_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D) (b : V)
    (hb : b ∈ A.range) :
    A (D b) = b := by
  obtain ⟨y, rfl⟩ := hb
  simpa [mul_assoc] using congrArg (fun f : Module.End ℝ V => f y) hD.1

/-- The group-inverse solution of `A x = b` is unique among solutions in `A.range`.
No uniqueness among all of `V` is asserted when `A` has a nontrivial kernel. -/
theorem groupInverse_solution_unique_on_range
    (A D : Module.End ℝ V) (hD : IsGroupInverse A D)
    (x y : V) (hx : x ∈ A.range) (hy : y ∈ A.range)
    (hxy : A x = A y) :
    x = y := by
  have hx_rec := apply_groupInverse_eq_of_mem_range A D hD x hx
  have hy_rec := apply_groupInverse_eq_of_mem_range A D hD y hy
  calc
    x = A (D x) := hx_rec.symm
    _ = D (A x) := congrArg (fun f : Module.End ℝ V => f x) hD.2.2
    _ = D (A y) := by rw [hxy]
    _ = A (D y) := (congrArg (fun f : Module.End ℝ V => f y) hD.2.2).symm
    _ = y := hy_rec

/-- For a finite row-stochastic matrix, each right-hand side in the range of its
Markov Laplacian has a unique solution constrained to that range. The group
inverse supplies the solution `D b`; this is a finite algebraic Poisson solver,
not a claim about convergence of stochastic powers. -/
theorem stochastic_laplacian_poisson_solution_exists_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (b : ι → ℝ) (hb : b ∈ (Matrix.toLin' (1 - P)).range) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - P)) D ∧
      Matrix.toLin' (1 - P) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - P)).range ∧
      ∀ x : ι → ℝ, x ∈ (Matrix.toLin' (1 - P)).range →
        Matrix.toLin' (1 - P) x = b → x = D b := by
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  refine ⟨D, hD, apply_groupInverse_eq_of_mem_range _ _ hD b hb,
    groupInverse_apply_mem_range _ _ hD b, ?_⟩
  intro x hx hx_eq
  exact groupInverse_solution_unique_on_range _ _ hD x (D b)
    hx (groupInverse_apply_mem_range _ _ hD b) (hx_eq.trans
      (apply_groupInverse_eq_of_mem_range _ _ hD b hb).symm)

/-- A strictly positive row-stochastic matrix fixes exactly the constant
column observables. The proof is the finite maximum principle: at a maximal
coordinate, a strictly positive weighted average can equal the maximum only
when every coordinate is that maximum. -/
theorem positive_rowStochastic_mulVec_fixed_iff_const
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hpos : ∀ i j, 0 < P i j) (x : ι → ℝ) :
    P *ᵥ x = x ↔ ∃ c : ℝ, ∀ i, x i = c := by
  constructor
  · intro hfixed
    classical
    obtain ⟨i₀, hi₀, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) x Finset.univ_nonempty
    by_contra hnot_const
    push Not at hnot_const
    obtain ⟨j₀, hneq⟩ := hnot_const (x i₀)
    have hle : x j₀ ≤ x i₀ := hmax j₀ (Finset.mem_univ j₀)
    have hlt : x j₀ < x i₀ := lt_of_le_of_ne hle hneq
    have hterm_le : ∀ j, P i₀ j * x j ≤ P i₀ j * x i₀ := by
      intro j
      exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j))
        (le_of_lt (hpos i₀ j))
    have hterm_lt : P i₀ j₀ * x j₀ < P i₀ j₀ * x i₀ :=
      mul_lt_mul_of_pos_left hlt (hpos i₀ j₀)
    have hsum_lt :
        (∑ j, P i₀ j * x j) < ∑ j, P i₀ j * x i₀ :=
      Finset.sum_lt_sum (fun j _ => hterm_le j)
        ⟨j₀, Finset.mem_univ j₀, hterm_lt⟩
    have hfixed_coord : (∑ j, P i₀ j * x j) = x i₀ := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hfixed i₀
    have hrow := Matrix.sum_row_of_mem_rowStochastic hP i₀
    rw [hfixed_coord, ← Finset.sum_mul, hrow, one_mul] at hsum_lt
    exact (lt_irrefl (x i₀)) hsum_lt
  · rintro ⟨c, hc⟩
    funext i
    have hrow := Matrix.sum_row_of_mem_rowStochastic hP i
    calc
      (P *ᵥ x) i = ∑ j, P i j * c := by
        simp [Matrix.mulVec, dotProduct, hc]
      _ = c := by rw [← Finset.sum_mul, hrow, one_mul]
      _ = x i := (hc i).symm

/-- For a strictly positive row-stochastic matrix, solutions of the same
Markov Laplacian equation differ by a constant column observable. This is
unconstrained uniqueness modulo the kernel; it does not assert uniqueness
of the solution itself. -/
theorem positive_rowStochastic_laplacian_solutions_differ_by_const
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hpos : ∀ i j, 0 < P i j) (x y : ι → ℝ)
    (hxy : (1 - P) *ᵥ x = (1 - P) *ᵥ y) :
    ∃ c : ℝ, ∀ i, x i - y i = c := by
  have hzero : (1 - P) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hxy
  have hfixed : P *ᵥ (x - y) = x - y := by
    have hzero' := hzero
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hzero'
    exact (sub_eq_zero.mp hzero').symm
  obtain ⟨c, hc⟩ :=
    (positive_rowStochastic_mulVec_fixed_iff_const P hP hpos (x - y)).mp hfixed
  exact ⟨c, hc⟩

/-! ### Polarized attention specialization

The following results connect the generic finite row-stochastic theorem to the
repository's actual query-indexed polarized attention matrix. They concern the
observable action of `I - P`, and assert solvability only for right-hand sides
in its range, with uniqueness only among range-constrained solutions.
-/

namespace Attention

open InfoGeometry.Canonical.Attention
open InfoGeometry.GrandCanonical

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedAttentionFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The actual polarized attention Laplacian `I - P` has a group inverse.
This is a finite algebraic conclusion from row stochasticity; it makes no
irreducibility, aperiodicity, or convergence claim. -/
theorem exists_polarizedAttention_laplacian_groupInverse
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∃ D : Module.End ℝ (Fin n → ℝ),
      IsGroupInverse
        (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)) D := by
  exact exists_stochastic_laplacian_groupInverse
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)

/-- The unmasked finite polarized-attention Laplacian has a two-sided
group-inverse shift. This specializes the algebraic resolvent identity to the
actual Gibbs-row attention matrix, without claiming a stationary distribution
or asymptotic convergence. -/
theorem exists_polarizedAttention_laplacian_groupInverse_shift_inverse
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∃ D : Module.End ℝ (Fin n → ℝ),
      IsGroupInverse
        (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)) D ∧
      groupInverseShift
          (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
            (E := E) (V := V) queries ctx β)) D *
          groupInverseShiftInverse
            (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
              (E := E) (V := V) queries ctx β)) D = 1 ∧
      groupInverseShiftInverse
          (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
            (E := E) (V := V) queries ctx β)) D *
          groupInverseShift
            (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
              (E := E) (V := V) queries ctx β)) D = 1 := by
  exact exists_stochastic_laplacian_groupInverse_shift_inverse
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)

/-- The polarized attention Poisson equation `(I - P) x = b` has a solution
unique within `range (I - P)` whenever `b` belongs to that range. No
unconstrained uniqueness or convergence of attention iterates is asserted. -/
theorem polarizedAttention_poisson_solution_exists_unique
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (b : Fin n → ℝ)
    (hb : b ∈ (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β)).range) :
    ∃ D : Module.End ℝ (Fin n → ℝ),
      IsGroupInverse
        (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)) D ∧
      Matrix.toLin' (1 - polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β)).range ∧
      ∀ x : Fin n → ℝ,
        x ∈ (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)).range →
        Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β) x = b →
        x = D b := by
  exact stochastic_laplacian_poisson_solution_exists_unique
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β) b hb

/-- The canonical group-inverse complementary projector for polarized
attention has range equal to the fixed-observable subspace of `P`.
The vectors are column observables under `P *ᵥ x`; this is not a claim about
stationary row distributions. -/
theorem exists_polarizedAttention_fixedObservable_projection
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∃ D : Module.End ℝ (Fin n → ℝ),
      IsGroupInverse
        (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)) D ∧
      LinearMap.range
          (principalIdempotent
            (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
              (E := E) (V := V) queries ctx β)) D) =
        (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
          (E := E) (V := V) queries ctx β)).ker := by
  obtain ⟨D, hD⟩ := exists_polarizedAttention_laplacian_groupInverse
    (E := E) (V := V) queries ctx β
  refine ⟨D, hD, ?_⟩
  rw [principalIdempotent_eq_drazin_complement]
  simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.drazinCore] using
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_range_eq_drazinCore
      hD.toDrazin)

/-- Every entry of the polarized attention matrix is positive because it is
the corresponding finite Gibbs weight. -/
theorem polarizedPlusAttentionMatrix_pos
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (i j : Fin n) :
    0 < polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β i j := by
  rw [polarizedPlusAttentionMatrix_apply_eq_gibbsWeight
    (E := E) (V := V) (queries := queries) (ctx := ctx) (β := β)
    (i := i) (j := j)]
  exact gibbsWeight_pos
    (polarizedPlusParams (E := E) (V := V) (queries i) ctx) β j

/-- The fixed column observables of polarized attention are the constants.
This is about `P *ᵥ x`, not stationary row probability distributions. -/
theorem polarizedPlusAttention_fixed_mulVec_iff_const
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (x : Fin n → ℝ) :
    polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β *ᵥ x = x ↔
      ∃ c : ℝ, ∀ i, x i = c := by
  exact positive_rowStochastic_mulVec_fixed_iff_const
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β) x

/-- Solutions of the same unmasked polarized-attention Laplacian equation
differ by a constant observable. Strict positivity is supplied by the finite
Gibbs weights defining `polarizedPlusAttentionMatrix`. -/
theorem polarizedAttention_poisson_solutions_differ_by_const
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (x y : Fin n → ℝ)
    (hxy : Matrix.toLin'
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) x =
      Matrix.toLin'
        (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) y) :
    ∃ c : ℝ, ∀ i, x i - y i = c := by
  apply positive_rowStochastic_laplacian_solutions_differ_by_const
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β) x y
  simpa only [Matrix.toLin'_apply] using hxy

/-- For a group inverse of the polarized attention Laplacian, the range of its
principal zero-root projector consists exactly of constant observables. -/
theorem polarizedAttention_principalProjector_mem_iff_const
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (D : Module.End ℝ (Fin n → ℝ))
    (hD : IsGroupInverse
      (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β)) D)
    (x : Fin n → ℝ) :
    x ∈ LinearMap.range
        (principalIdempotent
          (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
            (E := E) (V := V) queries ctx β)) D) ↔
      ∃ c : ℝ, ∀ i, x i = c := by
  let A : Module.End ℝ (Fin n → ℝ) :=
    Matrix.toLin' (1 - polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β)
  have hRange : LinearMap.range (principalIdempotent A D) = A.ker := by
    rw [principalIdempotent_eq_drazin_complement]
    simpa [A, InfoGeometry.Canonical.Drazin.IsDrazinInverse.drazinCore] using
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_range_eq_drazinCore
        hD.toDrazin)
  rw [hRange, LinearMap.mem_ker]
  change (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β) x = 0) ↔ _
  simp only [Matrix.toLin'_apply]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro hx
    exact (polarizedPlusAttention_fixed_mulVec_iff_const
      (E := E) (V := V) queries ctx β x).mp hx.symm
  · intro hx
    exact ((polarizedPlusAttention_fixed_mulVec_iff_const
      (E := E) (V := V) queries ctx β x).mpr hx).symm

/- The complementary group-inverse projector for polarized attention is
fixed by the transition operator on both sides. The first equality says its
image consists of right fixed observables; the second says its rows are left
stationary linear functionals. This does not assert those functionals are
positive or normalized probability distributions. -/
omit [AddCommMonoid V] [Module ℝ V] [Fact (0 < n)] in
theorem polarizedAttention_principalProjector_transition_invariant
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (D : Module.End ℝ (Fin n → ℝ))
    (hD : IsGroupInverse
      (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β)) D) :
    let P : Module.End ℝ (Fin n → ℝ) :=
      Matrix.toLin' (polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β)
    let E₀ : Module.End ℝ (Fin n → ℝ) :=
      principalIdempotent (Matrix.toLin' (1 - polarizedPlusAttentionMatrix
        (E := E) (V := V) queries ctx β)) D
    P * E₀ = E₀ ∧ E₀ * P = E₀ := by
  let P : Module.End ℝ (Fin n → ℝ) :=
    Matrix.toLin' (polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β)
  let L : Module.End ℝ (Fin n → ℝ) :=
    Matrix.toLin' (1 - polarizedPlusAttentionMatrix
      (E := E) (V := V) queries ctx β)
  let E₀ : Module.End ℝ (Fin n → ℝ) := principalIdempotent L D
  have hL : L = 1 - P := by
    ext x
    simp [L, P, Matrix.toLin'_apply]
  have hLE : L * E₀ = 0 := by
    exact mul_principalIdempotent_eq_zero hD
  have hEL : E₀ * L = 0 := by
    exact principalIdempotent_mul_eq_zero hD
  change P * E₀ = E₀ ∧ E₀ * P = E₀
  constructor
  · rw [hL] at hLE
    calc
      P * E₀ = (1 - (1 - P)) * E₀ := by congr 1; noncomm_ring
      _ = E₀ := by rw [sub_mul, one_mul, hLE]; simp
  · rw [hL] at hEL
    calc
      E₀ * P = E₀ * (1 - (1 - P)) := by congr 1; noncomm_ring
      _ = E₀ := by rw [mul_sub, mul_one, hEL]; simp

end Attention

end InfoGeometry.QuantumContext.MarkovDrazin

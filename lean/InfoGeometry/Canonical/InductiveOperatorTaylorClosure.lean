import InfoGeometry.Canonical.SuperBracketHestenesKreinClosure

/-!
# InfoGeometry.Canonical.InductiveOperatorTaylorClosure

Finite inductive operator-Taylor closure.

This is the algebraic/inductive lane: operator functions are represented by
finite Taylor prefixes, not by analytic continuation or completed infinite
series.  The theorem content is finite:

* `operatorTaylorPrefix c N A = ∑ k < N, c k • A^k`;
* prefixes satisfy the expected successor recursion;
* sector-preserving generators have sector-preserving powers and finite
  Taylor prefixes;
* Hestenes--Krein intertwiners have algebraically graded powers.

No infinite series.
No convergence theorem.
No analytic continuation.
No topological completion.
-/

namespace InfoGeometry.Canonical.InductiveOperatorTaylorClosure

open Finset
open InfoGeometry.Canonical.SymmetryClosureConformalBlocks
open InfoGeometry.Canonical.SuperBracketHestenesKreinClosure
open InfoGeometry.Canonical.SymmetryClosureConformalBlocks.SectorDecomposition

/-- A coefficient recursion for finite Taylor prefixes. -/
structure TaylorCoefficientRecursion where
  /-- Coefficient sequence. -/
  coeff : ℕ → ℂ

/-- Finite operator-Taylor prefix `∑_{k < N} cₖ A^k`. -/
noncomputable def operatorTaylorPrefix {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℕ → ℂ) (N : ℕ) (A : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ∑ k ∈ Finset.range N, c k • (A ^ k)

@[simp]
theorem operatorTaylorPrefix_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℕ → ℂ) (A : V →ₗ[ℂ] V) :
    operatorTaylorPrefix c 0 A = 0 := by
  simp [operatorTaylorPrefix]

/-- Inductive step for finite operator-Taylor prefixes. -/
theorem operatorTaylorPrefix_succ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℕ → ℂ) (N : ℕ) (A : V →ₗ[ℂ] V) :
    operatorTaylorPrefix c (N + 1) A =
      operatorTaylorPrefix c N A + c N • (A ^ N) := by
  simp [operatorTaylorPrefix, Finset.sum_range_succ]

/-- Prefix attached to a coefficient-recursion packet. -/
noncomputable def TaylorCoefficientRecursion.prefix {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : TaylorCoefficientRecursion) (N : ℕ) (A : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  operatorTaylorPrefix R.coeff N A

/-- The recursion packet prefix satisfies the same finite step formula. -/
theorem TaylorCoefficientRecursion.prefix_succ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : TaylorCoefficientRecursion) (N : ℕ) (A : V →ₗ[ℂ] V) :
    R.prefix (N + 1) A = R.prefix N A + R.coeff N • (A ^ N) :=
  operatorTaylorPrefix_succ R.coeff N A

/-- Coefficientwise sums become sums of finite operator-Taylor prefixes. -/
theorem operatorTaylorPrefix_add_coeff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c d : ℕ → ℂ) (N : ℕ) (A : V →ₗ[ℂ] V) :
    operatorTaylorPrefix (fun k => c k + d k) N A =
      operatorTaylorPrefix c N A + operatorTaylorPrefix d N A := by
  simp [operatorTaylorPrefix, add_smul, Finset.sum_add_distrib]

/-- Scalar rescaling of coefficients becomes scalar rescaling of the finite prefix. -/
theorem operatorTaylorPrefix_smul_coeff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : ℂ) (c : ℕ → ℂ) (N : ℕ) (A : V →ₗ[ℂ] V) :
    operatorTaylorPrefix (fun k => a * c k) N A =
      a • operatorTaylorPrefix c N A := by
  simp [operatorTaylorPrefix, mul_smul, Finset.smul_sum]

namespace SectorDecomposition

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Scalar multiples of sector-preserving generators preserve sectors. -/
theorem preservesSectors_smul {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (c : ℂ) :
    D.PreservesSectors (c • A) := by
  constructor
  · intro v hv
    exact D.computational.smul_mem c (hA.1 v hv)
  · intro v hv
    exact D.noncomputational.smul_mem c (hA.2 v hv)

/-- Powers of a sector-preserving generator preserve sectors. -/
theorem preservesSectors_pow {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (N : ℕ) :
    D.PreservesSectors (A ^ N) := by
  induction N with
  | zero => simpa using D.preservesSectors_id
  | succ N ih =>
      rw [pow_succ]
      exact D.preservesSectors_comp ih hA

/-- Every finite operator-Taylor prefix of a sector-preserving generator preserves sectors. -/
theorem preservesSectors_operatorTaylorPrefix {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (c : ℕ → ℂ) (N : ℕ) :
    D.PreservesSectors (operatorTaylorPrefix c N A) := by
  induction N with
  | zero =>
      simp [operatorTaylorPrefix]
      constructor <;> intro v hv <;> simp
  | succ N ih =>
      rw [operatorTaylorPrefix_succ]
      exact preservesSectors_add ih
        (preservesSectors_smul (preservesSectors_pow hA N) (c N))

/-- Finite operator-Taylor prefixes have no leakage from the computational sector. -/
theorem noLeakage_operatorTaylorPrefix {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (c : ℕ → ℂ) (N : ℕ) :
    D.NoLeakage (operatorTaylorPrefix c N A) :=
  noLeakage_of_preservesSectors (preservesSectors_operatorTaylorPrefix hA c N)

end SectorDecomposition

namespace IntertwinesBy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {K A : V →ₗ[ℂ] V} {σ : ℂ}

/-- Powers of an intertwining generator have the powered grade. -/
theorem pow (hA : IntertwinesBy K σ A) (N : ℕ) :
    IntertwinesBy K (σ ^ N) (A ^ N) := by
  induction N with
  | zero =>
      ext v
      simp [LinearMap.comp_apply]
  | succ N ih =>
      rw [pow_succ, pow_succ]
      exact IntertwinesBy.comp ih hA

end IntertwinesBy

/-- A homogeneous finite Taylor prefix uses coefficients only in one target grade. -/
def HomogeneousCoefficientSupport (σ target : ℂ) (c : ℕ → ℂ) (N : ℕ) : Prop :=
  ∀ k ∈ Finset.range N, c k ≠ 0 → σ ^ k = target

/--
Finite homogeneous operator-Taylor prefixes inherit the target Hestenes--Krein
grade.  The support condition is explicit; no infinite series is used.
-/
theorem intertwines_operatorTaylorPrefix_of_homogeneous
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {K A : V →ₗ[ℂ] V} {σ target : ℂ}
    (hA : IntertwinesBy K σ A) (c : ℕ → ℂ) (N : ℕ)
    (hsupp : HomogeneousCoefficientSupport σ target c N) :
    IntertwinesBy K target (operatorTaylorPrefix c N A) := by
  induction N with
  | zero =>
      simp [operatorTaylorPrefix]
      ext v
      simp
  | succ N ih =>
      rw [operatorTaylorPrefix_succ]
      by_cases hcN : c N = 0
      · simp [hcN]
        exact ih (by
          intro k hk hck
          exact hsupp k
            (Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self N)))
            hck)
      · have htarget : σ ^ N = target := hsupp N (by simp) hcN
        have hpow := IntertwinesBy.pow hA N
        have hterm : IntertwinesBy K target (c N • (A ^ N)) := by
          simpa [htarget] using IntertwinesBy.smul (K := K) (A := A ^ N)
            (σ := σ ^ N) (c := c N) hpow
        exact IntertwinesBy.add (ih (by
          intro k hk hck
          exact hsupp k
            (Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self N)))
            hck)) hterm

end InfoGeometry.Canonical.InductiveOperatorTaylorClosure

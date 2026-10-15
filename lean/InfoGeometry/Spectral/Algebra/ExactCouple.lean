import Mathlib.Algebra.Module.Submodule.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic

/-!
# Exact Couples

This file contains a small Lean-native exact-couple core.  It intentionally does
not claim construction of derived couples or convergence.  The closed theorem is
the standard theorem needed by spectral-sequence constructions: the differential
`d = j ∘ k` squares to zero, derived from the exactness law `ker k = range j`.
-/

namespace InfoGeometry.Spectral.Algebra

abbrev Z2 := ℤ × ℤ

def shiftI (pq : Z2) : Z2 := (pq.1 + 1, pq.2 - 1)

/-- The inverse bidegree shift to `shiftI`. -/
def shiftIPre (pq : Z2) : Z2 := (pq.1 - 1, pq.2 + 1)

def shiftK (pq : Z2) : Z2 := (pq.1 - 1, pq.2)

/-- The inverse bidegree shift to `shiftK`. -/
def shiftKPre (pq : Z2) : Z2 := (pq.1 + 1, pq.2)

@[simp]
theorem shiftI_shiftIPre (pq : Z2) : shiftI (shiftIPre pq) = pq := by
  ext <;> simp [shiftI, shiftIPre]

@[simp]
theorem shiftIPre_shiftI (pq : Z2) : shiftIPre (shiftI pq) = pq := by
  ext <;> simp [shiftI, shiftIPre]

@[simp]
theorem shiftK_shiftKPre (pq : Z2) : shiftK (shiftKPre pq) = pq := by
  ext <;> simp [shiftK, shiftKPre]

@[simp]
theorem shiftKPre_shiftK (pq : Z2) : shiftKPre (shiftK pq) = pq := by
  ext <;> simp [shiftK, shiftKPre]

universe u

/-- A bigraded exact-couple fragment with maps of the usual bidegrees. -/
structure ExactCouple (R : Type u) [Ring R]
    (D E : Z2 → Type u)
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)] where
  i : ∀ pq, D pq →ₗ[R] D (shiftI pq)
  j : ∀ pq, D pq →ₗ[R] E pq
  k : ∀ pq, E pq →ₗ[R] D (shiftK pq)
  exact_ij :
    ∀ pq, LinearMap.ker (j (shiftI pq)) = LinearMap.range (i pq)
  exact_jk :
    ∀ pq, LinearMap.ker (k pq) = LinearMap.range (j pq)
  exact_ki :
    ∀ pq, LinearMap.ker (i (shiftK pq)) = LinearMap.range (k pq)

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]
variable (C : ExactCouple R D E)

/-- The exact-couple differential `d = j ∘ k`. -/
def differential (pq : Z2) : E pq →ₗ[R] E (shiftK pq) :=
  (C.j (shiftK pq)).comp (C.k pq)

/-- The index calculation for applying the differential twice. -/
@[simp]
theorem shiftK_shiftK (pq : Z2) : shiftK (shiftK pq) = (pq.1 - 2, pq.2) := by
  ext <;> simp [shiftK]
  omega

/-- Exactness at `E` implies the exact-couple differential squares to zero. -/
theorem differential_comp_differential (pq : Z2) :
    (C.differential (shiftK pq)).comp (C.differential pq) = 0 := by
  ext x
  have hmem :
      C.j (shiftK pq) (C.k pq x) ∈ LinearMap.range (C.j (shiftK pq)) := by
    exact ⟨C.k pq x, rfl⟩
  have hker :
      C.j (shiftK pq) (C.k pq x) ∈ LinearMap.ker (C.k (shiftK pq)) := by
    rw [C.exact_jk (shiftK pq)]
    exact hmem
  have hzero :
      C.k (shiftK pq) (C.j (shiftK pq) (C.k pq x)) = 0 := hker
  simp [differential, LinearMap.comp_apply, hzero]

end ExactCouple

/-- A map between exact couples on possibly different bigraded module families.
The component maps commute with the three structure arrows; this is the actual
morphism data used to transport the differential. -/
structure ExactCoupleMap (R : Type u) [Ring R]
    {D E D' E' : Z2 → Type u}
    [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
    [∀ pq, AddCommGroup (D' pq)] [∀ pq, AddCommGroup (E' pq)]
    [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]
    [∀ pq, Module R (D' pq)] [∀ pq, Module R (E' pq)]
    (C : ExactCouple R D E) (C' : ExactCouple R D' E') where
  dMap : ∀ pq, D pq →ₗ[R] D' pq
  eMap : ∀ pq, E pq →ₗ[R] E' pq
  comm_i : ∀ pq x, dMap (shiftI pq) (C.i pq x) = C'.i pq (dMap pq x)
  comm_j : ∀ pq x, eMap pq (C.j pq x) = C'.j pq (dMap pq x)
  comm_k : ∀ pq x, dMap (shiftK pq) (C.k pq x) = C'.k pq (eMap pq x)

namespace ExactCoupleMap

variable {R : Type u} [Ring R]
variable {D E D' E' : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, AddCommGroup (D' pq)] [∀ pq, AddCommGroup (E' pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]
variable [∀ pq, Module R (D' pq)] [∀ pq, Module R (E' pq)]
variable {C : ExactCouple R D E} {C' : ExactCouple R D' E'}

/-- The exact-couple differential is natural under every diagram map. -/
theorem map_differential (f : ExactCoupleMap R C C') (pq : Z2) (x : E pq) :
    f.eMap (shiftK pq) (C.differential pq x) =
      C'.differential pq (f.eMap pq x) := by
  change f.eMap (shiftK pq)
      (C.j (shiftK pq) (C.k pq x)) =
    C'.j (shiftK pq) (C'.k pq (f.eMap pq x))
  rw [f.comm_j, f.comm_k]

end ExactCoupleMap

end InfoGeometry.Spectral.Algebra

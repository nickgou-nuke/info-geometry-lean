/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# From Grassmann to Clifford: the fermion CAR and the Clifford operator

Source: Z. Oziewicz, *From Grassmann to Clifford*, in Chisholm & Common (eds.),
Clifford Algebras and Their Applications in Mathematical Physics (Reidel, 1986),
pp. 245–255, Eqs. (6), (11), (16), (22), (23).

The carrier is the exterior algebra, presented as `CliffordAlgebra (Q := 0)`.
Left exterior multiplication `e_a` (wedge by a vector) and contraction `i_d`
(by a covector) are the fermion creation/annihilation operators.  The paper's
thesis is that the Clifford product is the Grassmann product together with a
structure map: the Clifford operator `γ_{a,d} = e_a + i_d` satisfies the Clifford
square relation `γ² = d(a)`, a direct consequence of the canonical
anticommutation relation (16).

All results are operator identities on the exterior algebra and reuse Mathlib's
`contractLeft_ι_mul`, `contractLeft_contractLeft`, `ι_sq_zero`, and
`ι_mul_ι_comm`.  No metric signature, Witt decomposition, or twistor ideal is
assumed.
-/

noncomputable section

namespace InfoGeometry.Algebra.GrassmannToCliffordCAR

open CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The exterior algebra as the zero-quadratic-form Clifford algebra. -/
abbrev EA (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  CliffordAlgebra (0 : QuadraticForm R M)

/-- Left exterior multiplication `e_a` (Oziewicz Eq. (5)): wedge by `a`. -/
def wedgeOp (a : M) : Module.End R (EA R M) :=
  LinearMap.mulLeft R (ι (0 : QuadraticForm R M) a)

/-- Contraction `i_d` (Oziewicz Eq. (9)): interior product by the covector `d`. -/
def contractOp (d : Module.Dual R M) : Module.End R (EA R M) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d

/-- **Oziewicz Eq. (16): the canonical anticommutation relation (CAR).**
`{i_d, e_a} = i_d ∘ e_a + e_a ∘ i_d = d(a) • id`.  This is the fermion
creation/annihilation anticommutator, a direct operator form of Mathlib's
`contractLeft_ι_mul`. -/
theorem car_anticommutator (a : M) (d : Module.Dual R M) :
    (contractOp d).comp (wedgeOp a) + (wedgeOp a).comp (contractOp d) =
      (d a) • LinearMap.id := by
  ext x
  simp only [wedgeOp, contractOp, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.mulLeft_apply]
  have h := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R M)) (d := d) a x
  rw [h]
  abel

/-- **Oziewicz Eq. (6): nilpotency of exterior multiplication.** `e_a ∘ e_a = 0`
(a vector has odd degree). -/
theorem wedgeOp_sq_zero (a : M) :
    (wedgeOp (R := R) (M := M) a).comp (wedgeOp (R := R) (M := M) a) =
      (0 : Module.End R (EA R M)) := by
  ext x
  simp only [wedgeOp, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
  rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar]
  simp

/-- **Oziewicz Eq. (11): nilpotency of contraction.** `i_d ∘ i_d = 0`. -/
theorem contractOp_sq_zero (d : Module.Dual R M) :
    (contractOp d).comp (contractOp d) = 0 := by
  ext x
  simp only [contractOp, LinearMap.comp_apply, LinearMap.zero_apply]
  exact CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm R M)) d x

/-- **Oziewicz Eq. (11): distinct contractions anticommute.** -/
theorem contractOp_anticommute (d e : Module.Dual R M) :
    (contractOp d).comp (contractOp e) + (contractOp e).comp (contractOp d) =
      (0 : Module.End R (EA R M)) := by
  ext x
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) e x) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) e
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

/-- **Oziewicz Eq. (6): supercommutativity of exterior multiplication.**
`e_a ∘ e_b + e_b ∘ e_a = 0` for vectors (odd degree). -/
theorem wedgeOp_anticommute (a b : M) :
    (wedgeOp (R := R) (M := M) a).comp (wedgeOp (R := R) (M := M) b) +
      (wedgeOp (R := R) (M := M) b).comp (wedgeOp (R := R) (M := M) a) =
        (0 : Module.End R (EA R M)) := by
  ext x
  simp only [wedgeOp, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply]
  have hcomm : ι (0 : QuadraticForm R M) a * ι (0 : QuadraticForm R M) b =
      -(ι (0 : QuadraticForm R M) b * ι (0 : QuadraticForm R M) a) := by
    have := CliffordAlgebra.ι_mul_ι_comm (Q := (0 : QuadraticForm R M)) a b
    simpa [QuadraticMap.polar] using this
  rw [← mul_assoc, ← mul_assoc, hcomm]
  rw [neg_mul]
  exact neg_add_cancel _

/-- The Clifford / Kähler–Atiyah operator `γ_{a,d} = e_a + i_d` (Oziewicz Eq. (23),
degree-one case). -/
def cliffordOp (a : M) (d : Module.Dual R M) : Module.End R (EA R M) :=
  wedgeOp a + contractOp d

/-- **Oziewicz Eqs. (22)+(16): the Clifford square relation.**
`γ_{a,d} ∘ γ_{a,d} = d(a) • id`.  The Clifford operator is a square root of the
scalar `d(a)`; this is the defining Clifford relation obtained from the Grassmann
products plus the structure covector `d`. -/
theorem cliffordOp_sq (a : M) (d : Module.Dual R M) :
    (cliffordOp (R := R) (M := M) a d).comp
        (cliffordOp (R := R) (M := M) a d) =
      (d a) • (LinearMap.id : Module.End R (EA R M)) := by
  have hdist : (cliffordOp a d).comp (cliffordOp a d)
      = (wedgeOp a).comp (wedgeOp a) + (contractOp d).comp (contractOp d)
        + ((contractOp d).comp (wedgeOp a) + (wedgeOp a).comp (contractOp d)) := by
    simp only [cliffordOp, LinearMap.add_comp, LinearMap.comp_add]
    abel
  rw [hdist, wedgeOp_sq_zero (R := R) (M := M) a,
    contractOp_sq_zero (R := R) (M := M) d]
  simp only [zero_add, add_zero]
  exact car_anticommutator (R := R) (M := M) a d

/-- **Oziewicz Eqs. (15)--(22): the full mixed Clifford relation.**
For two generators `a + d` and `b + e` in `M ⊕ M*`, the anticommutator
of their creation/contraction operators is the symmetric evaluation pairing
`d(b) + e(a)`. The square theorem is its diagonal specialization. -/
theorem cliffordOp_anticommutator (a b : M)
    (d e : Module.Dual R M) :
    (cliffordOp (R := R) (M := M) a d).comp
        (cliffordOp (R := R) (M := M) b e) +
      (cliffordOp (R := R) (M := M) b e).comp
        (cliffordOp (R := R) (M := M) a d) =
      (d b + e a) • (LinearMap.id : Module.End R (EA R M)) := by
  have hdist :
      (cliffordOp (R := R) (M := M) a d).comp
          (cliffordOp (R := R) (M := M) b e) +
        (cliffordOp (R := R) (M := M) b e).comp
          (cliffordOp (R := R) (M := M) a d) =
      ((wedgeOp (R := R) (M := M) a).comp (wedgeOp b) +
          (wedgeOp b).comp (wedgeOp a)) +
        ((contractOp d).comp (contractOp e) +
          (contractOp e).comp (contractOp d)) +
        ((contractOp d).comp (wedgeOp b) +
          (wedgeOp b).comp (contractOp d)) +
        ((contractOp e).comp (wedgeOp a) +
          (wedgeOp a).comp (contractOp e)) := by
    simp only [cliffordOp, LinearMap.add_comp, LinearMap.comp_add]
    abel
  rw [hdist, wedgeOp_anticommute, contractOp_anticommute,
    car_anticommutator (R := R) (M := M) b d,
    car_anticommutator (R := R) (M := M) a e]
  simp only [zero_add, add_zero]
  rw [← add_smul]

end InfoGeometry.Algebra.GrassmannToCliffordCAR

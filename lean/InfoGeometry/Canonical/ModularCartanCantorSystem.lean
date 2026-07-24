import Mathlib

/-!
# Modular Cartan/Cantor Toy Owner Surface

Small algebraic owner lemmas for modular twins, projective log increments,
normal-cone rays, and pullback metrics.  Stronger analytic claims belong in the
bridge modules that import this file.
-/

namespace InfoGeometry.Canonical.ModularCartanCantorSystem

def modularTwin {A : Type*} [Mul A] (J X : A) : A :=
J * X * J

theorem modularTwin_involutive
{A : Type*} [Monoid A]
(J X : A)
(hJ : J * J = 1) :
modularTwin J (modularTwin J X) = X := by
  unfold modularTwin
  rw [mul_assoc J (J * X * J) J]
  rw [mul_assoc (J * X) J J]
  rw [hJ, mul_one]
  rw [← mul_assoc J J X, hJ, one_mul]

def pairTheta {A : Type*} [Mul A] (J : A) (P : A × A) : A × A :=
(modularTwin J P.2, modularTwin J P.1)

theorem pairTheta_involutive
{A : Type*} [Monoid A]
(J : A)
(P : A × A)
(hJ : J * J = 1) :
pairTheta J (pairTheta J P) = P := by
  cases P with
  | mk A B =>
    unfold pairTheta
    simp [modularTwin_involutive J A hJ, modularTwin_involutive J B hJ]

def IsSelfDualTwinPair {A : Type*} [Mul A] (J : A) (P : A × A) : Prop :=
pairTheta J P = P

def IsAntiSelfDualTwinPair {A : Type*} [Mul A] [Neg A] (J : A) (P : A × A) : Prop :=
pairTheta J P = (-P.1, -P.2)

theorem selfDualTwinPair_fixed
{A : Type*} [Mul A]
(J : A) (P : A × A)
(hP : IsSelfDualTwinPair J P) :
pairTheta J P = P :=
hP

theorem antiSelfDualTwinPair_negated
{A : Type*} [Mul A] [Neg A]
(J : A) (P : A × A)
(hP : IsAntiSelfDualTwinPair J P) :
pairTheta J P = (-P.1, -P.2) :=
hP

theorem mkSelfDualTwinPair_isSelfDual
{A : Type*} [Monoid A]
(J X : A)
(hJ : J * J = 1) :
IsSelfDualTwinPair J (X, modularTwin J X) := by
  unfold IsSelfDualTwinPair pairTheta
  simp [modularTwin_involutive J X hJ]

noncomputable def scalarCylinderLogIncrement (r s : ℝ) : ℝ :=
  Real.log r - Real.log s

theorem cylinderLogIncrement_projective_rescale
{c r s : ℝ}
(hc : 0 < c)
(hr : 0 < r)
(hs : 0 < s) :
scalarCylinderLogIncrement (c * r) (c * s) =
scalarCylinderLogIncrement r s := by
unfold scalarCylinderLogIncrement
rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hr)]
rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hs)]
ring

noncomputable def cylinderLogPotential {Word : Type*} (weight : Word → ℝ) (w : Word) : ℝ :=
  -Real.log (weight w)

noncomputable def cylinderLogIncrement
    {Word : Type*}
    (weight : Word → ℝ)
    (parent child : Word) : ℝ :=
  -Real.log (weight child / weight parent)

theorem cylinderLogIncrement_common_pos_smul
    {Word : Type*}
    (weight : Word → ℝ)
    (parent child : Word)
    {c : ℝ}
    (hc : 0 < c) :
    cylinderLogIncrement (fun w => c * weight w) parent child =
      cylinderLogIncrement weight parent child := by
  unfold cylinderLogIncrement
  have hratio :
      c * weight child / (c * weight parent) = weight child / weight parent := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_div_mul_left (weight child) (weight parent) hc.ne')
  rw [hratio]

noncomputable def relativeCountModularProfile
{ι : Type*} [Fintype ι]
(r s : ι → ℝ) : ℝ :=
∑ i, scalarCylinderLogIncrement (r i) (s i)

theorem relativeCountModularProfile_projective_rescale
{ι : Type*} [Fintype ι]
(c : ℝ)
(r s : ι → ℝ)
(hc : 0 < c)
(hr : ∀ i, 0 < r i)
(hs : ∀ i, 0 < s i) :
relativeCountModularProfile (fun i => c * r i) (fun i => c * s i) =
relativeCountModularProfile r s := by
unfold relativeCountModularProfile
refine Finset.sum_congr rfl ?_
intro i hi
exact cylinderLogIncrement_projective_rescale hc (hr i) (hs i)

theorem coneVector_mem_naturalCone_of_mem
{E : Type*}
(naturalCone : Set E)
(coneVector : E)
(hmem : coneVector ∈ naturalCone) :
coneVector ∈ naturalCone :=
hmem

theorem J_fixes_coneVector_of_fixed
{E : Type*}
(J : E → E)
(coneVector : E)
(hfixed : J coneVector = coneVector) :
J coneVector = coneVector :=
hfixed

def outwardNormalCone {E : Type*} [SMul ℝ E] (v : E) : Set E :=
{x | ∃ c : ℝ, 0 ≤ c ∧ x = c • v}

def inwardNormalCone {E : Type*} [SMul ℝ E] [Neg E] (v : E) : Set E :=
{x | ∃ c : ℝ, 0 ≤ c ∧ x = c • (-v)}

theorem outwardNormalCone_coneVector
{E : Type*} [MulAction ℝ E]
(v : E) :
v ∈ outwardNormalCone v := by
refine ⟨1, zero_le_one, ?_⟩
exact (one_smul ℝ v).symm

theorem inwardNormalCone_coneVector
{E : Type*} [MulAction ℝ E] [Neg E]
(v : E) :
-v ∈ inwardNormalCone v := by
refine ⟨1, zero_le_one, ?_⟩
exact (one_smul ℝ (-v)).symm

def pullbackMetric
{Param State : Type*}
(stateMap : Param → State)
(modularMetric : State → State → ℝ)
(x y : Param) : ℝ :=
modularMetric (stateMap x) (stateMap y)

theorem metric_eq_pullback
{Param State : Type*}
(stateMap : Param → State)
(modularMetric : State → State → ℝ)
(metric : Param → Param → ℝ)
(hmetric : ∀ x y, metric x y = pullbackMetric stateMap modularMetric x y) :
∀ x y, metric x y = modularMetric (stateMap x) (stateMap y) := by
intro x y
exact hmetric x y

end InfoGeometry.Canonical.ModularCartanCantorSystem

import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Operations

open scoped BigOperators

/-!
# Finite Boltzmann Macroentropy

Boltzmann entropy is microstate-indexed and macrostate-defined.  For a finite
coarse graining `G : X → M`, the multiplicity of `m` is the cardinality of its
fiber and

`S_B(x) = log(card {y // G.project y = G.project x})`.

The operator lift is formed in an arbitrary real algebra from a finite
orthogonal family of macrosector projectors.  It is not restricted to a
diagonal matrix presentation.  The repository convention in this lane is the
dimensionless normalization `k_B = 1`.
-/

namespace InfoGeometry.Canonical.FiniteBoltzmannMacroentropy

variable {X M : Type*}
variable [Fintype X] [Fintype M] [DecidableEq X] [DecidableEq M]

/-- Number of microscopic states in a macrostate fiber. -/
def macroMultiplicity (G : FiniteCoarseGraining X M) (m : M) : ℕ :=
  Fintype.card {x : X // G.project x = m}

/-- Dimensionless Boltzmann entropy assigned through the realized macrostate. -/
noncomputable def boltzmannEntropy
    (G : FiniteCoarseGraining X M) (x : X) : ℝ :=
  Real.log (macroMultiplicity G (G.project x) : ℝ)

/--
Boltzmann macroentropy operator in an arbitrary noncommutative real algebra:
each macrosector projector carries the logarithm of its microscopic
multiplicity.
-/
noncomputable def boltzmannEntropyOperator
    {A : Type*} [Ring A] [Algebra ℝ A]
    (G : FiniteCoarseGraining X M) (P : M → A) : A :=
  ∑ m : M, Real.log (macroMultiplicity G m : ℝ) • P m

/-- Boltzmann entropy is constant on each macrostate fiber. -/
theorem boltzmannEntropy_eq_of_same_macrostate
    (G : FiniteCoarseGraining X M) {x y : X}
    (hxy : G.project x = G.project y) :
    boltzmannEntropy G x = boltzmannEntropy G y := by
  simp [boltzmannEntropy, hxy]

/--
An orthogonal macrosector family diagonalizes the macroentropy intrinsically:
right multiplication by `P m` extracts the `log W_m` sector.  The ambient
algebra itself may be noncommutative.
-/
theorem boltzmannEntropyOperator_mul_macroProjector
    {A : Type*} [Ring A] [Algebra ℝ A]
    (G : FiniteCoarseGraining X M) (P : M → A) (m : M)
    (hOrthogonal :
      ∀ n : M, P n * P m = if n = m then P m else 0) :
    boltzmannEntropyOperator G P * P m =
      Real.log (macroMultiplicity G m : ℝ) • P m := by
  rw [boltzmannEntropyOperator, Finset.sum_mul]
  simp [smul_mul_assoc, hOrthogonal]

/-- Uniform microcanonical density on one macrostate fiber. -/
noncomputable def microcanonicalDensity
    (G : FiniteCoarseGraining X M) (m : M) (x : X) : ℝ :=
  if G.project x = m then (macroMultiplicity G m : ℝ)⁻¹ else 0

/--
Pointwise surprisal relative to the uniform conditional law on one macrostate
fiber. This is defined before taking any expectation.
-/
noncomputable def conditionalMicrocanonicalSurprisal
    (G : FiniteCoarseGraining X M) (m : M) (x : X) : ℝ :=
  -Real.log (microcanonicalDensity G m x)

/--
On the selected macrostate fiber, conditional surprisal is the logarithm of
the fiber multiplicity.
-/
theorem conditionalMicrocanonicalSurprisal_eq_log_macroMultiplicity
    (G : FiniteCoarseGraining X M) (m : M) (x : X)
    (hx : G.project x = m) :
    conditionalMicrocanonicalSurprisal G m x =
      Real.log (macroMultiplicity G m : ℝ) := by
  simp [conditionalMicrocanonicalSurprisal, microcanonicalDensity, hx, Real.log_inv]

/--
With the repository's dimensionless convention `k_B = 1`, Boltzmann
macroentropy is exactly pointwise conditional surprisal relative to the
uniform law on the realized macrostate fiber.
-/
theorem boltzmannEntropy_eq_conditionalMicrocanonicalSurprisal
    (G : FiniteCoarseGraining X M) (m : M) (x : X)
    (hx : G.project x = m) :
    boltzmannEntropy G x =
      conditionalMicrocanonicalSurprisal G m x := by
  rw [conditionalMicrocanonicalSurprisal_eq_log_macroMultiplicity G m x hx]
  simp [boltzmannEntropy, hx]

/--
Historical compatibility name. In this theory `k_B = 1`, so there is no
additional scalar factor.
-/
theorem boltzmannEntropy_eq_kB_mul_conditionalMicrocanonicalSurprisal
    (G : FiniteCoarseGraining X M) (m : M) (x : X)
    (hx : G.project x = m) :
    boltzmannEntropy G x =
      conditionalMicrocanonicalSurprisal G m x :=
  boltzmannEntropy_eq_conditionalMicrocanonicalSurprisal G m x hx

/-- A realized macrostate fiber has strictly positive multiplicity. -/
theorem macroMultiplicity_pos_of_mem
    (G : FiniteCoarseGraining X M) (m : M) (x : X)
    (hx : G.project x = m) :
    0 < macroMultiplicity G m := by
  unfold macroMultiplicity
  rw [Fintype.card_pos_iff]
  exact ⟨⟨x, hx⟩⟩

/--
Coarse-grained density obtained by choosing a macrostate with weight `q` and
then choosing uniformly inside its fiber.
-/
noncomputable def coarseGrainedDensity
    (G : FiniteCoarseGraining X M) (q : M → ℝ) (x : X) : ℝ :=
  q (G.project x) * (macroMultiplicity G (G.project x) : ℝ)⁻¹

/-- Pointwise surprisal of the coarse-grained reference density. -/
noncomputable def coarseGrainedSurprisal
    (G : FiniteCoarseGraining X M) (q : M → ℝ) (x : X) : ℝ :=
  -Real.log (coarseGrainedDensity G q x)

/-- Pointwise rarity of selecting the realized macrostate. -/
noncomputable def macrostateRarity
    (G : FiniteCoarseGraining X M) (q : M → ℝ) (x : X) : ℝ :=
  -Real.log (q (G.project x))

/--
The coarse-grained surprisal splits pointwise into Boltzmann multiplicity and
macrostate-selection rarity. No expectation or trace is used.
-/
theorem coarseGrainedSurprisal_eq_logMultiplicity_add_macrostateRarity
    (G : FiniteCoarseGraining X M) (q : M → ℝ) (x : X)
    (hq : 0 < q (G.project x)) :
    coarseGrainedSurprisal G q x =
      Real.log (macroMultiplicity G (G.project x) : ℝ) +
        macrostateRarity G q x := by
  have hWpos : 0 < macroMultiplicity G (G.project x) :=
    macroMultiplicity_pos_of_mem G (G.project x) x rfl
  have hWne : (macroMultiplicity G (G.project x) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hWpos)
  simp only [coarseGrainedSurprisal, coarseGrainedDensity, macrostateRarity]
  rw [Real.log_mul (ne_of_gt hq) (inv_ne_zero hWne), Real.log_inv]
  ring

/-- Dimensionless decomposition into Boltzmann entropy and macrostate rarity. -/
theorem coarseGrainedSurprisal_eq_boltzmannEntropy_add_rarity
    (G : FiniteCoarseGraining X M) (q : M → ℝ) (x : X)
    (hq : 0 < q (G.project x)) :
    coarseGrainedSurprisal G q x =
      boltzmannEntropy G x + macrostateRarity G q x := by
  rw [coarseGrainedSurprisal_eq_logMultiplicity_add_macrostateRarity G q x hq]
  rfl

/--
Support-restricted microcanonical surprisal operator for one macrosector.
It is an algebra element, not a diagonal coordinate matrix.
-/
noncomputable def microcanonicalSurprisalOperator
    {A : Type*} [Ring A] [Algebra ℝ A]
    (G : FiniteCoarseGraining X M) (P : M → A) (m : M) : A :=
  Real.log (macroMultiplicity G m : ℝ) • P m

/--
On a macrosector support, the full Boltzmann operator restricts to the
microcanonical surprisal operator.
-/
theorem boltzmannEntropyOperator_mul_macroProjector_eq_microcanonicalSurprisalOperator
    {A : Type*} [Ring A] [Algebra ℝ A]
    (G : FiniteCoarseGraining X M) (P : M → A) (m : M)
    (hOrthogonal :
      ∀ n : M, P n * P m = if n = m then P m else 0) :
    boltzmannEntropyOperator G P * P m =
      microcanonicalSurprisalOperator G P m := by
  rw [boltzmannEntropyOperator_mul_macroProjector G P m hOrthogonal]
  rfl

end InfoGeometry.Canonical.FiniteBoltzmannMacroentropy

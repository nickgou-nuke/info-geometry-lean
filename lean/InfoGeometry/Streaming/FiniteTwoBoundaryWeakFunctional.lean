import Mathlib
import InfoGeometry.Streaming.WeakValueBoundary

/-!
# Finite two-boundary weak-value functional

A pre-selected vector and a post-selected covector direction determine a
linear functional on a finite operator algebra whenever their overlap is
nonzero.  The nonzero-overlap condition is carried by the type, so the weak
ratio is total on its declared domain.

This is finite complex linear algebra.  It does not construct a measurement
instrument, a probability state, a current operator, retrocausal dynamics, or
a non-orientable spacetime quotient.
-/

noncomputable section

namespace InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

open scoped BigOperators
open SarsModularWeakValue

variable {ι : Type*} [Fintype ι]

abbrev State (ι : Type*) := ι → ℂ
abbrev Operator (ι : Type*) := Module.End ℂ (State ι)

/-- Finite Dirac pairing, conjugate-linear in the first variable. -/
def pairing (post pre : State ι) : ℂ :=
  ∑ i, star (post i) * pre i

@[simp] theorem pairing_add_left
    (post₁ post₂ pre : State ι) :
    pairing (post₁ + post₂) pre =
      pairing post₁ pre + pairing post₂ pre := by
  simp [pairing, add_mul, star_add, Finset.sum_add_distrib]

@[simp] theorem pairing_add_right
    (post pre₁ pre₂ : State ι) :
    pairing post (pre₁ + pre₂) =
      pairing post pre₁ + pairing post pre₂ := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

@[simp] theorem pairing_smul_left
    (c : ℂ) (post pre : State ι) :
    pairing (c • post) pre = star c * pairing post pre := by
  unfold pairing
  calc
    ∑ i, star ((c • post) i) * pre i =
        ∑ i, star c * (star (post i) * pre i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [Pi.smul_apply, star_mul, mul_assoc, mul_comm, mul_left_comm]
    _ = star c * ∑ i, star (post i) * pre i := by
      simp [Finset.mul_sum]

@[simp] theorem pairing_smul_right
    (c : ℂ) (post pre : State ι) :
    pairing post (c • pre) = c * pairing post pre := by
  unfold pairing
  simp only [Pi.smul_apply, mul_assoc, mul_comm, mul_left_comm,
    Finset.mul_sum, Finset.sum_mul]

@[simp] theorem pairing_zero_left (pre : State ι) :
    pairing 0 pre = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (post : State ι) :
    pairing post 0 = 0 := by
  simp [pairing]

/-- A regular pair of boundary vectors.  The overlap premise is the exact
regularity condition needed by the weak ratio. -/
structure RegularBoundaryPair (ι : Type*) [Fintype ι] where
  pre : State ι
  post : State ι
  overlap_ne : pairing post pre ≠ 0

variable (p : RegularBoundaryPair ι)

/-- Boundary overlap `<post|pre>`. -/
def overlap : ℂ :=
  pairing p.post p.pre

/-- Transition numerator `<post|A|pre>`. -/
def numerator (A : Operator ι) : ℂ :=
  pairing p.post (A p.pre)

/-- The total weak-value functional on the regular boundary-pair domain. -/
def weakValue (A : Operator ι) : ℂ :=
  numerator p A / overlap p

@[simp] theorem overlap_ne : overlap p ≠ 0 :=
  p.overlap_ne

@[simp] theorem numerator_zero :
    numerator p (0 : Operator ι) = 0 := by
  simp [numerator]

@[simp] theorem numerator_add (A B : Operator ι) :
    numerator p (A + B) = numerator p A + numerator p B := by
  simp [numerator]

@[simp] theorem numerator_smul (c : ℂ) (A : Operator ι) :
    numerator p (c • A) = c * numerator p A := by
  simp [numerator]

@[simp] theorem numerator_sub (A B : Operator ι) :
    numerator p (A - B) = numerator p A - numerator p B := by
  simp [numerator]

@[simp] theorem weakValue_zero :
    weakValue p (0 : Operator ι) = 0 := by
  simp [weakValue]

theorem weakValue_add (A B : Operator ι) :
    weakValue p (A + B) = weakValue p A + weakValue p B := by
  simp [weakValue, add_div]

theorem weakValue_sub (A B : Operator ι) :
    weakValue p (A - B) = weakValue p A - weakValue p B := by
  simp [weakValue, sub_div]

theorem weakValue_smul (c : ℂ) (A : Operator ι) :
    weakValue p (c • A) = c * weakValue p A := by
  simp only [weakValue, numerator_smul]
  ring

@[simp] theorem weakValue_one :
    weakValue p (1 : Operator ι) = 1 := by
  simp [weakValue, numerator, overlap, p.overlap_ne]

/-- Weak values form a native complex-linear functional on finite
endomorphisms. -/
def weakValueLinear : Operator ι →ₗ[ℂ] ℂ where
  toFun := weakValue p
  map_add' := weakValue_add p
  map_smul' c A := by
    simpa only [smul_eq_mul] using weakValue_smul p c A

@[simp] theorem weakValueLinear_apply (A : Operator ι) :
    weakValueLinear p A = weakValue p A := rfl

/-- Every operator balance law descends through the weak-value functional. -/
theorem weakValue_operator_balance
    (A₀ A₁ incoming outgoing : Operator ι)
    (hbalance : A₁ - A₀ = incoming - outgoing) :
    weakValue p A₁ - weakValue p A₀ =
      weakValue p incoming - weakValue p outgoing := by
  have h := congrArg (fun A : Operator ι => weakValueLinear p A) hbalance
  simpa only [map_sub, weakValueLinear_apply] using h

/-- If both endpoint density weak values vanish, an operator continuity law
forces equality of the incoming and outgoing weak fluxes.  Their common value
need not be zero; nonzero flow still requires a separately constructed current
operator and dynamics. -/
theorem weak_flux_conserved_of_zero_endpoint_density
    (A₀ A₁ incoming outgoing : Operator ι)
    (hbalance : A₁ - A₀ = incoming - outgoing)
    (h₀ : weakValue p A₀ = 0)
    (h₁ : weakValue p A₁ = 0) :
    weakValue p incoming = weakValue p outgoing := by
  have h := weakValue_operator_balance p A₀ A₁ incoming outgoing hbalance
  rw [h₁, h₀, sub_self] at h
  exact sub_eq_zero.mp h.symm

/-- Nonzero rescaling of the pre-selected vector. -/
def rescalePre (c : ℂ) (hc : c ≠ 0) : RegularBoundaryPair ι where
  pre := c • p.pre
  post := p.post
  overlap_ne := by
    rw [pairing_smul_right]
    exact mul_ne_zero hc p.overlap_ne

/-- Nonzero rescaling of the post-selected vector. -/
def rescalePost (c : ℂ) (hc : c ≠ 0) : RegularBoundaryPair ι where
  pre := p.pre
  post := c • p.post
  overlap_ne := by
    rw [pairing_smul_left]
    have hstar : star c ≠ 0 := by simpa using hc
    exact mul_ne_zero hstar p.overlap_ne

/-- Weak values depend only on the ray of the pre-selected vector. -/
theorem weakValue_rescalePre
    (c : ℂ) (hc : c ≠ 0) (A : Operator ι) :
    weakValue (rescalePre p c hc) A = weakValue p A := by
  unfold weakValue numerator overlap rescalePre
  rw [A.map_smul, pairing_smul_right, pairing_smul_right]
  field_simp [hc, p.overlap_ne] <;> ring

/-- Weak values depend only on the ray of the post-selected vector. -/
theorem weakValue_rescalePost
    (c : ℂ) (hc : c ≠ 0) (A : Operator ι) :
    weakValue (rescalePost p c hc) A = weakValue p A := by
  unfold weakValue numerator overlap rescalePost
  rw [pairing_smul_left, pairing_smul_left]
  have hstar : star c ≠ 0 := by simpa using hc
  field_simp [hstar, p.overlap_ne] <;> ring

/-! ### Compatibility with the existing guarded two-level owner -/

/-- The existing explicit `2 × 2` matrix action as a native endomorphism. -/
def legacyMatrixEnd (A : M2C) : Operator (Fin 2) where
  toFun := matVec A
  map_add' x y := by
    ext i
    fin_cases i <;> simp [matVec] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [matVec]
    all_goals ring

/-- The generic pairing specializes to the repository's original two-level
pairing. -/
theorem pairing_fin2_eq_legacy_cinner (post pre : State2) :
    pairing post pre = cinner post pre := by
  simp [pairing, cinner, Fin.sum_univ_two]

/-- Turn a regular legacy pair into the proof-carrying generic pair. -/
def ofLegacyRegularPair
    (pre post : State2) (h : weakDenominator pre post ≠ 0) :
    RegularBoundaryPair (Fin 2) where
  pre := pre
  post := post
  overlap_ne := by
    simpa [pairing, weakDenominator, cinner, Fin.sum_univ_two] using h

/-- On the regular domain, the total generic functional is exactly the value
inside the existing Option-valued owner. -/
theorem weakValue_ofLegacyRegularPair
    (A : M2C) (pre post : State2)
    (h : weakDenominator pre post ≠ 0) :
    weakValue (ofLegacyRegularPair pre post h) (legacyMatrixEnd A) =
      weakNumerator A pre post / weakDenominator pre post := by
  change pairing post (matVec A pre) / pairing post pre =
    cinner post (matVec A pre) / cinner post pre
  simpa only [pairing_fin2_eq_legacy_cinner]

/-- Exact compatibility with `SarsModularWeakValue.weakValue?`. -/
theorem some_weakValue_eq_legacy
    (A : M2C) (pre post : State2)
    (h : weakDenominator pre post ≠ 0) :
    some (weakValue (ofLegacyRegularPair pre post h) (legacyMatrixEnd A)) =
      weakValue? A pre post := by
  rw [weak_value_some_of_nonorthogonal A pre post h]
  congr 1
  exact weakValue_ofLegacyRegularPair A pre post h

end InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

end noncomputable section

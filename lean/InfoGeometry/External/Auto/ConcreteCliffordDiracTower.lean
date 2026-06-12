import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.ConcreteCliffordDiracTower

open Complex

/--
Finite cutoff spinor stage.  We use `ℕ → ℂ` with only the first `2^n`
coordinates read by `stageInner`; this avoids quotienting finite support while
keeping every proof concrete and finite.
-/
def StageSpace (_n : ℕ) : Type :=
  ℕ → ℂ

instance (n : ℕ) : AddCommGroup (StageSpace n) := by
  unfold StageSpace
  infer_instance

instance (n : ℕ) : Module ℂ (StageSpace n) := by
  unfold StageSpace
  infer_instance

/-- Finite cutoff inner product on the first `2^n` coordinates. -/
def stageInner (n : ℕ) (f g : StageSpace n) : ℂ :=
  ∑ i ∈ Finset.range (2 ^ n), star (f i) * g i

/-- Concrete diagonal finite Dirac operator with real scalar stage weight. -/
def Dfinite (n : ℕ) (f : StageSpace n) : StageSpace n :=
  fun i => (n : ℂ) * f i

/-- Multiplication by a real natural scalar is self-adjoint for `stageInner`. -/
theorem Dfinite_self_adjoint (n : ℕ) (f g : StageSpace n) :
    stageInner n f (Dfinite n g) = stageInner n (Dfinite n f) g := by
  unfold stageInner Dfinite
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_assoc, mul_comm]

/-- Vacuum-extension bonding map: keep the old finite cutoff and zero the new tail. -/
def bond (n : ℕ) (f : StageSpace n) : StageSpace (n + 1) :=
  fun i => if i < 2 ^ n then f i else 0

private theorem sum_range_if_lt_eq_sum_range
    {N M : ℕ} (hNM : N ≤ M) (F : ℕ → ℂ) :
    (∑ i ∈ Finset.range M, (if i < N then F i else 0)) =
      ∑ i ∈ Finset.range N, F i := by
  have hfilter :
      (Finset.range M).filter (fun i => i < N) = Finset.range N := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
    · intro hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_of_lt_of_le hiN hNM), hiN⟩
  rw [← hfilter]
  rw [Finset.sum_filter]

/-- The bonding map preserves the finite cutoff inner product. -/
theorem bond_isometry (n : ℕ) (f g : StageSpace n) :
    stageInner (n + 1) (bond n f) (bond n g) = stageInner n f g := by
  unfold stageInner bond
  have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ n)
  calc
    (∑ i ∈ Finset.range (2 ^ (n + 1)),
        star (if i < 2 ^ n then f i else 0) *
          (if i < 2 ^ n then g i else 0))
        =
      ∑ i ∈ Finset.range (2 ^ (n + 1)),
        (if i < 2 ^ n then star (f i) * g i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i < 2 ^ n <;> simp [h]
    _ = ∑ i ∈ Finset.range (2 ^ n), star (f i) * g i := by
          exact sum_range_if_lt_eq_sum_range hpow (fun i => star (f i) * g i)

/--
Concrete finite-stage synthesis:
finite Dirac operators are self-adjoint and the bonding maps preserve the
finite cutoff inner product.
-/
theorem concrete_clifford_tower_synthesis :
    (∀ n f g, stageInner n f (Dfinite n g) = stageInner n (Dfinite n f) g) ∧
    (∀ n f g, stageInner (n + 1) (bond n f) (bond n g) = stageInner n f g) := by
  exact ⟨Dfinite_self_adjoint, bond_isometry⟩

/-!
## Operator-valued Clifford/Cuntz finite sums

The cutoff model above gives a concrete finite coordinate tower.  The following
section records the noncommutative finite-stage Dirac operator as a real-weighted
sum of creation/annihilation adjoint pairs.
-/

/-- Creation/annihilation generators indexed by a finite mode type. -/
structure CliffordCuntzGenerators
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type*) where
  creation : ι → H →L[ℂ] H
  annihilation : ι → H →L[ℂ] H
  creation_adjoint :
    ∀ i x y, inner ℂ x (creation i y) = inner ℂ (annihilation i x) y
  annihilation_adjoint :
    ∀ i x y, inner ℂ x (annihilation i y) = inner ℂ (creation i x) y

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-- Majorana mode `C_i + A_i`. -/
def majoranaMode (G : CliffordCuntzGenerators H ι) (i : ι) : H →L[ℂ] H :=
  G.creation i + G.annihilation i

/-- Energy-weighted finite Clifford/Cuntz Dirac operator. -/
def cuntzDiracFinite [Fintype ι] (G : CliffordCuntzGenerators H ι) (E : ι → ℝ) : H →L[ℂ] H :=
  ∑ i : ι, (E i : ℂ) • majoranaMode G i

/-- Each creation/annihilation pair gives a self-adjoint Majorana mode. -/
theorem majoranaMode_self_adjoint
    (G : CliffordCuntzGenerators H ι) (i : ι) (x y : H) :
    inner ℂ x (majoranaMode G i y) = inner ℂ (majoranaMode G i x) y := by
  simp [majoranaMode, G.creation_adjoint i x y, G.annihilation_adjoint i x y,
    add_comm]

/-- Same statement as a `LinearMap.IsSymmetric` theorem. -/
theorem majoranaMode_isSymmetric
    (G : CliffordCuntzGenerators H ι) (i : ι) :
    LinearMap.IsSymmetric (majoranaMode G i : H →ₗ[ℂ] H) := by
  intro x y
  simpa [eq_comm] using (majoranaMode_self_adjoint (G := G) i x y)

/-- The genuine finite Clifford/Cuntz Dirac operator is self-adjoint.
It is a finite sum of self-adjoint Majorana modes with real energy weights.
-/
theorem cuntzDiracFinite_isSymmetric
    [Fintype ι]
    (G : CliffordCuntzGenerators H ι) (E : ι → ℝ) :
    LinearMap.IsSymmetric (cuntzDiracFinite G E : H →ₗ[ℂ] H) := by
  classical
  have hsum :
      LinearMap.IsSymmetric
        (Finset.sum (Finset.univ : Finset ι)
          (fun i : ι => (E i : ℂ) • (majoranaMode G i : H →ₗ[ℂ] H)) : H →ₗ[ℂ] H) := by
    refine LinearMap.isSymmetric_sum (𝕜 := ℂ) (E := H)
      (T := fun i => (E i : ℂ) • (majoranaMode G i : H →ₗ[ℂ] H))
      (s := (Finset.univ : Finset ι)) ?_
    intro i _
    exact (majoranaMode_isSymmetric (G := G) i).smul (by simp [Complex.conj_ofReal])
  simpa [cuntzDiracFinite] using hsum

/-- Corollary in inner-product form. -/
theorem cuntzDiracFinite_self_adjoint
    [Fintype ι]
    (G : CliffordCuntzGenerators H ι) (E : ι → ℝ) (x y : H) :
    inner ℂ x (cuntzDiracFinite G E y) =
      inner ℂ (cuntzDiracFinite G E x) y := by
  simpa [eq_comm] using (cuntzDiracFinite_isSymmetric (G := G) (E := E)) x y

/-- Synthesis package for the operator-valued finite Clifford/Cuntz Dirac model. -/
theorem concrete_cuntz_dirac_synthesis
    [Fintype ι]
    (G : CliffordCuntzGenerators H ι) (E : ι → ℝ) :
    ∀ x y : H,
      inner ℂ x (cuntzDiracFinite G E y) =
        inner ℂ (cuntzDiracFinite G E x) y :=
  cuntzDiracFinite_self_adjoint G E

end InfoGeometry.Quantum.ConcreteCliffordDiracTower

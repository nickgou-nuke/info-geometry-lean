import InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

/-!
# Eigenspace readout for the projectivized double-Witt flow

The two distinguished projective lines are obtained from the two-dimensional
eigenspaces of the linear tetrad boost.  This file deliberately proves the
pointwise fixed-line statements only; it does not claim a classification of
all projective fixed points.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitRealNullTetradProjectiveFixedEigenspaces

open InfoGeometry.Clifford.SplitRealNullTetrad
open InfoGeometry.Lie.SplitRealNullTetradZornBridge
open InfoGeometry.Lie.SplitRealNullTetradZornBridge.Tetrad
open InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

abbrev Carrier := InfoGeometry.Clifford.SplitRealNullTetrad.Carrier
abbrev TetradProjective := ℙ ℝ Carrier

private theorem doubleWittBoost_ne_zero
    (t : ℝ) (X : Carrier) (hX : X ≠ 0) :
    doubleWittBoost t X ≠ 0 := by
  intro h
  apply hX
  have h' := congrArg (doubleWittBoost (-t)) h
  simpa [doubleWittBoost_neg_apply] using h'

def positiveEigenspace : Submodule ℝ Carrier :=
  Submodule.span ℝ {causalMinus, entropyMinus}

def negativeEigenspace : Submodule ℝ Carrier :=
  Submodule.span ℝ {causalPlus, entropyPlus}

def positiveProjectiveLine : Set TetradProjective :=
  {p | ∃ (X : Carrier) (hX : X ≠ 0),
      p = Projectivization.mk ℝ X hX ∧ X ∈ positiveEigenspace}

def negativeProjectiveLine : Set TetradProjective :=
  {p | ∃ (X : Carrier) (hX : X ≠ 0),
      p = Projectivization.mk ℝ X hX ∧ X ∈ negativeEigenspace}

theorem mem_positiveEigenspace_iff (X : Carrier) :
    X ∈ positiveEigenspace ↔ X 0 = X 1 ∧ X 2 = X 3 := by
  rw [positiveEigenspace, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp [causalMinus, entropyMinus]
  · rintro ⟨h01, h23⟩
    refine ⟨X 0 + X 1, X 2 + X 3, ?_⟩
    funext i
    fin_cases i
    · simp [causalMinus, entropyMinus, h01, h23] <;> ring
    · simp [causalMinus, entropyMinus, h01, h23] <;> ring
    · simp [causalMinus, entropyMinus, h01, h23] <;> ring
    · simp [causalMinus, entropyMinus, h01, h23] <;> ring

theorem mem_negativeEigenspace_iff (X : Carrier) :
    X ∈ negativeEigenspace ↔ X 0 = -X 1 ∧ X 2 = -X 3 := by
  rw [negativeEigenspace, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp [causalPlus, entropyPlus]
  · rintro ⟨h01, h23⟩
    refine ⟨X 0 - X 1, X 2 - X 3, ?_⟩
    funext i
    fin_cases i
    · simp [causalPlus, entropyPlus, h01, h23] <;> ring
    · simp [causalPlus, entropyPlus, h01, h23] <;> ring
    · simp [causalPlus, entropyPlus, h01, h23] <;> ring
    · simp [causalPlus, entropyPlus, h01, h23] <;> ring

theorem doubleWittBoost_mem_positiveEigenspace
    (t : ℝ) {X : Carrier} (hX : X ∈ positiveEigenspace) :
    doubleWittBoost t X = Real.exp t • X := by
  refine Submodule.span_induction
    (p := fun x _ => doubleWittBoost t x = Real.exp t • x)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with rfl | rfl
    · exact doubleWittBoost_causalMinus t
    · exact doubleWittBoost_entropyMinus t
  · simp [doubleWittBoost]
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, smul_add]
  · intro a x _ hx
    simpa [map_smul, hx, smul_smul, mul_comm]

theorem doubleWittBoost_mem_negativeEigenspace
    (t : ℝ) {X : Carrier} (hX : X ∈ negativeEigenspace) :
    doubleWittBoost t X = Real.exp (-t) • X := by
  refine Submodule.span_induction
    (p := fun x _ => doubleWittBoost t x = Real.exp (-t) • x)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with rfl | rfl
    · exact doubleWittBoost_causalPlus t
    · exact doubleWittBoost_entropyPlus t
  · simp [doubleWittBoost]
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, smul_add]
  · intro a x _ hx
    simpa [map_smul, hx, smul_smul, mul_comm]

theorem fixed_scalar_mem_eigenspace_union
    (t : ℝ) (ht : t ≠ 0) (X : Carrier) (a : ℝ)
    (hX : a • X = doubleWittBoost t X) :
    X ∈ positiveEigenspace ∨ X ∈ negativeEigenspace := by
  have hp0 : a * (X 0 + X 1) = Real.exp t * (X 0 + X 1) := by
    have h := congrArg (fun Y : Carrier => Y 0 + Y 1) hX
    simp [doubleWittBoost, smul_eq_mul] at h
    calc
      a * (X 0 + X 1) = a * X 0 + a * X 1 := by ring
      _ = Real.cosh t * X 0 + Real.sinh t * X 1 +
          (Real.sinh t * X 0 + Real.cosh t * X 1) := h
      _ = (Real.cosh t + Real.sinh t) * (X 0 + X 1) := by ring
      _ = Real.exp t * (X 0 + X 1) := by rw [Real.cosh_add_sinh]
  have hp1 : a * (X 2 + X 3) = Real.exp t * (X 2 + X 3) := by
    have h := congrArg (fun Y : Carrier => Y 2 + Y 3) hX
    simp [doubleWittBoost, smul_eq_mul] at h
    calc
      a * (X 2 + X 3) = a * X 2 + a * X 3 := by ring
      _ = Real.cosh t * X 2 + Real.sinh t * X 3 +
          (Real.sinh t * X 2 + Real.cosh t * X 3) := h
      _ = (Real.cosh t + Real.sinh t) * (X 2 + X 3) := by ring
      _ = Real.exp t * (X 2 + X 3) := by rw [Real.cosh_add_sinh]
  have hm0 : a * (X 0 - X 1) = Real.exp (-t) * (X 0 - X 1) := by
    have h := congrArg (fun Y : Carrier => Y 0 - Y 1) hX
    simp [doubleWittBoost, smul_eq_mul] at h
    calc
      a * (X 0 - X 1) = a * X 0 - a * X 1 := by ring
      _ = Real.cosh t * X 0 + Real.sinh t * X 1 -
          (Real.sinh t * X 0 + Real.cosh t * X 1) := h
      _ = (Real.cosh t - Real.sinh t) * (X 0 - X 1) := by ring
      _ = Real.exp (-t) * (X 0 - X 1) := by rw [Real.cosh_sub_sinh]
  have hm1 : a * (X 2 - X 3) = Real.exp (-t) * (X 2 - X 3) := by
    have h := congrArg (fun Y : Carrier => Y 2 - Y 3) hX
    simp [doubleWittBoost, smul_eq_mul] at h
    calc
      a * (X 2 - X 3) = a * X 2 - a * X 3 := by ring
      _ = Real.cosh t * X 2 + Real.sinh t * X 3 -
          (Real.sinh t * X 2 + Real.cosh t * X 3) := h
      _ = (Real.cosh t - Real.sinh t) * (X 2 - X 3) := by ring
      _ = Real.exp (-t) * (X 2 - X 3) := by rw [Real.cosh_sub_sinh]
  have scalar_of_ne {q c : ℝ} (hq : q ≠ 0) (h : a * q = c * q) : a = c := by
    have hp : (a - c) * q = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hac | hq'
    · exact sub_eq_zero.mp hac
    · exact False.elim (hq hq')
  have exp_ne : Real.exp t ≠ Real.exp (-t) := by
    intro h
    have ht' : t = -t := Real.exp_injective h
    exact ht (by linarith)
  by_cases hp : X 0 + X 1 = 0 ∧ X 2 + X 3 = 0
  · right
    apply (mem_negativeEigenspace_iff X).2
    constructor <;> linarith [hp.1, hp.2]
  · left
    apply (mem_positiveEigenspace_iff X).2
    have ha : a = Real.exp t := by
      by_cases hs0 : X 0 + X 1 = 0
      · exact scalar_of_ne (by intro hs1; exact hp ⟨hs0, hs1⟩) hp1
      · exact scalar_of_ne hs0 hp0
    have hd0 : X 0 - X 1 = 0 := by
      by_contra hne
      exact exp_ne (ha.symm.trans (scalar_of_ne hne hm0))
    have hd1 : X 2 - X 3 = 0 := by
      by_contra hne
      exact exp_ne (ha.symm.trans (scalar_of_ne hne hm1))
    constructor <;> linarith

theorem projective_fixed_mem_eigenspace_union
    (t : ℝ) (ht : t ≠ 0) (X : Carrier) (hX : X ≠ 0)
    (hfixed : Projectivization.mk ℝ (doubleWittBoost t X)
        (doubleWittBoost_ne_zero t X hX) =
      Projectivization.mk ℝ X hX) :
    X ∈ positiveEigenspace ∨ X ∈ negativeEigenspace := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℝ (doubleWittBoost t X) X
      (doubleWittBoost_ne_zero t X hX) hX).mp hfixed
  exact fixed_scalar_mem_eigenspace_union t ht X a ha

theorem projective_fixed_mem_eigenspace_union_rep
    (t : ℝ) (ht : t ≠ 0) (p : TetradProjective)
    (hfixed : doubleWittBoostProjectiveMap t p = p) :
    ∃ (X : Carrier) (hX : X ≠ 0),
      p = Projectivization.mk ℝ X hX ∧
        (X ∈ positiveEigenspace ∨ X ∈ negativeEigenspace) := by
  induction p using Projectivization.ind with
  | h X hX =>
      refine ⟨X, hX, rfl, ?_⟩
      apply projective_fixed_mem_eigenspace_union t ht X hX
      simpa only [doubleWittBoostProjectiveMap_mk] using hfixed

theorem positiveEigenspace_projective_fixed
    (t : ℝ) (X : Carrier) (hX : X ≠ 0)
    (hXE : X ∈ positiveEigenspace) :
    Projectivization.mk ℝ (doubleWittBoost t X)
        (by exact doubleWittBoost_ne_zero t X hX) =
      Projectivization.mk ℝ X hX := by
  apply (Projectivization.mk_eq_mk_iff' ℝ (doubleWittBoost t X) X
    (doubleWittBoost_ne_zero t X hX) hX).2
  refine ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), ?_⟩
  simpa [Units.smul_def] using
    (doubleWittBoost_mem_positiveEigenspace t hXE).symm

theorem negativeEigenspace_projective_fixed
    (t : ℝ) (X : Carrier) (hX : X ≠ 0)
    (hXE : X ∈ negativeEigenspace) :
    Projectivization.mk ℝ (doubleWittBoost t X)
        (by exact doubleWittBoost_ne_zero t X hX) =
      Projectivization.mk ℝ X hX := by
  apply (Projectivization.mk_eq_mk_iff' ℝ (doubleWittBoost t X) X
    (doubleWittBoost_ne_zero t X hX) hX).2
  refine ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), ?_⟩
  simpa [Units.smul_def] using
    (doubleWittBoost_mem_negativeEigenspace t hXE).symm

theorem projective_fixed_iff_mem_projectiveEigenspace_union
    (t : ℝ) (ht : t ≠ 0) (p : TetradProjective) :
    doubleWittBoostProjectiveMap t p = p ↔
      p ∈ positiveProjectiveLine ∨ p ∈ negativeProjectiveLine := by
  constructor
  · intro hfixed
    obtain ⟨X, hX, hp, hsector⟩ :=
      projective_fixed_mem_eigenspace_union_rep t ht p hfixed
    rcases hsector with hpos | hneg
    · exact Or.inl ⟨X, hX, hp, hpos⟩
    · exact Or.inr ⟨X, hX, hp, hneg⟩
  · rintro (hpos | hneg)
    · obtain ⟨X, hX, rfl, hXE⟩ := hpos
      simpa only [doubleWittBoostProjectiveMap_mk] using
        (positiveEigenspace_projective_fixed t X hX hXE)
    · obtain ⟨X, hX, rfl, hXE⟩ := hneg
      simpa only [doubleWittBoostProjectiveMap_mk] using
        (negativeEigenspace_projective_fixed t X hX hXE)

end InfoGeometry.Lie.SplitRealNullTetradProjectiveFixedEigenspaces

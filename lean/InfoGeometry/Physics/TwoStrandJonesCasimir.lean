/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Two-strand Jones projector and spin Casimir

The carrier is the finite coordinate realization of two spinor factors,
`Fin 2 → Fin 2 → ℂ`.  It is the standard basis model of the tensor product
of two two-component spinor spaces.  All identities below are explicit finite
matrix identities; no infinite-dimensional or representation-theoretic
assumption is used.
-/

noncomputable section

namespace InfoGeometry.Physics.TwoStrandJonesCasimir

open scoped Matrix

abbrev Spinor := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev TwoStrandState := Fin 2 → Fin 2 → ℂ
abbrev TwoStrandOperator := Module.End ℂ TwoStrandState

def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def leftAction (A : Matrix (Fin 2) (Fin 2) ℂ) : TwoStrandOperator where
  toFun ψ i j := ∑ k : Fin 2, A i k * ψ k j
  map_add' ψ φ := by
    funext i j
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c ψ := by
    funext i j
    simp [Fin.sum_univ_succ]
    ring

def rightAction (A : Matrix (Fin 2) (Fin 2) ℂ) : TwoStrandOperator where
  toFun ψ i j := ∑ k : Fin 2, A j k * ψ i k
  map_add' ψ φ := by
    funext i j
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c ψ := by
    funext i j
    simp [Fin.sum_univ_succ]
    ring

def singletProjector : TwoStrandOperator where
  toFun ψ i j :=
    let c := (1 / 2 : ℂ) * (ψ 0 1 - ψ 1 0)
    if i = 0 ∧ j = 1 then c
    else if i = 1 ∧ j = 0 then -c else 0
  map_add' ψ φ := by
    funext i j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c ψ := by
    funext i j
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [RingHom.id_apply] <;> ring

def spinX : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaX + rightAction sigmaX)

def spinY : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaY + rightAction sigmaY)

def spinZ : TwoStrandOperator :=
  (1 / 2 : ℂ) • (leftAction sigmaZ + rightAction sigmaZ)

def spinSquared : TwoStrandOperator :=
  spinX.comp spinX + spinY.comp spinY + spinZ.comp spinZ

theorem singletProjector_idem :
    singletProjector.comp singletProjector = singletProjector := by
  apply LinearMap.ext
  intro ψ
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [singletProjector]
    <;> ring

theorem spinSquared_eq_two_complement_singlet :
    spinSquared = 2 • ((1 : TwoStrandOperator) - singletProjector) := by
  apply LinearMap.ext
  intro ψ
  funext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [spinSquared, spinX, spinY, spinZ, leftAction, rightAction,
      sigmaX, sigmaY, sigmaZ, singletProjector, Fin.sum_univ_succ,
      LinearMap.comp_apply]
    simp_rw [← mul_assoc]
    try simp [Complex.I_mul_I]
    ring_nf
    rw [Complex.I_sq]
    ring

def twoStrandCasimir (M : ℂ) : TwoStrandOperator :=
  (-M ^ 2) • spinSquared

theorem twoStrandCasimir_eq_projector_polynomial (M : ℂ) :
    twoStrandCasimir M =
      (-2 * M ^ 2) • ((1 : TwoStrandOperator) - singletProjector) := by
  rw [twoStrandCasimir, spinSquared_eq_two_complement_singlet]
  module

/-- Orthogonal spin-1 triplet projector `P_triplet = I - P_singlet`. -/
def tripletProjector : TwoStrandOperator :=
  (1 : TwoStrandOperator) - singletProjector

theorem singlet_add_triplet :
    singletProjector + tripletProjector = (1 : TwoStrandOperator) := by
  dsimp [tripletProjector]
  abel

theorem tripletProjector_idem :
    tripletProjector.comp tripletProjector = tripletProjector := by
  dsimp [tripletProjector]
  change ((1 : TwoStrandOperator) - singletProjector) *
      ((1 : TwoStrandOperator) - singletProjector) = 1 - singletProjector
  rw [sub_mul, one_mul, mul_sub, mul_one]
  change 1 - singletProjector - (singletProjector - singletProjector.comp singletProjector) =
    1 - singletProjector
  rw [singletProjector_idem, sub_self, sub_zero]

theorem singlet_triplet_orthogonal :
    singletProjector.comp tripletProjector = 0 ∧
      tripletProjector.comp singletProjector = 0 := by
  dsimp [tripletProjector]
  constructor
  · change singletProjector * ((1 : TwoStrandOperator) - singletProjector) = 0
    rw [mul_sub, mul_one]
    change singletProjector - singletProjector.comp singletProjector = 0
    rw [singletProjector_idem, sub_self]
  · change ((1 : TwoStrandOperator) - singletProjector) * singletProjector = 0
    rw [sub_mul, one_mul]
    change singletProjector - singletProjector.comp singletProjector = 0
    rw [singletProjector_idem, sub_self]

theorem spinSquared_eq_two_triplet :
    spinSquared = (2 : ℂ) • tripletProjector := by
  simpa [tripletProjector, two_smul] using spinSquared_eq_two_complement_singlet

theorem spinSquared_on_singlet :
    spinSquared.comp singletProjector = 0 := by
  rw [spinSquared_eq_two_triplet]
  change ((2 : ℂ) • tripletProjector) * singletProjector = 0
  rw [Algebra.smul_mul_assoc]
  change (2 : ℂ) • tripletProjector.comp singletProjector = 0
  rw [singlet_triplet_orthogonal.2, smul_zero]

theorem spinSquared_on_triplet :
    spinSquared.comp tripletProjector = (2 : ℂ) • tripletProjector := by
  rw [spinSquared_eq_two_triplet]
  change ((2 : ℂ) • tripletProjector) * tripletProjector = (2 : ℂ) • tripletProjector
  rw [Algebra.smul_mul_assoc]
  change (2 : ℂ) • tripletProjector.comp tripletProjector = (2 : ℂ) • tripletProjector
  rw [tripletProjector_idem]

/-- Dirac two-spinor exchange (swap) operator `P_12(ψ)(i, j) = ψ(j, i)`. -/
def spinSwap : TwoStrandOperator where
  toFun ψ i j := ψ j i
  map_add' _ _ := by funext i j; rfl
  map_smul' _ _ := by funext i j; rfl

theorem spinSwap_sq :
    spinSwap.comp spinSwap = (1 : TwoStrandOperator) := by
  apply LinearMap.ext
  intro ψ
  funext i j
  rfl

/-- Dirac spin-exchange identity: `P_12 = P_triplet - P_singlet` (`+1` on spin triplet
`S = 1`, `-1` on spin singlet `S = 0`). -/
theorem spinSwap_eq_triplet_sub_singlet :
    spinSwap = tripletProjector - singletProjector := by
  apply LinearMap.ext
  intro ψ
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSwap, tripletProjector, singletProjector] <;> ring

theorem spinSwap_on_singlet :
    spinSwap.comp singletProjector = -singletProjector := by
  rw [spinSwap_eq_triplet_sub_singlet]
  change (tripletProjector - singletProjector) * singletProjector = -singletProjector
  rw [sub_mul]
  change tripletProjector.comp singletProjector - singletProjector.comp singletProjector =
    -singletProjector
  rw [singlet_triplet_orthogonal.2, singletProjector_idem, zero_sub]

theorem spinSwap_on_triplet :
    spinSwap.comp tripletProjector = tripletProjector := by
  rw [spinSwap_eq_triplet_sub_singlet]
  change (tripletProjector - singletProjector) * tripletProjector = tripletProjector
  rw [sub_mul]
  change tripletProjector.comp tripletProjector - singletProjector.comp tripletProjector =
    tripletProjector
  rw [tripletProjector_idem, singlet_triplet_orthogonal.1, sub_zero]

section TwoNucleonSpinIsospin

/-- Two-nucleon `(spin₁, spin₂, isospin₁, isospin₂)` state carrier. -/
abbrev TwoNucleonState := Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Linear endomorphisms on the two-nucleon spin-isospin carrier. -/
abbrev TwoNucleonOperator := Module.End ℂ TwoNucleonState

private def twoStrandBasis (a b : Fin 2) : TwoStrandState :=
  fun i j => if i = a ∧ j = b then 1 else 0

private lemma twoStrand_eq_sum_basis (φ : TwoStrandState) :
    φ = ∑ a : Fin 2, ∑ b : Fin 2, φ a b • twoStrandBasis a b := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [twoStrandBasis]

/-- Lift a two-strand spin operator to act on the spin indices `(s₁, s₂)`. -/
def spinLift (A : TwoStrandOperator) : TwoNucleonOperator where
  toFun ψ s₁ s₂ t₁ t₂ := A (fun u v => ψ u v t₁ t₂) s₁ s₂
  map_add' ψ₁ ψ₂ := by
    funext s₁ s₂ t₁ t₂
    change A (fun u v => ψ₁ u v t₁ t₂ + ψ₂ u v t₁ t₂) s₁ s₂ =
      A (fun u v => ψ₁ u v t₁ t₂) s₁ s₂ + A (fun u v => ψ₂ u v t₁ t₂) s₁ s₂
    rw [show (fun u v => ψ₁ u v t₁ t₂ + ψ₂ u v t₁ t₂) =
        (fun u v => ψ₁ u v t₁ t₂) + (fun u v => ψ₂ u v t₁ t₂) from rfl, map_add]
    rfl
  map_smul' c ψ := by
    funext s₁ s₂ t₁ t₂
    change A (fun u v => c * ψ u v t₁ t₂) s₁ s₂ = c * A (fun u v => ψ u v t₁ t₂) s₁ s₂
    rw [show (fun u v => c * ψ u v t₁ t₂) = c • (fun u v => ψ u v t₁ t₂) from rfl, map_smul]
    rfl

/-- Lift a two-strand isospin operator to act on the isospin indices `(t₁, t₂)`. -/
def isospinLift (B : TwoStrandOperator) : TwoNucleonOperator where
  toFun ψ s₁ s₂ t₁ t₂ := B (fun u v => ψ s₁ s₂ u v) t₁ t₂
  map_add' ψ₁ ψ₂ := by
    funext s₁ s₂ t₁ t₂
    change B (fun u v => ψ₁ s₁ s₂ u v + ψ₂ s₁ s₂ u v) t₁ t₂ =
      B (fun u v => ψ₁ s₁ s₂ u v) t₁ t₂ + B (fun u v => ψ₂ s₁ s₂ u v) t₁ t₂
    rw [show (fun u v => ψ₁ s₁ s₂ u v + ψ₂ s₁ s₂ u v) =
        (fun u v => ψ₁ s₁ s₂ u v) + (fun u v => ψ₂ s₁ s₂ u v) from rfl, map_add]
    rfl
  map_smul' c ψ := by
    funext s₁ s₂ t₁ t₂
    change B (fun u v => c * ψ s₁ s₂ u v) t₁ t₂ = c * B (fun u v => ψ s₁ s₂ u v) t₁ t₂
    rw [show (fun u v => c * ψ s₁ s₂ u v) = c • (fun u v => ψ s₁ s₂ u v) from rfl, map_smul]
    rfl

@[simp] theorem spinLift_one : spinLift (1 : TwoStrandOperator) = 1 := rfl
@[simp] theorem isospinLift_one : isospinLift (1 : TwoStrandOperator) = 1 := rfl
@[simp] theorem spinLift_zero : spinLift (0 : TwoStrandOperator) = 0 := by ext; rfl
@[simp] theorem isospinLift_zero : isospinLift (0 : TwoStrandOperator) = 0 := by ext; rfl
private theorem spinLift_mul (A₁ A₂ : TwoStrandOperator) :
    spinLift A₁ * spinLift A₂ = spinLift (A₁.comp A₂) := rfl
private theorem isospinLift_mul (B₁ B₂ : TwoStrandOperator) :
    isospinLift B₁ * isospinLift B₂ = isospinLift (B₁.comp B₂) := rfl

theorem spinLift_comp (A₁ A₂ : TwoStrandOperator) :
    spinLift (A₁.comp A₂) = (spinLift A₁).comp (spinLift A₂) := rfl

theorem isospinLift_comp (B₁ B₂ : TwoStrandOperator) :
    isospinLift (B₁.comp B₂) = (isospinLift B₁).comp (isospinLift B₂) := rfl

theorem spinLift_add (A₁ A₂ : TwoStrandOperator) :
    spinLift (A₁ + A₂) = spinLift A₁ + spinLift A₂ := rfl

theorem isospinLift_add (B₁ B₂ : TwoStrandOperator) :
    isospinLift (B₁ + B₂) = isospinLift B₁ + isospinLift B₂ := rfl

theorem spinLift_sub (A₁ A₂ : TwoStrandOperator) :
    spinLift (A₁ - A₂) = spinLift A₁ - spinLift A₂ := rfl

theorem isospinLift_sub (B₁ B₂ : TwoStrandOperator) :
    isospinLift (B₁ - B₂) = isospinLift B₁ - isospinLift B₂ := rfl

theorem spinLift_smul (c : ℂ) (A : TwoStrandOperator) :
    spinLift (c • A) = c • spinLift A := rfl

theorem isospinLift_smul (c : ℂ) (B : TwoStrandOperator) :
    isospinLift (c • B) = c • isospinLift B := rfl

/-- Spin operators and isospin operators commute identically on `TwoNucleonState`. -/
theorem spinLift_comp_isospinLift_comm (A B : TwoStrandOperator) :
    (spinLift A).comp (isospinLift B) = (isospinLift B).comp (spinLift A) := by
  apply LinearMap.ext
  intro ψ
  funext s₁ s₂ t₁ t₂
  change A (fun u v => B (fun p q => ψ u v p q) t₁ t₂) s₁ s₂ =
    B (fun p q => A (fun u v => ψ u v p q) s₁ s₂) t₁ t₂
  have hL :
      A (fun u v => B (fun p q => ψ u v p q) t₁ t₂) s₁ s₂ =
        ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
          ψ a b c d * B (twoStrandBasis c d) t₁ t₂ * A (twoStrandBasis a b) s₁ s₂ := by
    conv_lhs => rw [twoStrand_eq_sum_basis (fun u v => B (fun p q => ψ u v p q) t₁ t₂)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    conv_lhs => rw [twoStrand_eq_sum_basis (fun p q => ψ a b p q)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  have hR :
      B (fun p q => A (fun u v => ψ u v p q) s₁ s₂) t₁ t₂ =
        ∑ c : Fin 2, ∑ d : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2,
          ψ a b c d * A (twoStrandBasis a b) s₁ s₂ * B (twoStrandBasis c d) t₁ t₂ := by
    conv_lhs => rw [twoStrand_eq_sum_basis (fun p q => A (fun u v => ψ u v p q) s₁ s₂)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    conv_lhs => rw [twoStrand_eq_sum_basis (fun u v => ψ u v c d)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [hL, hR]
  calc
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        ψ a b c d * B (twoStrandBasis c d) t₁ t₂ * A (twoStrandBasis a b) s₁ s₂)
      = ∑ a : Fin 2, ∑ c : Fin 2, ∑ b : Fin 2, ∑ d : Fin 2,
          ψ a b c d * B (twoStrandBasis c d) t₁ t₂ * A (twoStrandBasis a b) s₁ s₂ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, ∑ d : Fin 2,
          ψ a b c d * B (twoStrandBasis c d) t₁ t₂ * A (twoStrandBasis a b) s₁ s₂ := Finset.sum_comm
    _ = ∑ c : Fin 2, ∑ a : Fin 2, ∑ d : Fin 2, ∑ b : Fin 2,
          ψ a b c d * B (twoStrandBasis c d) t₁ t₂ * A (twoStrandBasis a b) s₁ s₂ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : Fin 2, ∑ d : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2,
          ψ a b c d * A (twoStrandBasis a b) s₁ s₂ * B (twoStrandBasis c d) t₁ t₂ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private theorem spinLift_mul_isospinLift_comm (A B : TwoStrandOperator) :
    spinLift A * isospinLift B = isospinLift B * spinLift A :=
  spinLift_comp_isospinLift_comm A B

/-- Isovector spin-singlet `(S = 0, T = 1)` nuclear pairing projector. -/
def projS0T1 : TwoNucleonOperator :=
  (spinLift singletProjector).comp (isospinLift tripletProjector)

/-- Isoscalar spin-triplet `(S = 1, T = 0)` deuteron pairing projector. -/
def projS1T0 : TwoNucleonOperator :=
  (spinLift tripletProjector).comp (isospinLift singletProjector)

/-- Antisymmetric spin-singlet + isospin-singlet `(S = 0, T = 0)` projector (spatially odd). -/
def projS0T0 : TwoNucleonOperator :=
  (spinLift singletProjector).comp (isospinLift singletProjector)

/-- Symmetric spin-triplet + isospin-triplet `(S = 1, T = 1)` projector (spatially odd). -/
def projS1T1 : TwoNucleonOperator :=
  (spinLift tripletProjector).comp (isospinLift tripletProjector)

/-- Total `S`-wave antisymmetric spin-isospin subspace `(S=0, T=1) ⊕ (S=1, T=0)`. -/
def antisymSWaveProj : TwoNucleonOperator :=
  projS0T1 + projS1T0

/-- Combined spin-isospin exchange operator `P^σ P^τ`. -/
def totalSpinIsospinExchange : TwoNucleonOperator :=
  (spinLift spinSwap).comp (isospinLift spinSwap)

/-- Effective two-nucleon `S`-wave pairing competition Hamiltonian:
`H_pair = -g₁ P_{S=0,T=1} - g₀ P_{S=1,T=0}` (isovector vs isoscalar/deuteron condensates). -/
def pairingCompetitionHam (g0 g1 : ℂ) : TwoNucleonOperator :=
  (-g1) • projS0T1 + (-g0) • projS1T0

theorem proj_four_sector_sum :
    projS0T1 + projS1T0 + projS0T0 + projS1T1 = (1 : TwoNucleonOperator) := by
  dsimp [projS0T1, projS1T0, projS0T0, projS1T1]
  have hspin : spinLift singletProjector + spinLift tripletProjector = 1 := by
    rw [← spinLift_add, singlet_add_triplet, spinLift_one]
  have hiso : isospinLift singletProjector + isospinLift tripletProjector = 1 := by
    rw [← isospinLift_add, singlet_add_triplet, isospinLift_one]
  calc
    _ = (spinLift singletProjector + spinLift tripletProjector).comp
          (isospinLift singletProjector + isospinLift tripletProjector) := by
        change spinLift singletProjector * isospinLift tripletProjector +
            spinLift tripletProjector * isospinLift singletProjector +
            spinLift singletProjector * isospinLift singletProjector +
            spinLift tripletProjector * isospinLift tripletProjector =
          (spinLift singletProjector + spinLift tripletProjector) *
            (isospinLift singletProjector + isospinLift tripletProjector)
        noncomm_ring
    _ = (1 : TwoNucleonOperator) := by rw [hspin, hiso]; rfl

theorem projS0T1_idem : projS0T1.comp projS0T1 = projS0T1 := by
  dsimp [projS0T1]
  change (spinLift singletProjector * isospinLift tripletProjector) *
      (spinLift singletProjector * isospinLift tripletProjector) =
    spinLift singletProjector * isospinLift tripletProjector
  have hcomm : isospinLift tripletProjector * spinLift singletProjector =
      spinLift singletProjector * isospinLift tripletProjector :=
    (spinLift_comp_isospinLift_comm singletProjector tripletProjector).symm
  calc
    _ = (spinLift singletProjector * spinLift singletProjector) *
          (isospinLift tripletProjector * isospinLift tripletProjector) := by
        rw [mul_assoc (spinLift singletProjector), ← mul_assoc (isospinLift tripletProjector),
          hcomm, mul_assoc, ← mul_assoc]
    _ = spinLift singletProjector * isospinLift tripletProjector := by
        change (spinLift (singletProjector.comp singletProjector)) *
            (isospinLift (tripletProjector.comp tripletProjector)) = _
        rw [singletProjector_idem, tripletProjector_idem]

theorem projS1T0_idem : projS1T0.comp projS1T0 = projS1T0 := by
  dsimp [projS1T0]
  change (spinLift tripletProjector * isospinLift singletProjector) *
      (spinLift tripletProjector * isospinLift singletProjector) =
    spinLift tripletProjector * isospinLift singletProjector
  have hcomm : isospinLift singletProjector * spinLift tripletProjector =
      spinLift tripletProjector * isospinLift singletProjector :=
    (spinLift_comp_isospinLift_comm tripletProjector singletProjector).symm
  calc
    _ = (spinLift tripletProjector * spinLift tripletProjector) *
          (isospinLift singletProjector * isospinLift singletProjector) := by
        rw [mul_assoc (spinLift tripletProjector), ← mul_assoc (isospinLift singletProjector),
          hcomm, mul_assoc, ← mul_assoc]
    _ = spinLift tripletProjector * isospinLift singletProjector := by
        change (spinLift (tripletProjector.comp tripletProjector)) *
            (isospinLift (singletProjector.comp singletProjector)) = _
        rw [tripletProjector_idem, singletProjector_idem]

theorem projS0T1_projS1T0_orthogonal :
    projS0T1.comp projS1T0 = 0 ∧ projS1T0.comp projS0T1 = 0 := by
  dsimp [projS0T1, projS1T0]
  constructor
  · change (spinLift singletProjector * isospinLift tripletProjector) *
        (spinLift tripletProjector * isospinLift singletProjector) = 0
    calc
      (spinLift singletProjector * isospinLift tripletProjector) *
          (spinLift tripletProjector * isospinLift singletProjector)
        = (spinLift singletProjector * (isospinLift tripletProjector * spinLift tripletProjector)) *
            isospinLift singletProjector := by simp only [mul_assoc]
      _ = (spinLift singletProjector * (spinLift tripletProjector * isospinLift tripletProjector)) *
            isospinLift singletProjector := by
          rw [← spinLift_mul_isospinLift_comm]
      _ = ((spinLift singletProjector * spinLift tripletProjector) *
            isospinLift tripletProjector) * isospinLift singletProjector := by
          simp only [mul_assoc]
      _ = 0 := by
          rw [spinLift_mul, singlet_triplet_orthogonal.1, spinLift_zero, zero_mul, zero_mul]
  · change (spinLift tripletProjector * isospinLift singletProjector) *
        (spinLift singletProjector * isospinLift tripletProjector) = 0
    calc
      (spinLift tripletProjector * isospinLift singletProjector) *
          (spinLift singletProjector * isospinLift tripletProjector)
        = (spinLift tripletProjector * (isospinLift singletProjector * spinLift singletProjector)) *
            isospinLift tripletProjector := by simp only [mul_assoc]
      _ = (spinLift tripletProjector * (spinLift singletProjector * isospinLift singletProjector)) *
            isospinLift tripletProjector := by
          rw [← spinLift_mul_isospinLift_comm]
      _ = ((spinLift tripletProjector * spinLift singletProjector) *
            isospinLift singletProjector) * isospinLift tripletProjector := by
          simp only [mul_assoc]
      _ = 0 := by
          rw [spinLift_mul, singlet_triplet_orthogonal.2, spinLift_zero, zero_mul, zero_mul]

theorem totalSpinIsospinExchange_sq :
    totalSpinIsospinExchange.comp totalSpinIsospinExchange = (1 : TwoNucleonOperator) := by
  dsimp [totalSpinIsospinExchange]
  change (spinLift spinSwap * isospinLift spinSwap) *
      (spinLift spinSwap * isospinLift spinSwap) = 1
  have hcomm : isospinLift spinSwap * spinLift spinSwap =
      spinLift spinSwap * isospinLift spinSwap :=
    (spinLift_comp_isospinLift_comm spinSwap spinSwap).symm
  rw [mul_assoc (spinLift spinSwap), ← mul_assoc (isospinLift spinSwap), hcomm, mul_assoc,
    ← mul_assoc]
  change (spinLift (spinSwap.comp spinSwap)) * (isospinLift (spinSwap.comp spinSwap)) = 1
  rw [spinSwap_sq, spinLift_one, isospinLift_one, mul_one]

/-- Exact spin-isospin exchange decomposition:
`P^σ P^τ = (P_{S=1,T=1} + P_{S=0,T=0}) - (P_{S=0,T=1} + P_{S=1,T=0})`,
so `(1 - P^σ P^τ) / 2` projects onto the `S`-wave antisymmetric pair channel. -/
theorem antisymSWaveProj_eq_half_sub_exchange :
    antisymSWaveProj =
      (1 / 2 : ℂ) • ((1 : TwoNucleonOperator) - totalSpinIsospinExchange) := by
  have hswap : totalSpinIsospinExchange =
      (projS0T0 + projS1T1) - (projS0T1 + projS1T0) := by
    dsimp [totalSpinIsospinExchange, projS0T0, projS1T1, projS0T1, projS1T0]
    rw [spinSwap_eq_triplet_sub_singlet, spinLift_sub, isospinLift_sub]
    change (spinLift tripletProjector - spinLift singletProjector) *
        (isospinLift tripletProjector - isospinLift singletProjector) =
      spinLift singletProjector * isospinLift singletProjector +
        spinLift tripletProjector * isospinLift tripletProjector -
      (spinLift singletProjector * isospinLift tripletProjector +
        spinLift tripletProjector * isospinLift singletProjector)
    rw [sub_mul, mul_sub, mul_sub]
    abel
  rw [hswap, ← proj_four_sector_sum]
  dsimp [antisymSWaveProj]
  module

theorem totalSpinIsospinExchange_on_antisymSWave :
    totalSpinIsospinExchange.comp antisymSWaveProj = -antisymSWaveProj := by
  have h1 : antisymSWaveProj + antisymSWaveProj =
      (1 : TwoNucleonOperator) - totalSpinIsospinExchange := by
    rw [antisymSWaveProj_eq_half_sub_exchange]
    module
  rw [antisymSWaveProj_eq_half_sub_exchange]
  change totalSpinIsospinExchange * ((1 / 2 : ℂ) • (1 - totalSpinIsospinExchange)) =
    -((1 / 2 : ℂ) • (1 - totalSpinIsospinExchange))
  rw [Algebra.mul_smul_comm, mul_sub, mul_one]
  change (1 / 2 : ℂ) • (totalSpinIsospinExchange -
      totalSpinIsospinExchange.comp totalSpinIsospinExchange) = _
  rw [totalSpinIsospinExchange_sq]
  module

/-- On the `S`-wave antisymmetric pair channel, `S² + T² = 2` universally,
expressing spin-singlet vs. isospin-singlet duality `(S, T) ∈ {(0, 1), (1, 0)}`. -/
theorem spin_add_isospin_on_antisymSWave :
    (spinLift spinSquared + isospinLift spinSquared).comp antisymSWaveProj =
      (2 : ℂ) • antisymSWaveProj := by
  rw [spinSquared_eq_two_triplet, spinLift_smul, isospinLift_smul]
  dsimp [antisymSWaveProj, projS0T1, projS1T0]
  have hs0 : spinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) = 0 := by
    rw [← mul_assoc]
    change spinLift (tripletProjector.comp singletProjector) * isospinLift tripletProjector = 0
    rw [singlet_triplet_orthogonal.2, spinLift_zero, zero_mul]
  have hs1 : spinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) =
      spinLift tripletProjector * isospinLift singletProjector := by
    rw [← mul_assoc]
    change spinLift (tripletProjector.comp tripletProjector) * isospinLift singletProjector = _
    rw [tripletProjector_idem]
  have ht0 : isospinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) =
      spinLift singletProjector * isospinLift tripletProjector := by
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc]
    change spinLift singletProjector * isospinLift (tripletProjector.comp tripletProjector) = _
    rw [tripletProjector_idem]
  have ht1 : isospinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) = 0 := by
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc]
    change spinLift tripletProjector * isospinLift (tripletProjector.comp singletProjector) = 0
    rw [singlet_triplet_orthogonal.2, isospinLift_zero, mul_zero]
  change ((2 : ℂ) • spinLift tripletProjector + (2 : ℂ) • isospinLift tripletProjector) *
      (spinLift singletProjector * isospinLift tripletProjector +
        spinLift tripletProjector * isospinLift singletProjector) =
    (2 : ℂ) • (spinLift singletProjector * isospinLift tripletProjector +
      spinLift tripletProjector * isospinLift singletProjector)
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, mul_add, mul_add]
  rw [hs0, hs1, ht0, ht1, zero_add, add_zero, ← smul_add, add_comm]

/-- Exact Casimir asymmetry separating the deuteron (`S=1, T=0`) condensate from the
isovector (`S=0, T=1`) condensate on the `S`-wave antisymmetric subspace:
`(S² - T²) P_asym = 2 (P_{S=1,T=0} - P_{S=0,T=1})`. -/
theorem spin_sub_isospin_on_antisymSWave :
    (spinLift spinSquared - isospinLift spinSquared).comp antisymSWaveProj =
      (2 : ℂ) • (projS1T0 - projS0T1) := by
  rw [spinSquared_eq_two_triplet, spinLift_smul, isospinLift_smul]
  dsimp [antisymSWaveProj, projS0T1, projS1T0]
  have hs0 : spinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) = 0 := by
    rw [← mul_assoc]
    change spinLift (tripletProjector.comp singletProjector) * isospinLift tripletProjector = 0
    rw [singlet_triplet_orthogonal.2, spinLift_zero, zero_mul]
  have hs1 : spinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) =
      spinLift tripletProjector * isospinLift singletProjector := by
    rw [← mul_assoc]
    change spinLift (tripletProjector.comp tripletProjector) * isospinLift singletProjector = _
    rw [tripletProjector_idem]
  have ht0 : isospinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) =
      spinLift singletProjector * isospinLift tripletProjector := by
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc]
    change spinLift singletProjector * isospinLift (tripletProjector.comp tripletProjector) = _
    rw [tripletProjector_idem]
  have ht1 : isospinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) = 0 := by
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc]
    change spinLift tripletProjector * isospinLift (tripletProjector.comp singletProjector) = 0
    rw [singlet_triplet_orthogonal.2, isospinLift_zero, mul_zero]
  change ((2 : ℂ) • spinLift tripletProjector - (2 : ℂ) • isospinLift tripletProjector) *
      (spinLift singletProjector * isospinLift tripletProjector +
        spinLift tripletProjector * isospinLift singletProjector) =
    (2 : ℂ) • (spinLift tripletProjector * isospinLift singletProjector -
      spinLift singletProjector * isospinLift tripletProjector)
  rw [sub_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, mul_add, mul_add]
  rw [hs0, hs1, ht0, ht1, zero_add, add_zero, ← smul_sub]

/-- Exact exchange asymmetry `(P^σ - P^τ) P_asym = 2 (P_{S=1,T=0} - P_{S=0,T=1})`. -/
theorem exchange_asymmetry_on_antisymSWave :
    (spinLift spinSwap - isospinLift spinSwap).comp antisymSWaveProj =
      (2 : ℂ) • (projS1T0 - projS0T1) := by
  have hsing : spinLift singletProjector - isospinLift singletProjector =
      -(spinLift tripletProjector - isospinLift tripletProjector) := by
    have hsp : singletProjector = 1 - tripletProjector := by
      dsimp [tripletProjector]; abel
    rw [hsp, spinLift_sub, isospinLift_sub, spinLift_one, isospinLift_one]
    abel
  have hswap : spinLift spinSwap - isospinLift spinSwap =
      spinLift spinSquared - isospinLift spinSquared := by
    rw [spinSquared_eq_two_triplet, spinLift_smul, isospinLift_smul,
      spinSwap_eq_triplet_sub_singlet, spinLift_sub, isospinLift_sub]
    calc
      spinLift tripletProjector - spinLift singletProjector -
          (isospinLift tripletProjector - isospinLift singletProjector)
        = (spinLift tripletProjector - isospinLift tripletProjector) -
            (spinLift singletProjector - isospinLift singletProjector) := by abel
      _ = (spinLift tripletProjector - isospinLift tripletProjector) -
            (-(spinLift tripletProjector - isospinLift tripletProjector)) := by rw [hsing]
      _ = (2 : ℂ) • spinLift tripletProjector - (2 : ℂ) • isospinLift tripletProjector := by
          module
  rw [hswap]
  exact spin_sub_isospin_on_antisymSWave

/-- Spectral competition theorem: the pairing Hamiltonian assigns energy `-g₁` to the
isovector spin-singlet `(S=0, T=1)` channel and `-g₀` to the isoscalar deuteron
`(S=1, T=0)` channel. -/
theorem pairingCompetitionHam_on_isovector_and_deuteron (g0 g1 : ℂ) :
    (pairingCompetitionHam g0 g1).comp projS0T1 = (-g1) • projS0T1 ∧
      (pairingCompetitionHam g0 g1).comp projS1T0 = (-g0) • projS1T0 := by
  dsimp [pairingCompetitionHam]
  constructor
  · change ((-g1) • projS0T1 + (-g0) • projS1T0) * projS0T1 = (-g1) • projS0T1
    rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
    change (-g1) • projS0T1.comp projS0T1 + (-g0) • projS1T0.comp projS0T1 = (-g1) • projS0T1
    rw [projS0T1_idem, projS0T1_projS1T0_orthogonal.2, smul_zero, add_zero]
  · change ((-g1) • projS0T1 + (-g0) • projS1T0) * projS1T0 = (-g0) • projS1T0
    rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
    change (-g1) • projS0T1.comp projS1T0 + (-g0) • projS1T0.comp projS1T0 = (-g0) • projS1T0
    rw [projS0T1_projS1T0_orthogonal.1, projS1T0_idem, smul_zero, zero_add]

/-- Both competing pairing channels commute with total spin `S²`, total isospin `T²`,
and the combined spin-isospin exchange `P^σ P^τ`. -/
theorem pairingCompetitionHam_commutes_casimirs (g0 g1 : ℂ) :
    (pairingCompetitionHam g0 g1).comp (spinLift spinSquared) =
        (spinLift spinSquared).comp (pairingCompetitionHam g0 g1) ∧
      (pairingCompetitionHam g0 g1).comp (isospinLift spinSquared) =
        (isospinLift spinSquared).comp (pairingCompetitionHam g0 g1) ∧
      (pairingCompetitionHam g0 g1).comp totalSpinIsospinExchange =
        totalSpinIsospinExchange.comp (pairingCompetitionHam g0 g1) := by
  have comm_spin_S0T1 : spinLift spinSquared * projS0T1 = projS0T1 * spinLift spinSquared := by
    rw [spinSquared_eq_two_triplet, spinLift_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    congr 1
    dsimp [projS0T1]
    change spinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) =
      (spinLift singletProjector * isospinLift tripletProjector) * spinLift tripletProjector
    rw [← mul_assoc, mul_assoc (spinLift singletProjector), ← spinLift_mul_isospinLift_comm,
      ← mul_assoc]
    change spinLift (tripletProjector.comp singletProjector) * isospinLift tripletProjector =
      spinLift (singletProjector.comp tripletProjector) * isospinLift tripletProjector
    rw [singlet_triplet_orthogonal.2, singlet_triplet_orthogonal.1]
  have comm_spin_S1T0 : spinLift spinSquared * projS1T0 = projS1T0 * spinLift spinSquared := by
    rw [spinSquared_eq_two_triplet, spinLift_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    congr 1
    dsimp [projS1T0]
    change spinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) =
      (spinLift tripletProjector * isospinLift singletProjector) * spinLift tripletProjector
    rw [mul_assoc (spinLift tripletProjector) (isospinLift singletProjector) (spinLift tripletProjector),
      ← spinLift_mul_isospinLift_comm, ← mul_assoc]
  have comm_iso_S0T1 : isospinLift spinSquared * projS0T1 = projS0T1 * isospinLift spinSquared := by
    rw [spinSquared_eq_two_triplet, isospinLift_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    congr 1
    dsimp [projS0T1]
    change isospinLift tripletProjector * (spinLift singletProjector * isospinLift tripletProjector) =
      (spinLift singletProjector * isospinLift tripletProjector) * isospinLift tripletProjector
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc]
  have comm_iso_S1T0 : isospinLift spinSquared * projS1T0 = projS1T0 * isospinLift spinSquared := by
    rw [spinSquared_eq_two_triplet, isospinLift_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    congr 1
    dsimp [projS1T0]
    change isospinLift tripletProjector * (spinLift tripletProjector * isospinLift singletProjector) =
      (spinLift tripletProjector * isospinLift singletProjector) * isospinLift tripletProjector
    rw [← mul_assoc, ← spinLift_mul_isospinLift_comm, mul_assoc, mul_assoc]
    change spinLift tripletProjector * isospinLift (tripletProjector.comp singletProjector) =
      spinLift tripletProjector * isospinLift (singletProjector.comp tripletProjector)
    rw [singlet_triplet_orthogonal.2, singlet_triplet_orthogonal.1]
  have comm_ex_S0T1 : totalSpinIsospinExchange * projS0T1 = projS0T1 * totalSpinIsospinExchange := by
    dsimp [totalSpinIsospinExchange, projS0T1]
    change (spinLift spinSwap * isospinLift spinSwap) *
        (spinLift singletProjector * isospinLift tripletProjector) =
      (spinLift singletProjector * isospinLift tripletProjector) *
        (spinLift spinSwap * isospinLift spinSwap)
    calc
      _ = (spinLift spinSwap * spinLift singletProjector) *
            (isospinLift spinSwap * isospinLift tripletProjector) := by
          rw [mul_assoc (spinLift spinSwap), ← mul_assoc (isospinLift spinSwap),
            ← spinLift_mul_isospinLift_comm, mul_assoc, ← mul_assoc]
      _ = (spinLift singletProjector * spinLift spinSwap) *
            (isospinLift tripletProjector * isospinLift spinSwap) := by
          change spinLift (spinSwap.comp singletProjector) * isospinLift (spinSwap.comp tripletProjector) =
            spinLift (singletProjector.comp spinSwap) * isospinLift (tripletProjector.comp spinSwap)
          rw [spinSwap_on_singlet, spinSwap_on_triplet]
          have h1 : singletProjector.comp spinSwap = -singletProjector := by
            rw [spinSwap_eq_triplet_sub_singlet]
            change singletProjector * (tripletProjector - singletProjector) = -singletProjector
            rw [mul_sub]
            change singletProjector.comp tripletProjector - singletProjector.comp singletProjector =
              -singletProjector
            rw [singlet_triplet_orthogonal.1, singletProjector_idem, zero_sub]
          have h2 : tripletProjector.comp spinSwap = tripletProjector := by
            rw [spinSwap_eq_triplet_sub_singlet]
            change tripletProjector * (tripletProjector - singletProjector) = tripletProjector
            rw [mul_sub]
            change tripletProjector.comp tripletProjector - tripletProjector.comp singletProjector =
              tripletProjector
            rw [tripletProjector_idem, singlet_triplet_orthogonal.2, sub_zero]
          rw [h1, h2]
      _ = _ := by
          rw [mul_assoc (spinLift singletProjector), ← mul_assoc (spinLift spinSwap),
            spinLift_mul_isospinLift_comm, mul_assoc, ← mul_assoc]
  have comm_ex_S1T0 : totalSpinIsospinExchange * projS1T0 = projS1T0 * totalSpinIsospinExchange := by
    dsimp [totalSpinIsospinExchange, projS1T0]
    change (spinLift spinSwap * isospinLift spinSwap) *
        (spinLift tripletProjector * isospinLift singletProjector) =
      (spinLift tripletProjector * isospinLift singletProjector) *
        (spinLift spinSwap * isospinLift spinSwap)
    calc
      _ = (spinLift spinSwap * spinLift tripletProjector) *
            (isospinLift spinSwap * isospinLift singletProjector) := by
          rw [mul_assoc (spinLift spinSwap), ← mul_assoc (isospinLift spinSwap),
            ← spinLift_mul_isospinLift_comm, mul_assoc, ← mul_assoc]
      _ = (spinLift tripletProjector * spinLift spinSwap) *
            (isospinLift singletProjector * isospinLift spinSwap) := by
          change spinLift (spinSwap.comp tripletProjector) * isospinLift (spinSwap.comp singletProjector) =
            spinLift (tripletProjector.comp spinSwap) * isospinLift (singletProjector.comp spinSwap)
          rw [spinSwap_on_triplet, spinSwap_on_singlet]
          have h1 : singletProjector.comp spinSwap = -singletProjector := by
            rw [spinSwap_eq_triplet_sub_singlet]
            change singletProjector * (tripletProjector - singletProjector) = -singletProjector
            rw [mul_sub]
            change singletProjector.comp tripletProjector - singletProjector.comp singletProjector =
              -singletProjector
            rw [singlet_triplet_orthogonal.1, singletProjector_idem, zero_sub]
          have h2 : tripletProjector.comp spinSwap = tripletProjector := by
            rw [spinSwap_eq_triplet_sub_singlet]
            change tripletProjector * (tripletProjector - singletProjector) = tripletProjector
            rw [mul_sub]
            change tripletProjector.comp tripletProjector - tripletProjector.comp singletProjector =
              tripletProjector
            rw [tripletProjector_idem, singlet_triplet_orthogonal.2, sub_zero]
          rw [h1, h2]
      _ = _ := by
          rw [mul_assoc (spinLift tripletProjector), ← mul_assoc (spinLift spinSwap),
            spinLift_mul_isospinLift_comm, mul_assoc, ← mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · change pairingCompetitionHam g0 g1 * spinLift spinSquared =
      spinLift spinSquared * pairingCompetitionHam g0 g1
    dsimp [pairingCompetitionHam]
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Algebra.mul_smul_comm, comm_spin_S0T1, comm_spin_S1T0]
  · change pairingCompetitionHam g0 g1 * isospinLift spinSquared =
      isospinLift spinSquared * pairingCompetitionHam g0 g1
    dsimp [pairingCompetitionHam]
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Algebra.mul_smul_comm, comm_iso_S0T1, comm_iso_S1T0]
  · change pairingCompetitionHam g0 g1 * totalSpinIsospinExchange =
      totalSpinIsospinExchange * pairingCompetitionHam g0 g1
    dsimp [pairingCompetitionHam]
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Algebra.mul_smul_comm, comm_ex_S0T1, comm_ex_S1T0]

end TwoNucleonSpinIsospin

end InfoGeometry.Physics.TwoStrandJonesCasimir

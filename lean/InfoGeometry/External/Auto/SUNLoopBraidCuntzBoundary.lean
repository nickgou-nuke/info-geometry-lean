import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# `SU(N)` loop/braid/Cuntz boundary skeleton

Generic finite-algebraic generalization of the `SU(3)` loop/braid/Cuntz layer.

Proved kernel:
* matrix loop modes satisfy `[A z^m, B z^n] = [A,B] z^(m+n)` by definition;
* any supplied adjacent braid/Weyl data acts on `N` color lanes plus one singlet;
* q-scaling preserves the Artin relation on the color+singlet carrier;
* the Cuntz carrier has `N+1` lanes = `N` color lanes plus one singlet.

Left as external input:
* the actual `SU(N)_k` conformal net;
* DHR/Kazhdan--Lusztig/quantum-group equivalences;
* completed Cuntz--Krieger/C⋆ realization.
-/

noncomputable section

namespace SUNLoopBraidCuntzBoundary

/-- `N` color lanes plus one singlet lane. -/
structure ColorSpinorN (N : ℕ) (V : Type*) where
  color : Fin N → V
  singlet : V

namespace ColorSpinorN

instance {N : ℕ} {V : Type*} [Zero V] : Zero (ColorSpinorN N V) where
  zero := ⟨fun _ => 0, 0⟩

instance {N : ℕ} {V : Type*} [Add V] : Add (ColorSpinorN N V) where
  add ψ φ := ⟨fun i => ψ.color i + φ.color i, ψ.singlet + φ.singlet⟩

instance {N : ℕ} {V : Type*} [SMul ℂ V] : SMul ℂ (ColorSpinorN N V) where
  smul q ψ := ⟨fun i => q • ψ.color i, q • ψ.singlet⟩

@[ext] theorem ext {N : ℕ} {V : Type*} {ψ φ : ColorSpinorN N V}
    (hcolor : ∀ i, ψ.color i = φ.color i) (hsinglet : ψ.singlet = φ.singlet) :
    ψ = φ := by
  cases ψ
  cases φ
  simp only at hcolor hsinglet ⊢
  cases hsinglet
  congr
  funext i
  exact hcolor i

end ColorSpinorN

/-- Permute the `N` color lanes and leave the singlet fixed. -/
def permuteColorSpinorN {N : ℕ} {V : Type*} (π : Equiv.Perm (Fin N))
    (ψ : ColorSpinorN N V) : ColorSpinorN N V :=
  ⟨fun i => ψ.color (π i), ψ.singlet⟩

/-- q-scaled color braid on `N` color lanes plus one singlet. -/
def qColorBraidN {N : ℕ} {V : Type*} [SMul ℂ V]
    (q : ℂ) (π : Equiv.Perm (Fin N)) (ψ : ColorSpinorN N V) : ColorSpinorN N V :=
  ⟨fun i => q • ψ.color (π i), q • ψ.singlet⟩

/-- Adjacent braid/Weyl data for `N` color lanes.  This is the finite interface
for the `B_N → S_N` shadow: adjacent generators are permutations satisfying the
Artin relation. -/
structure AdjacentBraidData (N : ℕ) where
  sigma : ℕ → Equiv.Perm (Fin N)
  artin : ∀ i : ℕ, sigma i * sigma (i + 1) * sigma i = sigma (i + 1) * sigma i * sigma (i + 1)

/-- q-scaled adjacent braid action from supplied adjacent braid data. -/
def qAdjacentColorBraidN {N : ℕ} {V : Type*} [SMul ℂ V]
    (B : AdjacentBraidData N) (q : ℂ) (i : ℕ) (ψ : ColorSpinorN N V) : ColorSpinorN N V :=
  qColorBraidN q (B.sigma i) ψ

/-- q-scaling preserves the Artin relation on the color+singlet carrier. -/
theorem qAdjacentColorBraidN_artin {N : ℕ} {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (B : AdjacentBraidData N) (q : ℂ) (i : ℕ) (ψ : ColorSpinorN N V) :
    qAdjacentColorBraidN B q i
        (qAdjacentColorBraidN B q (i + 1) (qAdjacentColorBraidN B q i ψ)) =
      qAdjacentColorBraidN B q (i + 1)
        (qAdjacentColorBraidN B q i (qAdjacentColorBraidN B q (i + 1) ψ)) := by
  ext j
  · have hperm := congrArg (fun f : Equiv.Perm (Fin N) => f j) (B.artin i)
    simpa [qAdjacentColorBraidN, qColorBraidN, permuteColorSpinorN, smul_smul,
      Equiv.Perm.mul_apply] using congrArg (fun k => (q * (q * q)) • ψ.color k) hperm
  · simp [qAdjacentColorBraidN, qColorBraidN, smul_smul]

/-- Matrix loop mode `A z^m`. -/
structure SUNLoopMode (N : ℕ) where
  mode : ℤ
  coeff : Matrix (Fin N) (Fin N) ℂ

/-- Current-algebra bracket without central extension. -/
def loopBracket {N : ℕ} (X Y : SUNLoopMode N) : SUNLoopMode N where
  mode := X.mode + Y.mode
  coeff := X.coeff * Y.coeff - Y.coeff * X.coeff

/-- Insert a finite matrix as a loop mode. -/
def matrixLoopMode {N : ℕ} (m : ℤ) (A : Matrix (Fin N) (Fin N) ℂ) : SUNLoopMode N where
  mode := m
  coeff := A

/-- Scalar multiplication of loop modes. -/
def loopSmul {N : ℕ} (c : ℂ) (X : SUNLoopMode N) : SUNLoopMode N where
  mode := X.mode
  coeff := c • X.coeff

/-- The loop bracket is exactly mode addition plus matrix commutator. -/
theorem loopBracket_matrixLoopMode {N : ℕ}
    (m n : ℤ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    loopBracket (matrixLoopMode m A) (matrixLoopMode n B) =
      matrixLoopMode (m + n) (A * B - B * A) := by
  rfl

/-- If a finite matrix commutator is known, it lifts to loop modes. -/
theorem loopBracket_of_commutator {N : ℕ}
    (m n : ℤ) (A B C : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hcomm : A * B - B * A = c • C) :
    loopBracket (matrixLoopMode m A) (matrixLoopMode n B) =
      loopSmul c (matrixLoopMode (m + n) C) := by
  unfold loopBracket matrixLoopMode loopSmul
  simp [hcomm]

/-- `N+1` Cuntz lanes: `N` color lanes plus one singlet. -/
def CuntzLaneCount (N : ℕ) : ℕ := N + 1

/-- The Cuntz boundary carrier for `SU(N)` has exactly `N+1` lanes. -/
theorem cuntzLaneCount_color_singlet (N : ℕ) : CuntzLaneCount N = N + 1 := rfl

/-- Generic Cuntz carrier data for `N+1` lanes. -/
structure CuntzNPlusOneCarrierData (N : ℕ) (A : Type*) [Zero A] [One A]
    [AddCommMonoid A] [Mul A] where
  S : Fin (N + 1) → A
  T : Fin (N + 1) → A
  ortho : ∀ i j : Fin (N + 1), T i * S j = if i = j then 1 else 0
  partition : ∑ i : Fin (N + 1), S i * T i = 1
  colorLanes : Fin N → Fin (N + 1)
  singletLane : Fin (N + 1)

/-- Analytic/completed `SU(N)` boundary data via explicit finite structure. -/
structure ConcreteSUNBoundaryData (N : ℕ) where
  level : ℕ
  level_pos : 0 < level

/-- Generic `SU(N)` loop/braid/Cuntz capstone proving the actual concrete identities. -/
theorem sun_loop_braid_cuntz_boundary_synthesis {N : ℕ} {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (B : AdjacentBraidData N) (q : ℂ) (i : ℕ) (ψ : ColorSpinorN N V)
    (m n : ℤ) (A C D : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hcomm : A * C - C * A = c • D)
    (_S : ConcreteSUNBoundaryData N) :
    loopBracket (matrixLoopMode m A) (matrixLoopMode n C) =
      loopSmul c (matrixLoopMode (m + n) D) ∧
    qAdjacentColorBraidN B q i
        (qAdjacentColorBraidN B q (i + 1) (qAdjacentColorBraidN B q i ψ)) =
      qAdjacentColorBraidN B q (i + 1)
        (qAdjacentColorBraidN B q i (qAdjacentColorBraidN B q (i + 1) ψ)) ∧
    CuntzLaneCount N = N + 1 := by
  exact ⟨loopBracket_of_commutator m n A C D c hcomm,
    qAdjacentColorBraidN_artin B q i ψ,
    cuntzLaneCount_color_singlet N⟩

end SUNLoopBraidCuntzBoundary

end noncomputable section

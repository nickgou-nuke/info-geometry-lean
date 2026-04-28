/-
InfoGeometry/Algebraic/SplitSuperGeometry.lean

Abstract parity / grade-involution layer for split Clifford geometry.

This file intentionally avoids an explicit exterior-algebra grade decomposition.
Parity is represented as an involutive algebra automorphism of the carrier.

No complex imports.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import InfoGeometry.Algebraic.SplitCliffordCarrier

noncomputable section

namespace InfoGeometry.Algebraic.SplitSuperGeometry

open InfoGeometry.Algebraic.SplitSignature

open scoped BigOperators

/--
An abstract parity involution on an algebra carrier.

Interpretation:
* `toAlgEquiv` is the parity or grade involution.
* `involutive` says parity squared is the identity.
* `evenPart` and `oddPart` are abstract eigenspaces/submodules.
* even elements have parity `+1`;
* odd elements have parity `-1`.

This avoids choosing an explicit exterior-grade decomposition.
-/
structure ParityInvolution
    (A : Type*) [Ring A] [Algebra ℝ A] where
  toAlgEquiv : A ≃ₐ[ℝ] A
  involutive : Function.Involutive toAlgEquiv
  evenPart : Submodule ℝ A
  oddPart : Submodule ℝ A
  parity_eq_on_even :
    ∀ {x : A}, x ∈ evenPart → toAlgEquiv x = x
  parity_eq_on_odd :
    ∀ {x : A}, x ∈ oddPart → toAlgEquiv x = -x

namespace ParityInvolution

variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

/-- The underlying linear parity operator. -/
def toLinearMap (P : ParityInvolution A) : Module.End ℝ A :=
  P.toAlgEquiv.toLinearMap

@[simp]
theorem parity_parity
    (P : ParityInvolution A) (x : A) :
    P.toAlgEquiv (P.toAlgEquiv x) = x :=
  P.involutive x

@[simp]
theorem parity_even
    (P : ParityInvolution A) {x : A}
    (hx : x ∈ P.evenPart) :
    P.toAlgEquiv x = x :=
  P.parity_eq_on_even hx

@[simp]
theorem parity_odd
    (P : ParityInvolution A) {x : A}
    (hx : x ∈ P.oddPart) :
    P.toAlgEquiv x = -x :=
  P.parity_eq_on_odd hx

/--
Supertrace induced by parity.

For an endomorphism `T`, this is

`str(T) = Tr(parity ∘ T)`.

No explicit even-minus-odd decomposition is needed at this layer.
-/
def supertrace
    (P : ParityInvolution A)
    (T : Module.End ℝ A) : ℝ :=
  LinearMap.trace ℝ A (P.toLinearMap.comp T)

@[simp]
theorem supertrace_zero
    (P : ParityInvolution A) :
    P.supertrace 0 = 0 := by
  simp [supertrace, toLinearMap]

/-- The superdimension is the supertrace of the identity endomorphism. -/
def superdimension
    (P : ParityInvolution A) : ℝ :=
  P.supertrace 1

/-- A linear map preserves parity if it commutes with the parity involution. -/
def ParityPreserving
    (P : ParityInvolution A) (T : Module.End ℝ A) : Prop :=
  P.toLinearMap.comp T = T.comp P.toLinearMap

end ParityInvolution

/-
Compatibility alias: the canonical parity involution on the split Clifford
carrier as an algebra automorphism.
-/
def cliffordParity (n : ℕ) : Cl_nn n ≃ₐ[ℝ] Cl_nn n :=
  CliffordAlgebra.involuteEquiv (Q := splitQuadraticForm n)

@[simp]
theorem cliffordParity_ι
    (n : ℕ) (v : SplitModule n) :
    cliffordParity n (CliffordAlgebra.ι (splitQuadraticForm n) v) =
      -(CliffordAlgebra.ι (splitQuadraticForm n) v) := by
  simpa [cliffordParity] using
    (CliffordAlgebra.involute_ι
      (Q := splitQuadraticForm n)
      v)

@[simp]
theorem cliffordParity_involutive
    (n : ℕ) :
    Function.Involutive (cliffordParity n) := by
  intro x
  simpa [cliffordParity] using
    (CliffordAlgebra.involute_involutive
      (Q := splitQuadraticForm n) x)

@[simp]
theorem cliffordParity_comp_self
    (n : ℕ) (x : Cl_nn n) :
    cliffordParity n (cliffordParity n x) = x :=
  cliffordParity_involutive n x

/--
The canonical parity involution on the split Clifford algebra.

This is exactly Mathlib's Clifford grade involution, wrapped in the abstract
`ParityInvolution` interface.
-/
def splitCliffordParityInvolution
    (n : ℕ) : ParityInvolution (Cl_nn n) where
  toAlgEquiv := CliffordAlgebra.involuteEquiv (Q := splitQuadraticForm n)
  involutive := by
    intro x
    simpa using
      (CliffordAlgebra.involute_involutive
        (Q := splitQuadraticForm n) x)
  evenPart := CliffordAlgebra.evenOdd (splitQuadraticForm n) 0
  oddPart := CliffordAlgebra.evenOdd (splitQuadraticForm n) 1
  parity_eq_on_even := by
    intro x hx
    simpa using
      (CliffordAlgebra.involute_eq_of_mem_even
        (Q := splitQuadraticForm n) hx)
  parity_eq_on_odd := by
    intro x hx
    simpa using
      (CliffordAlgebra.involute_eq_of_mem_odd
        (Q := splitQuadraticForm n) hx)

@[simp]
theorem splitCliffordParityInvolution_vector
    {n : ℕ} (v : SplitModule n) :
    (splitCliffordParityInvolution n).toAlgEquiv
        (CliffordAlgebra.ι (splitQuadraticForm n) v) =
      - CliffordAlgebra.ι (splitQuadraticForm n) v := by
  simpa [splitCliffordParityInvolution] using
    (CliffordAlgebra.involute_ι
      (Q := splitQuadraticForm n) v)

/--
Split supergeometry carrier.

Klein/Hestenes reading:
the Clifford carrier has a parity involution;
supertrace, Berezinian, and supervolume are derived from this involution,
not from coordinate-level alternating sums.
-/
structure SplitSuperGeometry (n : ℕ) where
  parity : ParityInvolution (Cl_nn n)

namespace SplitSuperGeometry

/-- Canonical split supergeometry from the Clifford grade involution. -/
def canonical (n : ℕ) : SplitSuperGeometry n where
  parity := splitCliffordParityInvolution n

/-- Supertrace of an endomorphism of the split Clifford carrier. -/
def supertrace
    {n : ℕ}
    (S : SplitSuperGeometry n)
    (T : Module.End ℝ (Cl_nn n)) : ℝ :=
  S.parity.supertrace T

/-- Superdimension of the split Clifford carrier. -/
def superdimension
    {n : ℕ}
    (S : SplitSuperGeometry n) : ℝ :=
  S.parity.superdimension

@[simp]
theorem canonical_parity
    (n : ℕ) :
    (canonical n).parity = splitCliffordParityInvolution n :=
  rfl

end SplitSuperGeometry

/-
Abstract Berezinian readout attached to a parity involution.

This is intentionally not implemented as an explicit determinant on even and
odd coordinate blocks. That refinement belongs in a later file once a concrete
splitting or basis has been supplied.
-/
structure SuperBerezinianReadout
    {A : Type*} [Ring A] [Algebra ℝ A]
    (P : ParityInvolution A) where

  /-- Berezinian/superdeterminant of a parity-preserving operator. -/
  ber : Module.End ℝ A → ℝ

  /-- The Berezinian of the identity is one. -/
  ber_one : ber 1 = 1

  /--
  Multiplicativity on parity-preserving operators.

  The order is retained for compatibility with noncommutative operator
  algebras, even though the target is commutative.
  -/
  ber_mul_of_parityPreserving :
    ∀ {S T : Module.End ℝ A},
      P.ParityPreserving S →
      P.ParityPreserving T →
      ber (S * T) = ber S * ber T


namespace SuperBerezinianReadout

variable
    {A : Type*} [Ring A] [Algebra ℝ A]
    {P : ParityInvolution A}

/--
Negative logarithmic Berezinian potential.

This is the algebraic super-volume analogue of `-log det`.
Positivity/nonvanishing hypotheses are not built into this definition; they
belong in analytic or cone-specific files.
-/
def negLogBer
    (B : SuperBerezinianReadout P)
    (T : Module.End ℝ A) : ℝ :=
  - Real.log (B.ber T)

@[simp]
theorem negLogBer_one
    (B : SuperBerezinianReadout P) :
    B.negLogBer 1 = - Real.log 1 := by
  simp [negLogBer, B.ber_one]

end SuperBerezinianReadout


/--
Split Clifford supergeometry package.

This packages the canonical parity structure on `Cl(n,n)`.
The determinant/Berezinian data is intentionally separate.
-/
structure SplitSuperCarrier (n : ℕ) where
  parity : ParityInvolution (Cl_nn n)

namespace SplitSuperCarrier

/-- The standard split Clifford super carrier using the Clifford grade involution. -/
def standard (n : ℕ) : SplitSuperCarrier n where
  parity := splitCliffordParityInvolution n

end SplitSuperCarrier

/--
A parity-preserving operator action.

This is the correct input for later Berezinian/determinant readouts:
operators must commute with the parity involution before an even/odd
supervolume character can be extracted.
-/
structure ParityPreservingOperatorAction
    (G A : Type*) [Group G] [Ring A] [Algebra ℝ A]
    (P : ParityInvolution A) where
  op : G →* Units (Module.End ℝ A)
  commute_parity :
    ∀ g : G,
      P.toLinearMap.comp ((op g : Units (Module.End ℝ A)) : Module.End ℝ A) =
        ((op g : Units (Module.End ℝ A)) : Module.End ℝ A).comp P.toLinearMap

namespace ParityPreservingOperatorAction

variable
    {G A : Type*} [Group G] [Ring A] [Algebra ℝ A]
    {P : ParityInvolution A}

/-- The underlying endomorphism associated to a group element. -/
def endomorphism
    (ρ : ParityPreservingOperatorAction G A P)
    (g : G) : Module.End ℝ A :=
  ((ρ.op g : Units (Module.End ℝ A)) : Module.End ℝ A)

theorem endomorphism_commute_parity
    (ρ : ParityPreservingOperatorAction G A P)
    (g : G) :
    P.toLinearMap.comp (ρ.endomorphism g) =
      (ρ.endomorphism g).comp P.toLinearMap :=
  ρ.commute_parity g

/-- Supertrace of a parity-preserving operator. -/
def supertraceOp
    (ρ : ParityPreservingOperatorAction G A P)
    (g : G) : ℝ :=
  P.supertrace (ρ.endomorphism g)

end ParityPreservingOperatorAction

/-
Compatibility aliases for the older supervolume vocabulary.
These keep the translated legacy files stable while the new involution-based
core is adopted.
-/
abbrev SplitCliffordEnd (n : ℕ) : Type :=
  Module.End ℝ (Cl_nn n)

def parityOp (n : ℕ) : SplitCliffordEnd n :=
  (cliffordParity n).toLinearMap

@[simp]
theorem parityOp_ι
    (n : ℕ) (v : SplitModule n) :
    parityOp n (CliffordAlgebra.ι (splitQuadraticForm n) v) =
      -(CliffordAlgebra.ι (splitQuadraticForm n) v) := by
  simp [parityOp]

@[simp]
theorem parityOp_comp_self
    (n : ℕ) (x : Cl_nn n) :
    parityOp n (parityOp n x) = x := by
  simp [parityOp, cliffordParity_comp_self]

def cliffordSupertrace (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  (splitCliffordParityInvolution n).supertrace

def superBerezinian (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  fun T => Real.exp (cliffordSupertrace n T)

def superVolumeAnomaly (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  superBerezinian n

def superEffectiveAction (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  fun T => - Real.log (superVolumeAnomaly n T)

@[simp]
theorem superVolumeAnomaly_eq_superBerezinian
    (n : ℕ) :
    superVolumeAnomaly n = superBerezinian n :=
  rfl

@[simp]
theorem superEffectiveAction_eq_neg_log_superBerezinian
    (n : ℕ) (T : SplitCliffordEnd n) :
    superEffectiveAction n T = - Real.log (superBerezinian n T) :=
  rfl

@[simp]
theorem superBerezinian_pos
    (n : ℕ) (T : SplitCliffordEnd n) :
    0 < superBerezinian n T := by
  dsimp [superBerezinian]
  positivity

end InfoGeometry.Algebraic.SplitSuperGeometry

namespace InfoGeometry.Algebraic.SplitSignature

abbrev SplitCliffordEnd (n : ℕ) : Type :=
  InfoGeometry.Algebraic.SplitSuperGeometry.SplitCliffordEnd n

def cliffordParity (n : ℕ) : Cl_nn n ≃ₐ[ℝ] Cl_nn n :=
  InfoGeometry.Algebraic.SplitSuperGeometry.cliffordParity n

def parityOp (n : ℕ) : SplitCliffordEnd n :=
  InfoGeometry.Algebraic.SplitSuperGeometry.parityOp n

def cliffordSupertrace (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  InfoGeometry.Algebraic.SplitSuperGeometry.cliffordSupertrace n

def superBerezinian (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  InfoGeometry.Algebraic.SplitSuperGeometry.superBerezinian n

def superVolumeAnomaly (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  InfoGeometry.Algebraic.SplitSuperGeometry.superVolumeAnomaly n

def superEffectiveAction (n : ℕ) :
    SplitCliffordEnd n → ℝ :=
  InfoGeometry.Algebraic.SplitSuperGeometry.superEffectiveAction n

end InfoGeometry.Algebraic.SplitSignature

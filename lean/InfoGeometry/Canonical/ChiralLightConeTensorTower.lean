import InfoGeometry.Canonical.Cl11PolarizedBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordHeadSuperBracket
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ChiralLightConeTensorTower

Canonical import surface for the chiral light-cone tensor tower.

This file intentionally does not duplicate bridge theorems already owned by the
repo.  The theorem-bearing surfaces are:

* `Cl11PolarizedBasis`
  - local `u⁺/u⁻` polarized channels;
  - nilpotence `u⁺u⁺=0`, `u⁻u⁻=0`;
  - mixed products landing in the grade-zero lane.

* `ChiralOperatorConeClosure`
  - enrollment of `u⁺/u⁻` in the Drazin/chiral cone under `eps = Γ_S`;
  - `[𝔭_S,𝔭_S] ⊆ 𝔨_S` compact/even closure.

* `SplitCliffordTensorBridge`
  - recursive split `Cl(n+1,n+1) ≃ Cl(1,1) ⊗ Cl(n,n)` tensor step;
  - head null-mode factorization.

* `SplitCliffordHeadSuperBracket`
  - tensor-head null-mode CAR laws;
  - head `J/K/ε` super-bracket identities.

This module only names the finite symbolic word and infinite symbolic boundary
carriers used to discuss the tensor tower.  It does not assert:

* a basis theorem for a concrete `Cl(n,n)` implementation;
* matrix-unit laws such as `u⁺u⁻=P⁺`;
* a Cantor homeomorphism;
* an infinite tensor-product theorem.
-/

namespace InfoGeometry.Canonical.ChiralLightConeTensorTower

/--
Four-symbol local split `Cl(1,1)` chiral alphabet.

This is a symbolic alphabet only.  The algebraic laws of the realized local
operators remain owned by `Cl11PolarizedBasis` and related owner modules.
-/
@[rep_depth krein]
inductive ChiralSymbol where
  | one
  | uPlus
  | uMinus
  | epsilon
  deriving DecidableEq, Repr

namespace ChiralSymbol

/-- The local symbol is causal/off-diagonal exactly when it is `u⁺` or `u⁻`. -/
@[rep_depth krein]
def IsCausal (s : ChiralSymbol) : Prop :=
  s = uPlus ∨ s = uMinus

@[simp, rep_depth krein]
theorem uPlus_isCausal : IsCausal uPlus := Or.inl rfl

@[simp, rep_depth krein]
theorem uMinus_isCausal : IsCausal uMinus := Or.inr rfl

@[simp, rep_depth krein]
theorem one_not_isCausal : ¬ IsCausal one := by
  intro h
  cases h with
  | inl h1 => cases h1
  | inr h1 => cases h1

@[simp, rep_depth krein]
theorem epsilon_not_isCausal : ¬ IsCausal epsilon := by
  intro h
  cases h with
  | inl h1 => cases h1
  | inr h1 => cases h1

end ChiralSymbol

/-- Finite four-symbol chiral word of length `n`. -/
@[rep_depth krein]
abbrev ChiralWord (n : ℕ) := Fin n → ChiralSymbol

/-- Binary chiral arrow alphabet: `u⁺` and `u⁻`. -/
@[rep_depth krein]
inductive ChiralArrow where
  | plus
  | minus
  deriving DecidableEq, Repr

namespace ChiralArrow

/-- Flip the light-cone arrow orientation. -/
@[rep_depth krein]
def flip : ChiralArrow → ChiralArrow
  | plus => minus
  | minus => plus

@[simp, rep_depth krein]
theorem flip_flip (a : ChiralArrow) : flip (flip a) = a := by
  cases a <;> rfl

/-- Read a binary arrow as a four-symbol local chiral alphabet element. -/
@[rep_depth krein]
def toSymbol : ChiralArrow → ChiralSymbol
  | plus => ChiralSymbol.uPlus
  | minus => ChiralSymbol.uMinus

@[simp, rep_depth krein]
theorem toSymbol_flip_plus : toSymbol (flip plus) = ChiralSymbol.uMinus := rfl

@[simp, rep_depth krein]
theorem toSymbol_flip_minus : toSymbol (flip minus) = ChiralSymbol.uPlus := rfl

end ChiralArrow

/-- Causal arrow is the binary `u⁺/u⁻` subalphabet. -/
@[rep_depth krein]
abbrev CausalArrow := ChiralArrow

/-- Finite binary causal word of length `n`. -/
@[rep_depth krein]
abbrev CausalWord (n : ℕ) := Fin n → CausalArrow

/-- Infinite symbolic chiral boundary.  This is the Cantor-type boundary carrier. -/
@[rep_depth krein]
abbrev ChiralBoundary := ℕ → CausalArrow

/-- Embed a finite binary causal word into the four-symbol chiral word carrier. -/
@[rep_depth krein]
def CausalWord.toChiralWord {n : ℕ} (w : CausalWord n) : ChiralWord n :=
  fun k => ChiralArrow.toSymbol (w k)

/-- Embed a finite chiral word into the infinite boundary by a default tail. -/
@[rep_depth krein]
def CausalWord.toBoundary {n : ℕ} (w : CausalWord n) (tail : CausalArrow) :
    ChiralBoundary :=
  fun k =>
    if h : k < n then w ⟨k, h⟩ else tail

@[simp, rep_depth krein]
theorem CausalWord.toBoundary_of_lt {n : ℕ}
    (w : CausalWord n) (tail : CausalArrow) {k : ℕ} (hk : k < n) :
    CausalWord.toBoundary w tail k = w ⟨k, hk⟩ := by
  simp [CausalWord.toBoundary, hk]

@[simp, rep_depth krein]
theorem CausalWord.toChiralWord_apply {n : ℕ} (w : CausalWord n) (k : Fin n) :
    CausalWord.toChiralWord w k = ChiralArrow.toSymbol (w k) := rfl

end InfoGeometry.Canonical.ChiralLightConeTensorTower

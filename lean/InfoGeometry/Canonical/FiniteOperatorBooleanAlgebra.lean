/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.Canonical.KreinProjectorLattice
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# Finite operator Boolean algebra

The Boolean algebra of a finite family of commuting split-Clifford sectors.
`KreinSector` is the one-generator Boolean algebra of the `Cl(1,1)` projectors;
a function `Fin P → KreinSector` is the `P`-generator Boolean algebra, with
operations taken pointwise. Its embedding into `Fin P → CliffordAlgebra splitQ11`
realizes meet as multiplication, complement as `1 -`, and every generator as an
idempotent.

For a certified prime register `P : PrimeRegister`, each subset `S : Finset ℕ`
also determines a sector family `primeSubsetSector P S` (placing `p₊` on `p ∈ S`
and `p₋` on `p ∈ P.primes \ S`) with pointwise projector realization
`primeSubsetOps P S`, yielding idempotence, Boolean complementation on `P.primes \ S`,
and mutual orthogonality whenever a prime `p ∈ P.primes` distinguishes `S` and `T`.
-/

namespace InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra

open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.Canonical.KreinProjectorLattice
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- The `P`-generator sector algebra. -/
abbrev Sector (P : ℕ) := Fin P → KreinSector

/-- The pointwise operator carrier. -/
abbrev Ops (P : ℕ) := Fin P → Alg

/-- The operator realization of a sector family. -/
noncomputable def toOps {P : ℕ} (s : Sector P) : Ops P :=
  fun i => KreinSector.toAlg (s i)

@[simp] theorem toOps_apply {P : ℕ} (s : Sector P) (i : Fin P) :
    toOps s i = KreinSector.toAlg (s i) := rfl

theorem toOps_idempotent {P : ℕ} (s : Sector P) (i : Fin P) :
    IsIdempotentElem (toOps s i) :=
  KreinSector.toAlg_idempotent (s i)

theorem toOps_inf_eq_mul {P : ℕ} (s t : Sector P) :
    toOps (s ⊓ t) = toOps s * toOps t := by
  funext i
  exact KreinSector.toAlg_inf_eq_mul (s i) (t i)

theorem toOps_sup_eq_add_sub_mul {P : ℕ} (s t : Sector P) :
    toOps (s ⊔ t) = toOps s + toOps t - toOps s * toOps t := by
  funext i
  exact KreinSector.toAlg_sup_eq_add_sub_mul (s i) (t i)

theorem toOps_compl_eq_one_sub {P : ℕ} (s : Sector P) :
    toOps sᶜ = 1 - toOps s := by
  funext i
  exact KreinSector.toAlg_compl_eq_one_sub (s i)

/-- Permutation action on a sector family: the coordinate permutation of a Boolean product. -/
instance instPermAction (P : ℕ) : MulAction (Equiv.Perm (Fin P)) (Sector P) where
  smul σ s := fun i => s (σ.symm i)
  one_smul s := by
    funext i
    change s ((1 : Equiv.Perm (Fin P)).symm i) = s i
    rfl
  mul_smul σ τ s := by
    funext i
    change s ((σ * τ).symm i) = s (τ.symm (σ.symm i))
    rfl

theorem perm_meet (P : ℕ) (σ : Equiv.Perm (Fin P)) (s t : Sector P) :
    σ • (s ⊓ t) = (σ • s) ⊓ (σ • t) :=
  rfl

theorem perm_sup (P : ℕ) (σ : Equiv.Perm (Fin P)) (s t : Sector P) :
    σ • (s ⊔ t) = (σ • s) ⊔ (σ • t) :=
  rfl

theorem perm_compl (P : ℕ) (σ : Equiv.Perm (Fin P)) (s : Sector P) :
    σ • sᶜ = (σ • s)ᶜ :=
  rfl

/-- Coordinatewise complement (XOR) action. It is an involution and preserves
complement, but it is order-reversing: it is not a Boolean automorphism. -/
def flip {P : ℕ} (ε : Fin P → Bool) (s : Sector P) : Sector P :=
  fun i => if ε i then (s i)ᶜ else s i

theorem flip_zero {P : ℕ} (s : Sector P) : flip (0 : Fin P → Bool) s = s := by
  funext i
  simp [flip]

theorem flip_self {P : ℕ} (ε : Fin P → Bool) (s : Sector P) : flip ε (flip ε s) = s := by
  funext i
  by_cases h : ε i = true <;> simp [flip, h]

/-! ## Hyperoctahedral Boolean automorphism group `(ℤ/2)^P ⋊ S_P` -/

/-- Order-preserving atom swap on `KreinSector` (`plus ↔ minus`, fixing `bot` and `top`). -/
def signFlip : KreinSector → KreinSector
  | .bot   => .bot
  | .minus => .plus
  | .plus  => .minus
  | .top   => .top

@[simp] theorem signFlip_involutive (a : KreinSector) :
    signFlip (signFlip a) = a := by
  cases a <;> rfl

@[simp] theorem signFlip_bot : signFlip (⊥ : KreinSector) = ⊥ := rfl
@[simp] theorem signFlip_top : signFlip (⊤ : KreinSector) = ⊤ := rfl

theorem signFlip_meet (a b : KreinSector) :
    signFlip (a ⊓ b) = signFlip a ⊓ signFlip b := by
  cases a <;> cases b <;> rfl

theorem signFlip_sup (a b : KreinSector) :
    signFlip (a ⊔ b) = signFlip a ⊔ signFlip b := by
  cases a <;> cases b <;> rfl

theorem signFlip_compl (a : KreinSector) :
    signFlip aᶜ = (signFlip a)ᶜ := by
  cases a <;> rfl

/-- The elementary abelian 2-group `(ℤ/2)^P` written multiplicatively. -/
abbrev FlipGroup (P : ℕ) := Fin P → Multiplicative (ZMod 2)

/-- Single-bit action of `Multiplicative (ZMod 2)` on `KreinSector`. -/
def applyFlipBit (b : Multiplicative (ZMod 2)) (a : KreinSector) : KreinSector :=
  if Multiplicative.toAdd b = (1 : ZMod 2) then signFlip a else a

@[simp] theorem applyFlipBit_one (a : KreinSector) :
    applyFlipBit 1 a = a := by
  simp [applyFlipBit]

theorem applyFlipBit_mul (b₁ b₂ : Multiplicative (ZMod 2)) (a : KreinSector) :
    applyFlipBit (b₁ * b₂) a = applyFlipBit b₁ (applyFlipBit b₂ a) := by
  unfold applyFlipBit
  rw [toAdd_mul]
  generalize Multiplicative.toAdd b₁ = x₁
  generalize Multiplicative.toAdd b₂ = x₂
  fin_cases x₁ <;> fin_cases x₂ <;> cases a <;> decide

theorem applyFlipBit_meet (b : Multiplicative (ZMod 2)) (a₁ a₂ : KreinSector) :
    applyFlipBit b (a₁ ⊓ a₂) = applyFlipBit b a₁ ⊓ applyFlipBit b a₂ := by
  unfold applyFlipBit
  split_ifs
  · exact signFlip_meet a₁ a₂
  · rfl

theorem applyFlipBit_sup (b : Multiplicative (ZMod 2)) (a₁ a₂ : KreinSector) :
    applyFlipBit b (a₁ ⊔ a₂) = applyFlipBit b a₁ ⊔ applyFlipBit b a₂ := by
  unfold applyFlipBit
  split_ifs
  · exact signFlip_sup a₁ a₂
  · rfl

theorem applyFlipBit_compl (b : Multiplicative (ZMod 2)) (a : KreinSector) :
    applyFlipBit b aᶜ = (applyFlipBit b a)ᶜ := by
  unfold applyFlipBit
  split_ifs
  · exact signFlip_compl a
  · rfl

@[simp] theorem applyFlipBit_bot (b : Multiplicative (ZMod 2)) :
    applyFlipBit b (⊥ : KreinSector) = ⊥ := by
  unfold applyFlipBit
  split_ifs <;> rfl

@[simp] theorem applyFlipBit_top (b : Multiplicative (ZMod 2)) :
    applyFlipBit b (⊤ : KreinSector) = ⊤ := by
  unfold applyFlipBit
  split_ifs <;> rfl

/-- Coordinatewise order-preserving sign-flip action of `FlipGroup P` on `Sector P`. -/
def signFlipSector {P : ℕ} (ε : FlipGroup P) (s : Sector P) : Sector P :=
  fun i => applyFlipBit (ε i) (s i)

@[simp] theorem signFlipSector_one {P : ℕ} (s : Sector P) :
    signFlipSector (1 : FlipGroup P) s = s := by
  funext i
  exact applyFlipBit_one (s i)

theorem signFlipSector_mul {P : ℕ} (ε δ : FlipGroup P) (s : Sector P) :
    signFlipSector (ε * δ) s = signFlipSector ε (signFlipSector δ s) := by
  funext i
  exact applyFlipBit_mul (ε i) (δ i) (s i)

theorem signFlipSector_meet {P : ℕ} (ε : FlipGroup P) (s t : Sector P) :
    signFlipSector ε (s ⊓ t) = signFlipSector ε s ⊓ signFlipSector ε t := by
  funext i
  exact applyFlipBit_meet (ε i) (s i) (t i)

theorem signFlipSector_sup {P : ℕ} (ε : FlipGroup P) (s t : Sector P) :
    signFlipSector ε (s ⊔ t) = signFlipSector ε s ⊔ signFlipSector ε t := by
  funext i
  exact applyFlipBit_sup (ε i) (s i) (t i)

theorem signFlipSector_compl {P : ℕ} (ε : FlipGroup P) (s : Sector P) :
    signFlipSector ε sᶜ = (signFlipSector ε s)ᶜ := by
  funext i
  exact applyFlipBit_compl (ε i) (s i)

/-- Coordinate permutation automorphism of `FlipGroup P`. -/
def flipPermAut (P : ℕ) (σ : Equiv.Perm (Fin P)) : MulAut (FlipGroup P) where
  toFun ε i := ε (σ.symm i)
  invFun ε i := ε (σ i)
  left_inv ε := by funext i; simp
  right_inv ε := by funext i; simp
  map_mul' ε δ := by funext i; rfl

/-- Action homomorphism `S_P →* Aut((ℤ/2)^P)` defining the hyperoctahedral group. -/
def flipPermHom (P : ℕ) : Equiv.Perm (Fin P) →* MulAut (FlipGroup P) where
  toFun := flipPermAut P
  map_one' := by
    ext ε i
    rfl
  map_mul' σ τ := by
    ext ε i
    rfl

/-- The hyperoctahedral group `B_P = (ℤ/2)^P ⋊ S_P` acting on `Sector P`. -/
abbrev SignedPerm (P : ℕ) := SemidirectProduct (FlipGroup P) (Equiv.Perm (Fin P)) (flipPermHom P)

/-- Full `MulAction` of the hyperoctahedral group `SignedPerm P` on `Sector P`. -/
instance instSignedPermAction (P : ℕ) : MulAction (SignedPerm P) (Sector P) where
  smul g s := signFlipSector g.left (g.right • s)
  one_smul s := by
    change signFlipSector (1 : FlipGroup P) ((1 : Equiv.Perm (Fin P)) • s) = s
    rw [one_smul, signFlipSector_one]
  mul_smul g h s := by
    funext i
    change applyFlipBit ((g.left * flipPermAut P g.right h.left) i)
        (s ((g.right * h.right).symm i)) =
      applyFlipBit (g.left i) (applyFlipBit (h.left (g.right.symm i))
        (s (h.right.symm (g.right.symm i))))
    exact applyFlipBit_mul (g.left i) (h.left (g.right.symm i))
      (s (h.right.symm (g.right.symm i)))

theorem signedPerm_meet (P : ℕ) (g : SignedPerm P) (s t : Sector P) :
    g • (s ⊓ t) = (g • s) ⊓ (g • t) :=
  signFlipSector_meet g.left (g.right • s) (g.right • t)

theorem signedPerm_sup (P : ℕ) (g : SignedPerm P) (s t : Sector P) :
    g • (s ⊔ t) = (g • s) ⊔ (g • t) :=
  signFlipSector_sup g.left (g.right • s) (g.right • t)

theorem signedPerm_compl (P : ℕ) (g : SignedPerm P) (s : Sector P) :
    g • sᶜ = (g • s)ᶜ :=
  signFlipSector_compl g.left (g.right • s)

theorem signedPerm_bot (P : ℕ) (g : SignedPerm P) :
    g • (⊥ : Sector P) = ⊥ := by
  funext i
  exact applyFlipBit_bot (g.left i)

theorem signedPerm_top (P : ℕ) (g : SignedPerm P) :
    g • (⊤ : Sector P) = ⊤ := by
  funext i
  exact applyFlipBit_top (g.left i)

/-! ## Prime-register Boolean sector assignment -/

/-- Prime-register subset assignment mapping `p ∈ P.primes` to `p₊` if `p ∈ S`
and `p₋` otherwise. -/
def primeSubsetSector (P : PrimeRegister) (S : Finset ℕ) :
    {p // p ∈ P.primes} → KreinSector :=
  fun p => if p.val ∈ S then KreinSector.plus else KreinSector.minus

/-- Pointwise `Cl(1,1)` projector realization of `primeSubsetSector P S`. -/
noncomputable def primeSubsetOps (P : PrimeRegister) (S : Finset ℕ) :
    {p // p ∈ P.primes} → Alg :=
  fun p => KreinSector.toAlg (primeSubsetSector P S p)

/-- Every coordinate operator of `primeSubsetOps P S` is an idempotent in `Cl(1,1)`. -/
theorem primeSubsetOps_idempotent (P : PrimeRegister) (S : Finset ℕ)
    (p : {p // p ∈ P.primes}) :
    IsIdempotentElem (primeSubsetOps P S p) :=
  KreinSector.toAlg_idempotent (primeSubsetSector P S p)

/-- Taking the complement `P.primes \ S` replaces each mode's `Cl(1,1)` projector `p`
with `1 - p`. -/
theorem primeSubsetOps_compl (P : PrimeRegister) (S : Finset ℕ)
    (p : {p // p ∈ P.primes}) :
    primeSubsetOps P (P.primes \ S) p = 1 - primeSubsetOps P S p := by
  dsimp [primeSubsetOps, primeSubsetSector]
  by_cases hp : p.val ∈ S
  · have hpCompl : p.val ∉ P.primes \ S := fun h => (Finset.mem_sdiff.mp h).2 hp
    simp only [hpCompl, hp, ↓reduceIte]
    exact KreinSector.toAlg_compl_eq_one_sub KreinSector.plus
  · have hpCompl : p.val ∈ P.primes \ S := Finset.mem_sdiff.mpr ⟨p.property, hp⟩
    simp only [hpCompl, hp, ↓reduceIte]
    exact KreinSector.toAlg_compl_eq_one_sub KreinSector.minus

/-- If a prime `p ∈ P.primes` distinguishes subsets `S` and `T` (`p ∈ S ∧ p ∉ T` or
`p ∉ S ∧ p ∈ T`), then their coordinate `Cl(1,1)` projectors at `p` multiply to `0`. -/
theorem primeSubsetOps_mul_eq_zero_of_mem_symmDiff
    (P : PrimeRegister) {S T : Finset ℕ} {p : ℕ} (hp : p ∈ P.primes)
    (hdiff : (p ∈ S ∧ p ∉ T) ∨ (p ∉ S ∧ p ∈ T)) :
    primeSubsetOps P S ⟨p, hp⟩ * primeSubsetOps P T ⟨p, hp⟩ = 0 := by
  dsimp [primeSubsetOps, primeSubsetSector]
  rcases hdiff with ⟨hpS, hpT⟩ | ⟨hpS, hpT⟩
  · simp only [hpS, hpT, ↓reduceIte]
    exact KreinSector.toAlg_plus_mul_minus
  · simp only [hpS, hpT, ↓reduceIte]
    exact KreinSector.toAlg_minus_mul_plus

end InfoGeometry.Canonical.FiniteOperatorBooleanAlgebra

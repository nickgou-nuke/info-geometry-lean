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

/-! ## The sector carrier as two Boolean bits per site -/

/-- The four-element projector algebra records occupancy of its two distinct
atoms, `minus` and `plus`.  Thus one site is a two-bit Boolean cube. -/
def kreinSectorBitEquiv : KreinSector ≃ Bool × Bool where
  toFun
    | .bot => (false, false)
    | .minus => (true, false)
    | .plus => (false, true)
    | .top => (true, true)
  invFun
    | (false, false) => .bot
    | (true, false) => .minus
    | (false, true) => .plus
    | (true, true) => .top
  left_inv a := by cases a <;> rfl
  right_inv b := by
    rcases b with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂ <;> rfl

/-- Pointwise bit representation of a finite family of Krein sectors. -/
def sectorBitEquiv (P : ℕ) : Sector P ≃ (Fin P → Bool × Bool) where
  toFun s i := kreinSectorBitEquiv (s i)
  invFun b i := kreinSectorBitEquiv.symm (b i)
  left_inv s := by
    funext i
    exact kreinSectorBitEquiv.left_inv (s i)
  right_inv b := by
    funext i
    exact kreinSectorBitEquiv.right_inv (b i)

/-- The sitewise bit representation preserves meet, coordinatewise. -/
theorem kreinSectorBitEquiv_inf (a b : KreinSector) :
    kreinSectorBitEquiv (a ⊓ b) = kreinSectorBitEquiv a ⊓ kreinSectorBitEquiv b := by
  cases a <;> cases b <;> rfl

/-- The sitewise bit representation preserves join, coordinatewise. -/
theorem kreinSectorBitEquiv_sup (a b : KreinSector) :
    kreinSectorBitEquiv (a ⊔ b) = kreinSectorBitEquiv a ⊔ kreinSectorBitEquiv b := by
  cases a <;> cases b <;> rfl

/-- Complement in the sector algebra negates each of its two atom bits. -/
theorem kreinSectorBitEquiv_compl (a : KreinSector) :
    kreinSectorBitEquiv aᶜ =
      (!((kreinSectorBitEquiv a).1), !((kreinSectorBitEquiv a).2)) := by
  cases a <;> rfl

/-- The finite-sector equivalence preserves the pointwise Boolean meet. -/
theorem sectorBitEquiv_inf (P : ℕ) (s t : Sector P) :
    sectorBitEquiv P (s ⊓ t) = sectorBitEquiv P s ⊓ sectorBitEquiv P t := by
  funext i
  exact kreinSectorBitEquiv_inf (s i) (t i)

/-- The finite-sector equivalence preserves the pointwise Boolean join. -/
theorem sectorBitEquiv_sup (P : ℕ) (s t : Sector P) :
    sectorBitEquiv P (s ⊔ t) = sectorBitEquiv P s ⊔ sectorBitEquiv P t := by
  funext i
  exact kreinSectorBitEquiv_sup (s i) (t i)

/-- The finite-sector equivalence carries complement to bitwise Boolean negation. -/
theorem sectorBitEquiv_compl (P : ℕ) (s : Sector P) :
    sectorBitEquiv P sᶜ = fun i =>
      (!((sectorBitEquiv P s i).1), !((sectorBitEquiv P s i).2)) := by
  funext i
  exact kreinSectorBitEquiv_compl (s i)

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

/-- Under the two-bit encoding, the nontrivial group element swaps the two
atomic projector bits. -/
theorem kreinSectorBitEquiv_applyFlipBit
    (b : Multiplicative (ZMod 2)) (a : KreinSector) :
    kreinSectorBitEquiv (applyFlipBit b a) =
      if Multiplicative.toAdd b = (1 : ZMod 2) then
        Prod.swap (kreinSectorBitEquiv a)
      else kreinSectorBitEquiv a := by
  unfold applyFlipBit
  split_ifs with h
  · cases a <;> rfl
  · rfl

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

/-- The signed-permutation action, transported to bits, permutes sites and
then swaps the two atom bits at each site selected by the flip component. -/
theorem signedPerm_sectorBitEquiv_apply
    (P : ℕ) (g : SignedPerm P) (s : Sector P) (i : Fin P) :
    sectorBitEquiv P (g • s) i =
      if Multiplicative.toAdd (g.left i) = (1 : ZMod 2) then
        Prod.swap (sectorBitEquiv P s (g.right.symm i))
      else sectorBitEquiv P s (g.right.symm i) := by
  change kreinSectorBitEquiv
      (applyFlipBit (g.left i) (s (g.right.symm i))) = _
  exact kreinSectorBitEquiv_applyFlipBit (g.left i) (s (g.right.symm i))

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

private theorem applyFlipBit_minus_ne_bot (b : Multiplicative (ZMod 2)) :
    applyFlipBit b KreinSector.minus ≠ KreinSector.bot := by
  unfold applyFlipBit
  split_ifs <;> simp [signFlip]

/-- An element of the signed-permutation group fixing every sector family is
the identity, provided the register has at least one site. -/
theorem signedPerm_eq_one_of_forall_smul_eq_self
    (P : ℕ) [Nonempty (Fin P)] (g : SignedPerm P)
    (hfix : ∀ s : Sector P, g • s = s) :
    g = 1 := by
  classical
  have hright_apply : ∀ i : Fin P, g.right i = i := by
    intro i
    let s : Sector P := fun j => if j = i then KreinSector.minus else KreinSector.bot
    have hs := congrFun (hfix s) (g.right i)
    change applyFlipBit (g.left (g.right i))
        (if g.right.symm (g.right i) = i then KreinSector.minus else KreinSector.bot) =
      if g.right i = i then KreinSector.minus else KreinSector.bot at hs
    simp only [Equiv.symm_apply_apply, ↓reduceIte] at hs
    have hne := applyFlipBit_minus_ne_bot (g.left (g.right i))
    by_contra hne'
    simp [hne'] at hs
    exact hne hs
  have hright : g.right = 1 := by
    ext i
    exact congrArg Fin.val (hright_apply i)
  have hleft_apply : ∀ i : Fin P, g.left i = 1 := by
    intro i
    have hs := congrFun (hfix (fun _ : Fin P => KreinSector.minus)) i
    change applyFlipBit (g.left i) KreinSector.minus = KreinSector.minus at hs
    have hzero : Multiplicative.toAdd (g.left i) = 0 := by
      by_cases hone : Multiplicative.toAdd (g.left i) = 1
      · simp [applyFlipBit, signFlip, hone] at hs
      · have hvalne : (Multiplicative.toAdd (g.left i)).val ≠ 1 := by
          intro hv
          apply hone
          apply ZMod.val_injective 2
          simpa only [ZMod.val_one] using hv
        have hval : (Multiplicative.toAdd (g.left i)).val = 0 := by
          have hlt := ZMod.val_lt (Multiplicative.toAdd (g.left i))
          omega
        apply ZMod.val_injective 2
        simpa only [ZMod.val_zero] using hval
    apply Multiplicative.ext
    simpa using hzero
  apply SemidirectProduct.ext
  · ext i
    exact hleft_apply i
  · exact hright

/-- For a nonempty finite register the hyperoctahedral action on sector
families is faithful. -/
instance instSignedPermFaithfulSMul (P : ℕ) :
    FaithfulSMul (SignedPerm P) (Sector P) := by
  rw [faithfulSMul_iff]
  intro g hfix
  by_cases hP : 0 < P
  · let hnonempty : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
    exact @signedPerm_eq_one_of_forall_smul_eq_self P hnonempty g hfix
  · have hP0 : P = 0 := Nat.eq_zero_of_not_pos hP
    subst P
    apply SemidirectProduct.ext
    · funext i
      exact Fin.elim0 i
    · ext i
      exact Fin.elim0 i

/-! ## Prime-register Boolean sector assignment -/

/-- Prime-register subset assignment mapping `p ∈ P.primes` to `p₊` if `p ∈ S`
and `p₋` otherwise. -/
def primeSubsetSector (P : PrimeRegister) (S : Finset ℕ) :
    {p // p ∈ P.primes} → KreinSector :=
  fun p => if p.val ∈ S then KreinSector.plus else KreinSector.minus

/-- Prime-register sector families using only the two atomic projectors.  This
is the precise sector slice corresponding to one Boolean occupancy bit per
prime; the unrestricted `Sector P` has four choices at every site. -/
abbrev PrimeAtomSector (P : PrimeRegister) :=
  {s : {p // p ∈ P.primes} → KreinSector //
    ∀ p, s p = KreinSector.minus ∨ s p = KreinSector.plus}

/-- Boolean occupancy words are equivalent to prime-register sector families
restricted to the atomic projectors `minus` and `plus`. -/
def primeBitAtomSectorEquiv (P : PrimeRegister) :
    PrimeBitState P ≃ PrimeAtomSector P where
  toFun ψ := ⟨fun p => if ψ p then KreinSector.plus else KreinSector.minus, by
    intro p
    by_cases h : ψ p <;> simp [h]⟩
  invFun s := fun p => decide (s.1 p = KreinSector.plus)
  left_inv ψ := by
    funext p
    cases h : ψ p <;> simp [h]
  right_inv s := by
    apply Subtype.ext
    funext p
    rcases s.2 p with hminus | hplus
    · simp [hminus]
    · simp [hplus]

/-- Pointwise form of the state-to-sector encoding. -/
@[simp] theorem primeBitAtomSectorEquiv_apply
    (P : PrimeRegister) (ψ : PrimeBitState P) (p : {p // p ∈ P.primes}) :
    (primeBitAtomSectorEquiv P ψ).1 p =
      if ψ p then KreinSector.plus else KreinSector.minus := rfl

/-- Negating an occupancy bit complements its atomic Krein projector. -/
theorem primeBitAtomSectorEquiv_not_apply
    (P : PrimeRegister) (ψ : PrimeBitState P) (p : {p // p ∈ P.primes}) :
    (primeBitAtomSectorEquiv P (fun q => !(ψ q))).1 p =
      ((primeBitAtomSectorEquiv P ψ).1 p)ᶜ := by
  cases h : ψ p <;> simp [h, primeBitAtomSectorEquiv] <;> rfl

/-- The existing subset-to-projector assignment is the state encoding of its
characteristic occupancy word. -/
theorem primeSubsetSector_eq_stateEncoding
    (P : PrimeRegister) (S : Finset ℕ) :
    primeSubsetSector P S =
      (primeBitAtomSectorEquiv P (fun p => decide (p.val ∈ S))).1 := by
  funext p
  simp [primeSubsetSector, primeBitAtomSectorEquiv]

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

import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Meta.Architecture

/-!
# Krein Projector Lattice

The local order-theoretic structure on the `{0, p₋, p₊, 1}` projector system
of split `Cl(1,1)`.

The four elements `{⊥, ε₋, ε₊, ⊤}` form a Boolean algebra (diamond lattice)
with:

  - `⊥ = 0`, `⊤ = 1`
  - `ε₋ ∧ ε₊ = 0`, `ε₋ ∨ ε₊ = 1`
  - complementation: `ε₋ᶜ = ε₊`, `ε₊ᶜ = ε₋`

This is the local Krein-site lattice before Cantor refinement.

The Krein involution is recovered as `K = ε₊ - ε₋` at the algebraic level.
-/

namespace InfoGeometry.Canonical.KreinProjectorLattice

/-! ## 1. The four-element Krein sector type -/

/-- The four Krein sectors at a single split-quaternion site. -/
inductive KreinSector : Type
  | bot   : KreinSector  -- trivial sector (0)
  | minus : KreinSector  -- negative chirality (p₋)
  | plus  : KreinSector  -- positive chirality (p₊)
  | top   : KreinSector  -- full sector (1)
  deriving DecidableEq, Repr

namespace KreinSector

/-! ## 2. Partial order -/

/-- The partial order on Krein sectors: `bot ≤ minus, plus ≤ top`. -/
instance : LE KreinSector where
  le a b := a = bot ∨ b = top ∨ a = b

instance : LT KreinSector where
  lt a b := a ≤ b ∧ ¬(b ≤ a)

instance : DecidableRel (· ≤ · : KreinSector → KreinSector → Prop) :=
  fun a b => inferInstanceAs (Decidable (a = bot ∨ b = top ∨ a = b))

instance : Preorder KreinSector where
  le_refl a := by cases a <;> trivial
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance : PartialOrder KreinSector where
  le_antisymm a b hab hba := by cases a <;> cases b <;> simp_all [LE.le]

/-! ## 3. Lattice structure -/

/-- Meet (infimum) of two Krein sectors. -/
def meet : KreinSector → KreinSector → KreinSector
  | bot, _       => bot
  | _, bot       => bot
  | top, b       => b
  | a, top       => a
  | minus, minus => minus
  | plus, plus   => plus
  | minus, plus  => bot
  | plus, minus  => bot

/-- Join (supremum) of two Krein sectors. -/
def join : KreinSector → KreinSector → KreinSector
  | top, _       => top
  | _, top       => top
  | bot, b       => b
  | a, bot       => a
  | minus, minus => minus
  | plus, plus   => plus
  | minus, plus  => top
  | plus, minus  => top

instance : Min KreinSector where min := meet
instance : Max KreinSector where max := join

private theorem inf_le_left (a b : KreinSector) : a ⊓ b ≤ a := by
  cases a <;> cases b <;> simp [Min.min, meet, LE.le]

private theorem inf_le_right (a b : KreinSector) : a ⊓ b ≤ b := by
  cases a <;> cases b <;> simp [Min.min, meet, LE.le]

private theorem le_inf (a b c : KreinSector) (hab : a ≤ b) (hac : a ≤ c) : a ≤ b ⊓ c := by
  cases a <;> cases b <;> cases c <;> simp_all [Min.min, meet, LE.le]

private theorem le_sup_left (a b : KreinSector) : a ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [Max.max, join, LE.le]

private theorem le_sup_right (a b : KreinSector) : b ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [Max.max, join, LE.le]

private theorem sup_le (a b c : KreinSector) (hac : a ≤ c) (hbc : b ≤ c) : a ⊔ b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [Max.max, join, LE.le]

instance : Lattice KreinSector where
  sup := join
  inf := meet
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := sup_le

/-! ## 4. Bounded lattice -/

instance : Bot KreinSector where bot := KreinSector.bot
instance : Top KreinSector where top := KreinSector.top

instance : OrderBot KreinSector where
  bot_le a := by cases a <;> decide

instance : OrderTop KreinSector where
  le_top a := by cases a <;> decide

instance : BoundedOrder KreinSector where

/-! ## 5. Distributive lattice -/

private theorem le_sup_inf (a b c : KreinSector) :
    (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c := by
  cases a <;> cases b <;> cases c <;>
    simp [Max.max, Min.min, join, meet, LE.le]

instance : DistribLattice KreinSector where
  le_sup_inf := le_sup_inf

/-! ## 6. Complementation and Boolean algebra -/

/-- Complement of a Krein sector. -/
def compl : KreinSector → KreinSector
  | bot   => top
  | minus => plus
  | plus  => minus
  | top   => bot

instance : Compl KreinSector where compl := compl

/-- Set difference on Krein sectors. -/
def sdiff (a b : KreinSector) : KreinSector := a ⊓ KreinSector.compl b

instance : SDiff KreinSector where sdiff := sdiff

/-- Heyting implication on Krein sectors. -/
def himp (a b : KreinSector) : KreinSector := b ⊔ KreinSector.compl a

instance : HImp KreinSector where himp := himp

private theorem inf_compl_le_bot (a : KreinSector) : a ⊓ aᶜ ≤ ⊥ := by
  cases a <;> decide

private theorem top_le_sup_compl (a : KreinSector) : ⊤ ≤ a ⊔ aᶜ := by
  cases a <;> decide

private theorem sdiff_eq (a b : KreinSector) : a \ b = a ⊓ bᶜ := by
  rfl

private theorem himp_eq (a b : KreinSector) : a ⇨ b = b ⊔ aᶜ := by
  rfl

instance : BooleanAlgebra KreinSector where
  compl := compl
  inf_compl_le_bot := inf_compl_le_bot
  top_le_sup_compl := top_le_sup_compl
  le_top a := by cases a <;> decide
  bot_le a := by cases a <;> decide
  sdiff_eq := sdiff_eq
  himp_eq := himp_eq

/-! ## 7. Finiteness and completeness -/

instance : Fintype KreinSector where
  elems := {bot, minus, plus, top}
  complete a := by cases a <;> simp

/-- The Krein sector lattice is complete (automatic from finiteness). -/
noncomputable instance : CompleteLattice KreinSector :=
  Fintype.toCompleteLattice KreinSector

/-! ## 8. Connection to Cl(1,1) projectors -/

open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors

/-- Representation map from Krein sectors to Cl(1,1) algebra elements. -/
noncomputable def toAlg : KreinSector → Alg
  | bot   => 0
  | minus => epsMinusProjector
  | plus  => epsPlusProjector
  | top   => 1

/-- The representation map preserves `⊥`. -/
@[simp] theorem toAlg_bot : toAlg bot = 0 := rfl

/-- The representation map preserves `⊤`. -/
@[simp] theorem toAlg_top : toAlg top = 1 := rfl

@[simp] theorem toAlg_minus : toAlg minus = epsMinusProjector := rfl

@[simp] theorem toAlg_plus : toAlg plus = epsPlusProjector := rfl

/-- Every local Krein lattice sector maps to an actual idempotent algebra element. -/
theorem toAlg_idempotent (a : KreinSector) :
    IsIdempotentElem (toAlg a) := by
  cases a
  · change IsIdempotentElem (0 : Alg)
    simp [IsIdempotentElem]
  · change IsIdempotentElem epsMinusProjector
    exact epsMinusProjector_idempotent
  · change IsIdempotentElem epsPlusProjector
    exact epsPlusProjector_idempotent
  · change IsIdempotentElem (1 : Alg)
    simp [IsIdempotentElem]

/-- The two projectors sum to the identity. -/
theorem toAlg_minus_add_plus :
    toAlg minus + toAlg plus = toAlg top := by
  show epsMinusProjector + epsPlusProjector = 1
  exact epsMinusProjector_add_epsPlusProjector

/-- The meet of the two nontrivial sectors maps to zero. -/
theorem toAlg_minus_mul_plus :
    toAlg minus * toAlg plus = toAlg bot := by
  show epsMinusProjector * epsPlusProjector = 0
  exact epsMinusProjector_mul_epsPlusProjector

/-- The opposite ordered product of the two primitive sectors is also zero. -/
theorem toAlg_plus_mul_minus :
    toAlg plus * toAlg minus = toAlg bot := by
  show epsPlusProjector * epsMinusProjector = 0
  exact epsPlusProjector_mul_epsMinusProjector

@[simp] theorem plus_inf_minus :
    plus ⊓ minus = bot :=
  rfl

@[simp] theorem minus_inf_plus :
    minus ⊓ plus = bot :=
  rfl

@[simp] theorem plus_sup_minus :
    plus ⊔ minus = top :=
  rfl

@[simp] theorem minus_sup_plus :
    minus ⊔ plus = top :=
  rfl

/-- Meet in the local Krein sector lattice is represented by projector multiplication. -/
theorem toAlg_inf_eq_mul (a b : KreinSector) :
    toAlg (a ⊓ b) = toAlg a * toAlg b := by
  cases a <;> cases b <;>
    simp only [toAlg, Min.min, meet, zero_mul, mul_zero, one_mul, mul_one]
  all_goals
    try rw [epsMinusProjector_idempotent]
    try rw [epsPlusProjector_idempotent]
    try rw [epsMinusProjector_mul_epsPlusProjector]
    try rw [epsPlusProjector_mul_epsMinusProjector]

/-- Join in the local Krein sector lattice is represented by `p + q - p*q`. -/
theorem toAlg_sup_eq_add_sub_mul (a b : KreinSector) :
    toAlg (a ⊔ b) = toAlg a + toAlg b - toAlg a * toAlg b := by
  have hsum_pm : epsPlusProjector + epsMinusProjector = 1 := by
    rw [add_comm, epsMinusProjector_add_epsPlusProjector]
  cases a <;> cases b <;>
    simp only [toAlg, Max.max, join, zero_add, add_zero, sub_zero, sub_self,
      one_mul, mul_one, zero_mul, mul_zero]
  all_goals
    try simp only [epsMinusProjector_idempotent, epsPlusProjector_idempotent,
      epsMinusProjector_mul_epsPlusProjector, epsPlusProjector_mul_epsMinusProjector,
      epsMinusProjector_add_epsPlusProjector, hsum_pm, sub_zero]
    try abel

/-- Boolean complement in the local Krein sector lattice is represented by `1 - p`. -/
theorem toAlg_compl_eq_one_sub (a : KreinSector) :
    toAlg aᶜ = 1 - toAlg a := by
  have hminus : epsPlusProjector = 1 - epsMinusProjector := by
    rw [← epsMinusProjector_add_epsPlusProjector]
    abel
  have hplus : epsMinusProjector = 1 - epsPlusProjector := by
    rw [← epsMinusProjector_add_epsPlusProjector]
    abel
  cases a
  · change (1 : Alg) = 1 - 0
    simp
  · change epsPlusProjector = 1 - epsMinusProjector
    exact hminus
  · change epsMinusProjector = 1 - epsPlusProjector
    exact hplus
  · change (0 : Alg) = 1 - 1
    simp

/-- The Krein involution recovered from the lattice. -/
noncomputable def kreinInvolution : Alg :=
  toAlg plus - toAlg minus

/-- The Krein involution is `ε₊ - ε₋`. -/
theorem kreinInvolution_eq :
    kreinInvolution = epsPlusProjector - epsMinusProjector := rfl

/-- The positive-minus-negative projector difference is the split `ε` pseudoscalar. -/
theorem epsPlusProjector_sub_epsMinusProjector_eq_epsGen :
    epsPlusProjector - epsMinusProjector = epsGen := by
  rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
  simp [sub_eq_add_neg, smul_add]
  module

/-- The lattice-recovered Krein involution is the split `ε` pseudoscalar. -/
theorem kreinInvolution_eq_epsGen :
    kreinInvolution = epsGen := by
  rw [kreinInvolution_eq, epsPlusProjector_sub_epsMinusProjector_eq_epsGen]

/-- The Krein involution squares to the identity.

This is the order-theoretic expression of `K² = 1`. -/
theorem kreinInvolution_sq :
    kreinInvolution * kreinInvolution = 1 := by
  show (epsPlusProjector - epsMinusProjector) * (epsPlusProjector - epsMinusProjector) = 1
  have h1 := epsPlusProjector_idempotent
  have h2 := epsMinusProjector_idempotent
  have h3 := epsPlusProjector_mul_epsMinusProjector
  have h4 := epsMinusProjector_mul_epsPlusProjector
  have h5 := epsMinusProjector_add_epsPlusProjector
  calc (epsPlusProjector - epsMinusProjector) * (epsPlusProjector - epsMinusProjector)
      = epsPlusProjector * epsPlusProjector
        - epsPlusProjector * epsMinusProjector
        - epsMinusProjector * epsPlusProjector
        + epsMinusProjector * epsMinusProjector := by
          simp only [sub_mul, mul_sub]; abel
    _ = epsPlusProjector - 0 - 0 + epsMinusProjector := by rw [h1, h3, h4, h2]
    _ = epsPlusProjector + epsMinusProjector := by simp
    _ = epsMinusProjector + epsPlusProjector := by abel
    _ = 1 := h5

end KreinSector

end InfoGeometry.Canonical.KreinProjectorLattice

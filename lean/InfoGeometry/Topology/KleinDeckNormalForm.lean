import InfoGeometry.Topology.KleinQuotientDeckInvariants

/-! Finite, theorem-safe affine shadow of the Klein glide.  The full deck-group
normal form remains a separate integration frontier because the current
repository has several incompatible historical carriers. -/
namespace InfoGeometry.Topology.KleinDeckNormalForm

open InfoGeometry.Topology.KleinQuotientDeckInvariants

abbrev Plane := PlanePoint
abbrev Deck := KleinDeckGroup

instance : Mul Deck := ⟨KleinDeckGroup.mul⟩
instance : One Deck := ⟨KleinDeckGroup.one⟩
instance : Inv Deck := ⟨KleinDeckGroup.inv⟩

def a : Deck := KleinDeckGroup.a
def b : Deck := KleinDeckGroup.b

def deckAct (g : Deck) (p : Plane) : Plane := deckAction g p

def abelianReadout (g : Deck) : ℤ × ZMod 2 :=
  (g.n, (g.m : ZMod 2))

private theorem signZ_cast_zmod_two (n : ℤ) :
    (signZ n : ZMod 2) = 1 := by
  simp [signZ]

theorem abelianReadout_mul (g h : Deck) :
    abelianReadout (g * h) = abelianReadout g + abelianReadout h := by
  rcases g with ⟨gm, gn⟩
  rcases h with ⟨hm, hn⟩
  change (gn + hn, ((gm + signZ gn * hm : ℤ) : ZMod 2)) =
    (gn + hn, ((gm : ZMod 2) + (hm : ZMod 2)))
  congr 1
  rw [Int.cast_add]
  rw [show ((signZ gn * hm : ℤ) : ZMod 2) = (hm : ZMod 2) by
    rw [Int.cast_mul, signZ_cast_zmod_two]
    simp]

@[simp] theorem abelianReadout_a : abelianReadout a = (0, 1) := by
  change (0, ((1 : ℤ) : ZMod 2)) = (0, 1)
  rfl

@[simp] theorem abelianReadout_b : abelianReadout b = (1, 0) := by
  change (1, ((0 : ℤ) : ZMod 2)) = (1, 0)
  rfl

theorem abelianReadout_surjective : Function.Surjective abelianReadout := by
  rintro ⟨n, p⟩
  fin_cases p
  · exact ⟨⟨0, n⟩, by simp [abelianReadout]⟩
  · exact ⟨⟨1, n⟩, by simp [abelianReadout]⟩

theorem horizontal_class_order_two : (2 : ℕ) • abelianReadout a = 0 := by
  rw [abelianReadout_a]
  change (2 : ℕ) • ((0 : ℤ), (1 : ZMod 2)) = (0, 0)
  decide

theorem klein_conjugation_relation : b * a * b⁻¹ = a⁻¹ := by
  change (⟨-1, 0⟩ : KleinDeckGroup) = ⟨-1, 0⟩
  rfl

theorem deckAct_eq_self_iff (g : Deck) (p : Plane) :
    deckAct g p = p ↔ g = 1 := by
  constructor
  · exact action_free g p
  · intro h
    cases h
    exact deckAction_one p

noncomputable def glide (p : Plane) : Plane := (p.1 + (1 / 2 : ℝ), -p.2)

def horizontalTranslation (p : Plane) : Plane := (p.1 + 1, p.2)

@[simp] theorem glide_twice (p : Plane) : glide (glide p) = horizontalTranslation p := by
  rcases p with ⟨x, y⟩
  simp only [glide, horizontalTranslation, Prod.fst, Prod.snd, neg_neg]
  congr 1
  ring

@[simp] theorem glide_orientation_shadow (p : Plane) :
    (glide p).1 = p.1 + (1 / 2 : ℝ) ∧ (glide p).2 = -p.2 := by
  simp [glide]

end InfoGeometry.Topology.KleinDeckNormalForm

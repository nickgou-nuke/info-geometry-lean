import Mathlib

/-!
# Klein-bottle deck normal form

The repository already owns several glide relations and a finite orbit
quotient.  This file supplies the missing normal-form group

`Γ = ℤ ⋊_{(-1)} ℤ`

and its explicit free affine action

`(m,n) · (x,y) = ((-1)^n x + m, y+n)`.

It also constructs the canonical abelian readout `Γ → ℤ × ZMod 2` and the
orientation character.  The file does not identify the affine orbit quotient
with a smooth Klein-bottle manifold or compute singular homology; those require
covering-space and manifold infrastructure beyond the algebra proved here.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinDeckNormalForm

/-- Integer sign `(-1)^n`, represented through Mathlib's integer unit power. -/
def paritySign (n : ℤ) : ℤ :=
  (n.negOnePow : ℤ)

@[simp] theorem paritySign_zero : paritySign 0 = 1 := rfl

@[simp] theorem paritySign_one : paritySign 1 = -1 := rfl

@[simp] theorem paritySign_neg (n : ℤ) :
    paritySign (-n) = paritySign n := by
  simp [paritySign]

theorem paritySign_add (m n : ℤ) :
    paritySign (m + n) = paritySign m * paritySign n := by
  simpa [paritySign] using
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.negOnePow_add m n)

@[simp] theorem paritySign_sq (n : ℤ) :
    paritySign n * paritySign n = 1 := by
  by_cases hn : Even n
  · rw [paritySign, Int.negOnePow_even n hn]
    norm_num
  · have hn' : Odd n := Int.not_even_iff_odd.mp hn
    rw [paritySign, Int.negOnePow_odd n hn']
    norm_num

/-- Normal-form element `a^m b^n`. -/
@[ext]
structure Deck where
  horizontal : ℤ
  vertical : ℤ
  deriving DecidableEq, Repr

instance : Mul Deck where
  mul g h :=
    ⟨g.horizontal + paritySign g.vertical * h.horizontal,
      g.vertical + h.vertical⟩

instance : One Deck where
  one := ⟨0, 0⟩

instance : Inv Deck where
  inv g :=
    ⟨-(paritySign g.vertical * g.horizontal), -g.vertical⟩

@[simp] theorem mul_horizontal (g h : Deck) :
    (g * h).horizontal =
      g.horizontal + paritySign g.vertical * h.horizontal := rfl

@[simp] theorem mul_vertical (g h : Deck) :
    (g * h).vertical = g.vertical + h.vertical := rfl

@[simp] theorem one_horizontal : (1 : Deck).horizontal = 0 := rfl
@[simp] theorem one_vertical : (1 : Deck).vertical = 0 := rfl

@[simp] theorem inv_horizontal (g : Deck) :
    g⁻¹.horizontal = -(paritySign g.vertical * g.horizontal) := rfl

@[simp] theorem inv_vertical (g : Deck) :
    g⁻¹.vertical = -g.vertical := rfl

/-- The normal forms carry the Klein semidirect-product group law. -/
instance : Group Deck where
  mul_assoc g h k := by
    ext
    · simp [paritySign_add]
      ring
    · simp
  one_mul g := by
    ext <;> simp
  mul_one g := by
    ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp [paritySign_neg]
      ring
    · simp

/-- Universal-cover affine plane. -/
abbrev Plane := ℝ × ℝ

/-- Affine action of a normal-form deck element. -/
def deckAct (g : Deck) (p : Plane) : Plane :=
  (((paritySign g.vertical : ℤ) : ℝ) * p.1 + (g.horizontal : ℝ),
    p.2 + (g.vertical : ℝ))

@[simp] theorem deckAct_one (p : Plane) :
    deckAct 1 p = p := by
  rcases p with ⟨x, y⟩
  simp [deckAct]

/-- Multiplication is exactly composition of the affine transformations. -/
theorem deckAct_mul (g h : Deck) (p : Plane) :
    deckAct (g * h) p = deckAct g (deckAct h p) := by
  rcases p with ⟨x, y⟩
  ext <;> simp [deckAct, paritySign_add] <;> ring

/-- The identity is the only deck element fixing a point. -/
theorem deckAct_eq_self_iff (g : Deck) (p : Plane) :
    deckAct g p = p ↔ g = 1 := by
  constructor
  · intro h
    have hy := congrArg Prod.snd h
    have hvr : (g.vertical : ℝ) = 0 := by
      simpa [deckAct] using sub_eq_zero.mp (sub_eq_zero.mpr hy)
    have hv : g.vertical = 0 := by
      exact_mod_cast hvr
    have hx := congrArg Prod.fst h
    have hhr : (g.horizontal : ℝ) = 0 := by
      simpa [deckAct, hv] using sub_eq_zero.mp (sub_eq_zero.mpr hx)
    have hh : g.horizontal = 0 := by
      exact_mod_cast hhr
    ext <;> simp [hh, hv]
  · rintro rfl
    exact deckAct_one p

/-- Equivalent freeness formulation. -/
theorem deckAct_free {g : Deck} (hg : g ≠ 1) (p : Plane) :
    deckAct g p ≠ p := by
  intro h
  exact hg ((deckAct_eq_self_iff g p).mp h)

/-- Horizontal translation generator. -/
def a : Deck := ⟨1, 0⟩

/-- Orientation-reversing glide generator. -/
def b : Deck := ⟨0, 1⟩

@[simp] theorem deckAct_a (x y : ℝ) :
    deckAct a (x, y) = (x + 1, y) := by
  simp [deckAct, a]

@[simp] theorem deckAct_b (x y : ℝ) :
    deckAct b (x, y) = (-x, y + 1) := by
  simp [deckAct, b]

/-- Klein-bottle presentation relation `b a = a⁻¹ b`. -/
theorem klein_relation : b * a = a⁻¹ * b := by
  ext <;> norm_num [a, b, paritySign]

/-- Conjugation presentation `b a b⁻¹ = a⁻¹`. -/
theorem klein_conjugation_relation : b * a * b⁻¹ = a⁻¹ := by
  calc
    b * a * b⁻¹ = (a⁻¹ * b) * b⁻¹ := by rw [klein_relation]
    _ = a⁻¹ := by group

/-- Orientation character: parity of the glide exponent. -/
def orientationCharacter : Deck →* ℤˣ where
  toFun g := g.vertical.negOnePow
  map_one' := rfl
  map_mul' g h := by
    simpa using Int.negOnePow_add g.vertical h.vertical

@[simp] theorem orientationCharacter_a :
    orientationCharacter a = 1 := rfl

@[simp] theorem orientationCharacter_b :
    orientationCharacter b = -1 := rfl

/-- Linear part of the affine action. -/
def linearPart (g : Deck) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((paritySign g.vertical : ℤ) : ℝ), 0;
      0, 1]

@[simp] theorem det_linearPart (g : Deck) :
    Matrix.det (linearPart g) = (paritySign g.vertical : ℝ) := by
  rw [Matrix.det_fin_two]
  simp [linearPart]

@[simp] theorem det_linearPart_a :
    Matrix.det (linearPart a) = 1 := by
  simp

@[simp] theorem det_linearPart_b :
    Matrix.det (linearPart b) = -1 := by
  simp

/-- The sign `(-1)^n` becomes trivial modulo two. -/
@[simp] theorem paritySign_cast_zmod_two (n : ℤ) :
    (paritySign n : ZMod 2) = 1 := by
  by_cases hn : Even n
  · rw [paritySign, Int.negOnePow_even n hn]
    norm_num
  · have hn' : Odd n := Int.not_even_iff_odd.mp hn
    rw [paritySign, Int.negOnePow_odd n hn']
    norm_num

/-- Canonical additive coordinate of the abelianization:
vertical winding remains integral and horizontal translation is reduced mod 2. -/
def abelianReadout (g : Deck) : ℤ × ZMod 2 :=
  (g.vertical, (g.horizontal : ZMod 2))

@[simp] theorem abelianReadout_one :
    abelianReadout 1 = 0 := by
  ext <;> simp [abelianReadout]

/-- The readout turns the semidirect product into ordinary addition. -/
theorem abelianReadout_mul (g h : Deck) :
    abelianReadout (g * h) = abelianReadout g + abelianReadout h := by
  ext
  · simp [abelianReadout]
  · simp [abelianReadout]

@[simp] theorem abelianReadout_a :
    abelianReadout a = (0, 1) := by
  ext <;> norm_num [abelianReadout, a]

@[simp] theorem abelianReadout_b :
    abelianReadout b = (1, 0) := by
  ext <;> norm_num [abelianReadout, b]

/-- Every pair in `ℤ × ZMod 2` has a deck normal-form representative. -/
theorem abelianReadout_surjective : Function.Surjective abelianReadout := by
  rintro ⟨n, r⟩
  refine ⟨⟨(r.val : ℤ), n⟩, ?_⟩
  ext
  · rfl
  · change (((r.val : ℕ) : ℤ) : ZMod 2) = r
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The horizontal class is the nonzero order-two summand. -/
theorem horizontal_class_order_two :
    (2 : ℕ) • abelianReadout a = 0 := by
  ext <;> norm_num

/-- The glide class supplies the unrestricted integral coordinate. -/
theorem vertical_class_zsmul_eq_zero_iff (n : ℤ) :
    n • abelianReadout b = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    simpa using hfst
  · rintro rfl
    simp

/-- Algebraic Klein normal-form packet. -/
theorem klein_deck_packet :
    b * a * b⁻¹ = a⁻¹ ∧
      (∀ g p, deckAct g p = p ↔ g = 1) ∧
      orientationCharacter a = 1 ∧
      orientationCharacter b = -1 ∧
      Matrix.det (linearPart a) = 1 ∧
      Matrix.det (linearPart b) = -1 ∧
      Function.Surjective abelianReadout ∧
      (2 : ℕ) • abelianReadout a = 0 := by
  exact ⟨klein_conjugation_relation,
    deckAct_eq_self_iff,
    orientationCharacter_a,
    orientationCharacter_b,
    det_linearPart_a,
    det_linearPart_b,
    abelianReadout_surjective,
    horizontal_class_order_two⟩

end InfoGeometry.Topology.KleinDeckNormalForm

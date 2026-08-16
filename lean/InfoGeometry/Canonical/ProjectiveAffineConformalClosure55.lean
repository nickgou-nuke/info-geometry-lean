import Mathlib.Tactic

/-!
# Projective affine conformal closure at `O(5,5)` / `Pin(5,5)`

Finite algebraic core:
* split affine space `ℝ^(4,4)` has quadratic form `Q44`;
* its projective conformal closure is modeled by the null cone of `ℝ^(5,5)`;
* the standard affine chart embedding
  `x ↦ (x, (1-Q44 x)/2, (1+Q44 x)/2)` is null for `Q55`;
* elementary `O(5,5)` reflections preserve `Q55`;
* the spectral CPT map has fixed locus `Re(s)=1/2`.
-/

noncomputable section

namespace ProjectiveAffineConformalClosure55

open scoped ComplexConjugate

/-- Split-octonionic affine coordinate model `ℝ^(4,4)`. -/
structure PACSplit44 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ
  y3 : ℝ

/-- Ambient conformal coordinate model `ℝ^(5,5) = ℝ^(4,4) ⊕ ℝ^(1,1)`. -/
structure PACSplit55 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ
  y3 : ℝ
  u : ℝ
  v : ℝ

/-- Split quadratic form of signature `(4,4)`. -/
def Q44 (x : PACSplit44) : ℝ :=
  x.x0^2 + x.x1^2 + x.x2^2 + x.x3^2 -
    (x.y0^2 + x.y1^2 + x.y2^2 + x.y3^2)

/-- Split quadratic form of signature `(5,5)`. -/
def Q55 (X : PACSplit55) : ℝ :=
  X.x0^2 + X.x1^2 + X.x2^2 + X.x3^2 + X.u^2 -
    (X.y0^2 + X.y1^2 + X.y2^2 + X.y3^2 + X.v^2)

/-- Affine conformal embedding into the projective null cone. -/
def conformalEmbed44to55 (x : PACSplit44) : PACSplit55 where
  x0 := x.x0
  x1 := x.x1
  x2 := x.x2
  x3 := x.x3
  y0 := x.y0
  y1 := x.y1
  y2 := x.y2
  y3 := x.y3
  u := (1 - Q44 x) / 2
  v := (1 + Q44 x) / 2

/-- The affine chart lands on the null cone of `ℝ^(5,5)`. -/
theorem conformalEmbed44to55_null (x : PACSplit44) :
    Q55 (conformalEmbed44to55 x) = 0 := by
  unfold Q55 conformalEmbed44to55 Q44
  ring

/-- Scalar multiplication in the ambient projective space. -/
def smul55 (a : ℝ) (X : PACSplit55) : PACSplit55 where
  x0 := a * X.x0
  x1 := a * X.x1
  x2 := a * X.x2
  x3 := a * X.x3
  y0 := a * X.y0
  y1 := a * X.y1
  y2 := a * X.y2
  y3 := a * X.y3
  u := a * X.u
  v := a * X.v

@[simp] theorem smul55_one (X : PACSplit55) : smul55 1 X = X := by
  cases X
  simp [smul55]

theorem smul55_smul (a b : ℝ) (X : PACSplit55) :
    smul55 a (smul55 b X) = smul55 (a * b) X := by
  cases X
  simp only [smul55]
  congr 1 <;> ring

/-- Projective same-line relation in the ambient conformal space. -/
def sameProjectiveLine55 (X Y : PACSplit55) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ Y = smul55 a X

/-- Projective equivalence is reflexive. -/
theorem sameProjectiveLine55_refl (X : PACSplit55) :
    sameProjectiveLine55 X X := by
  refine ⟨1, by norm_num, ?_⟩
  cases X
  simp [smul55]

theorem sameProjectiveLine55_symm {X Y : PACSplit55}
    (h : sameProjectiveLine55 X Y) :
    sameProjectiveLine55 Y X := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  rw [smul55_smul, inv_mul_cancel₀ ha, smul55_one]

theorem sameProjectiveLine55_trans {X Y Z : PACSplit55}
    (hXY : sameProjectiveLine55 X Y)
    (hYZ : sameProjectiveLine55 Y Z) :
    sameProjectiveLine55 X Z := by
  rcases hXY with ⟨a, ha, rfl⟩
  rcases hYZ with ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  rw [smul55_smul]

def projectiveSetoid55 : Setoid PACSplit55 where
  r := sameProjectiveLine55
  iseqv := {
    refl := sameProjectiveLine55_refl
    symm := sameProjectiveLine55_symm
    trans := sameProjectiveLine55_trans
  }

/-- The actual projective carrier of the split conformal ambient space. -/
abbrev Projective55 := Quotient projectiveSetoid55

def projectiveMk55 (X : PACSplit55) : Projective55 :=
  Quotient.mk projectiveSetoid55 X

/-- The null cone condition is invariant under nonzero projective rescaling. -/
theorem Q55_smul (a : ℝ) (X : PACSplit55) :
    Q55 (smul55 a X) = a^2 * Q55 X := by
  cases X
  unfold Q55 smul55
  ring

/-- Projective rescaling preserves nullity. -/
theorem projective_rescale_preserves_null
    {X Y : PACSplit55} (h : sameProjectiveLine55 X Y) (hX : Q55 X = 0) :
    Q55 Y = 0 := by
  rcases h with ⟨a, _ha, rfl⟩
  rw [Q55_smul, hX]
  ring

theorem sameProjectiveLine55_null_iff {X Y : PACSplit55}
    (h : sameProjectiveLine55 X Y) :
    Q55 X = 0 ↔ Q55 Y = 0 := by
  constructor
  · exact projective_rescale_preserves_null h
  · exact projective_rescale_preserves_null (sameProjectiveLine55_symm h)

/-- Nullity is a well-defined predicate on the projective quotient. -/
def projectiveNull55 : Projective55 → Prop :=
  Quotient.lift (fun X => Q55 X = 0) (by
    intro X Y h
    apply propext
    exact sameProjectiveLine55_null_iff h)

/-- A concrete `O(5,5)`-type reflection: flip the added positive coordinate. -/
def reflectU (X : PACSplit55) : PACSplit55 where
  x0 := X.x0; x1 := X.x1; x2 := X.x2; x3 := X.x3
  y0 := X.y0; y1 := X.y1; y2 := X.y2; y3 := X.y3
  u := -X.u; v := X.v

/-- A concrete `O(5,5)`-type reflection: flip the added negative coordinate. -/
def reflectV (X : PACSplit55) : PACSplit55 where
  x0 := X.x0; x1 := X.x1; x2 := X.x2; x3 := X.x3
  y0 := X.y0; y1 := X.y1; y2 := X.y2; y3 := X.y3
  u := X.u; v := -X.v

theorem reflectU_smul (a : ℝ) (X : PACSplit55) :
    reflectU (smul55 a X) = smul55 a (reflectU X) := by
  cases X
  simp [reflectU, smul55]

theorem reflectV_smul (a : ℝ) (X : PACSplit55) :
    reflectV (smul55 a X) = smul55 a (reflectV X) := by
  cases X
  simp [reflectV, smul55]

def reflectUProjective : Projective55 → Projective55 :=
  Quotient.lift (fun X => projectiveMk55 (reflectU X)) (by
    intro X Y hXY
    rcases hXY with ⟨a, ha, hXY⟩
    change projectiveMk55 (reflectU X) = projectiveMk55 (reflectU Y)
    apply Quotient.sound
    refine ⟨a, ha, ?_⟩
    rw [hXY, reflectU_smul])

def reflectVProjective : Projective55 → Projective55 :=
  Quotient.lift (fun X => projectiveMk55 (reflectV X)) (by
    intro X Y hXY
    rcases hXY with ⟨a, ha, hXY⟩
    change projectiveMk55 (reflectV X) = projectiveMk55 (reflectV Y)
    apply Quotient.sound
    refine ⟨a, ha, ?_⟩
    rw [hXY, reflectV_smul])

/-- The `u` reflection preserves the split `(5,5)` quadratic form. -/
theorem reflectU_preserves_Q55 (X : PACSplit55) :
    Q55 (reflectU X) = Q55 X := by
  cases X
  unfold Q55 reflectU
  ring

/-- The `v` reflection preserves the split `(5,5)` quadratic form. -/
theorem reflectV_preserves_Q55 (X : PACSplit55) :
    Q55 (reflectV X) = Q55 X := by
  cases X
  unfold Q55 reflectV
  ring

/-- Reflections preserve the projective null cone. -/
theorem reflectU_preserves_null (X : PACSplit55) (hX : Q55 X = 0) :
    Q55 (reflectU X) = 0 := by
  rw [reflectU_preserves_Q55, hX]

theorem reflectV_preserves_null (X : PACSplit55) (hX : Q55 X = 0) :
    Q55 (reflectV X) = 0 := by
  rw [reflectV_preserves_Q55, hX]

theorem reflectUProjective_preserves_null (P : Projective55)
    (hP : projectiveNull55 P) :
    projectiveNull55 (reflectUProjective P) := by
  revert hP
  refine Quotient.inductionOn P ?_
  intro X hX
  change Q55 X = 0 at hX
  change Q55 (reflectU X) = 0
  rw [reflectU_preserves_Q55, hX]

theorem reflectVProjective_preserves_null (P : Projective55)
    (hP : projectiveNull55 P) :
    projectiveNull55 (reflectVProjective P) := by
  revert hP
  refine Quotient.inductionOn P ?_
  intro X hX
  change Q55 X = 0 at hX
  change Q55 (reflectV X) = 0
  rw [reflectV_preserves_Q55, hX]

@[simp] theorem reflectUProjective_involutive (P : Projective55) :
    reflectUProjective (reflectUProjective P) = P := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectU (reflectU X)) = projectiveMk55 X
  cases X
  simp [reflectU]

@[simp] theorem reflectVProjective_involutive (P : Projective55) :
    reflectVProjective (reflectVProjective P) = P := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectV (reflectV X)) = projectiveMk55 X
  cases X
  simp [reflectV]

/-- The `u` reflection as an involutive projective equivalence. -/
def reflectUProjectiveEquiv : Projective55 ≃ Projective55 where
  toFun := reflectUProjective
  invFun := reflectUProjective
  left_inv := reflectUProjective_involutive
  right_inv := reflectUProjective_involutive

/-- The `v` reflection as an involutive projective equivalence. -/
def reflectVProjectiveEquiv : Projective55 ≃ Projective55 where
  toFun := reflectVProjective
  invFun := reflectVProjective
  left_inv := reflectVProjective_involutive
  right_inv := reflectVProjective_involutive

theorem reflectUProjective_commute_reflectVProjective (P : Projective55) :
    reflectUProjective (reflectVProjective P) =
      reflectVProjective (reflectUProjective P) := by
  refine Quotient.inductionOn P ?_
  intro X
  change projectiveMk55 (reflectU (reflectV X)) =
    projectiveMk55 (reflectV (reflectU X))
  cases X
  rfl

theorem reflectUProjectiveEquiv_commute_reflectVProjectiveEquiv :
    reflectUProjectiveEquiv * reflectVProjectiveEquiv =
      reflectVProjectiveEquiv * reflectUProjectiveEquiv := by
  apply Equiv.ext
  intro P
  exact reflectUProjective_commute_reflectVProjective P

/-- Spectral CPT involution `s ↦ 1 - conj(s)`. -/
def spectralCPT (s : ℂ) : ℂ :=
  1 - conj s

/-- Fixed points of spectral CPT are exactly the critical line. -/
theorem spectralCPT_fixed_iff_criticalLine (s : ℂ) :
    spectralCPT s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre : (spectralCPT s).re = s.re := by rw [h]
    unfold spectralCPT at hre
    simp at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [spectralCPT, h]
      norm_num
    · simp [spectralCPT]

end ProjectiveAffineConformalClosure55

end noncomputable section

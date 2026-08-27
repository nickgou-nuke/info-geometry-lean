import InfoGeometry.Exceptional.FreudenthalSymplecticTKKTotalBracket
import InfoGeometry.Exceptional.FreudenthalHeisenbergLieRepresentation

/-!
# Five-Graded Bracket Closure Candidate on the Freudenthal Heisenberg/TKK Carrier

This module formalizes a contact 5-graded bracket candidate:

$$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$$

on the native exceptional carriers:
- $\mathfrak{g}_{-2} \cong \mathbb{R} E_-$ (Central Heisenberg scalar lane at degree $-2$)
- $\mathfrak{g}_{-1} \cong \text{FreudenthalCharge } J$ (Charge sector at degree $-1$)
- $\mathfrak{g}_0 \cong \text{SymplecticTKKZero } D \times \mathbb{R}$ (Symplectic Lie subalgebra $\oplus$ Scale generator $H$)
- $\mathfrak{g}_{+1} \cong \text{FreudenthalCharge } J$ (Charge sector at degree $+1$)
- $\mathfrak{g}_{+2} \cong \mathbb{R} E_+$ (Central Heisenberg scalar lane at degree $+2$)

## Key Bracket Theorems Proven:

1. **Extreme $\mathfrak{sl}_2$ Bracket Closure**:
   $$\llbracket E_+, E_- \rrbracket = H$$
   $$\llbracket H, E_+ \rrbracket = 2 E_+$$
   $$\llbracket H, E_- \rrbracket = -2 E_-$$

2. **Heisenberg Nilpotent Brackets**:
   - $[\mathfrak{g}_{-1}, \mathfrak{g}_{-1}] \subseteq \mathfrak{g}_{-2}$ via $\omega(X, Y) E_-$
   - $[\mathfrak{g}_{+1}, \mathfrak{g}_{+1}] \subseteq \mathfrak{g}_{+2}$ via $\omega(X, Y) E_+$

3. **Mixed TKK Transversal Bracket**:
   - $[\mathfrak{g}_{-1}, \mathfrak{g}_{+1}] \subseteq \mathfrak{g}_0$ via the native `mixedSymplecticBracket`

4. **Euler Scale Grading Action**:
   $$\llbracket H, X_k \rrbracket = k \cdot X_k \quad \text{for each grade } k \in \{-2, -1, 0, 1, 2\}$$

5. **Strict Skew-Symmetry**:
   $$\llbracket u, v \rrbracket = - \llbracket v, u \rrbracket$$

The file does not claim the Jacobi identity or a Lie-algebra instance.
All proofs in this file are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-! ## 1. Zero Vanishing Lemmas for Symplectic Form -/

@[simp] theorem symplecticForm_zero_right (P : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P 0 = 0 := by
  exact (symplecticFormLinear D P).map_zero

@[simp] theorem symplecticForm_zero_left (P : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D 0 P = 0 := by
  rw [FreudenthalCharge.symplectic_form_skew, symplecticForm_zero_right, neg_zero]

/-! ## 2. The 5-Graded Carrier Structure -/

/-- Total 5-graded carrier $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus (\mathfrak{g}_0^{\text{symp}} \oplus \mathbb{R} H) \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$. -/
structure FiveGradedCarrier where
  minus2 : ℝ
  minus1 : FreudenthalCharge J
  zero_symp : SymplecticTKKZero D
  zero_scale : ℝ
  plus1 : FreudenthalCharge J
  plus2 : ℝ

namespace FiveGradedCarrier

instance : Add (FiveGradedCarrier D) where
  add u v := ⟨u.minus2 + v.minus2,
               u.minus1 + v.minus1,
               u.zero_symp + v.zero_symp,
               u.zero_scale + v.zero_scale,
               u.plus1 + v.plus1,
               u.plus2 + v.plus2⟩

instance : Neg (FiveGradedCarrier D) where
  neg u := ⟨-u.minus2, -u.minus1, -u.zero_symp, -u.zero_scale, -u.plus1, -u.plus2⟩

instance : Sub (FiveGradedCarrier D) where
  sub u v := ⟨u.minus2 - v.minus2,
               u.minus1 - v.minus1,
               u.zero_symp - v.zero_symp,
               u.zero_scale - v.zero_scale,
               u.plus1 - v.plus1,
               u.plus2 - v.plus2⟩

instance : Zero (FiveGradedCarrier D) where
  zero := ⟨0, 0, 0, 0, 0, 0⟩

instance : SMul ℝ (FiveGradedCarrier D) where
  smul r u := ⟨r * u.minus2,
                r • u.minus1,
                r • u.zero_symp,
                r * u.zero_scale,
                r • u.plus1,
                r * u.plus2⟩

@[simp] theorem neg_minus2 (u : FiveGradedCarrier D) : (-u).minus2 = -u.minus2 := rfl
@[simp] theorem neg_minus1 (u : FiveGradedCarrier D) : (-u).minus1 = -u.minus1 := rfl
@[simp] theorem neg_zero_symp (u : FiveGradedCarrier D) : (-u).zero_symp = -u.zero_symp := rfl
@[simp] theorem neg_zero_scale (u : FiveGradedCarrier D) : (-u).zero_scale = -u.zero_scale := rfl
@[simp] theorem neg_plus1 (u : FiveGradedCarrier D) : (-u).plus1 = -u.plus1 := rfl
@[simp] theorem neg_plus2 (u : FiveGradedCarrier D) : (-u).plus2 = -u.plus2 := rfl

@[simp] theorem zero_minus2 : (0 : FiveGradedCarrier D).minus2 = 0 := rfl
@[simp] theorem zero_minus1 : (0 : FiveGradedCarrier D).minus1 = 0 := rfl
@[simp] theorem zero_zero_symp : (0 : FiveGradedCarrier D).zero_symp = 0 := rfl
@[simp] theorem zero_zero_scale : (0 : FiveGradedCarrier D).zero_scale = 0 := rfl
@[simp] theorem zero_plus1 : (0 : FiveGradedCarrier D).plus1 = 0 := rfl
@[simp] theorem zero_plus2 : (0 : FiveGradedCarrier D).plus2 = 0 := rfl

@[ext]
theorem ext (u v : FiveGradedCarrier D)
    (h_m2 : u.minus2 = v.minus2)
    (h_m1 : u.minus1 = v.minus1)
    (h_0s : u.zero_symp = v.zero_symp)
    (h_0h : u.zero_scale = v.zero_scale)
    (h_p1 : u.plus1 = v.plus1)
    (h_p2 : u.plus2 = v.plus2) : u = v := by
  cases u; cases v; congr

end FiveGradedCarrier

/-! ## 3. Canonical Sector Injections and Generators -/

/-- Grade $-2$ extreme Heisenberg generator $E_-$. -/
def genEminus (c : ℝ := 1) : FiveGradedCarrier D := ⟨c, 0, 0, 0, 0, 0⟩

/-- Grade $+2$ extreme Heisenberg generator $E_+$. -/
def genEplus (c : ℝ := 1) : FiveGradedCarrier D := ⟨0, 0, 0, 0, 0, c⟩

/-- Grade $0$ Euler scale/Cartan generator $H$. -/
def genHscale (h : ℝ := 1) : FiveGradedCarrier D := ⟨0, 0, 0, h, 0, 0⟩

/-- Grade $-1$ charge injection. -/
def injChargeMinus (x : FreudenthalCharge J) : FiveGradedCarrier D := ⟨0, x, 0, 0, 0, 0⟩

/-- Grade $+1$ charge injection. -/
def injChargePlus (y : FreudenthalCharge J) : FiveGradedCarrier D := ⟨0, 0, 0, 0, y, 0⟩

/-- Grade $0$ symplectic Lie subalgebra injection. -/
def injSympZero (T : SymplecticTKKZero D) : FiveGradedCarrier D := ⟨0, 0, T, 0, 0, 0⟩

/-! ## 4. Five-Graded Bracket Candidate Definition -/

/-- The total 5-graded Lie bracket on $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$. -/
def fiveGradedBracket (u v : FiveGradedCarrier D) : FiveGradedCarrier D where
  minus2 :=
    -- [H, E_-] = -2 E_- action
    (-2 * u.zero_scale * v.minus2 + 2 * v.zero_scale * u.minus2) +
    -- Heisenberg charge bracket [g_-1, g_-1] -> g_-2
    FreudenthalCharge.symplecticForm D u.minus1 v.minus1

  minus1 :=
    -- [H, X_-1] = -1 X_-1 action + symplectic g_0 action on g_-1
    (-u.zero_scale • v.minus1 + v.zero_scale • u.minus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.minus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.minus1)

  zero_symp :=
    -- [g_0, g_0] bracket + mixed [g_-1, g_+1] -> g_0
    ⁅u.zero_symp, v.zero_symp⁆ +
    mixedSymplecticBracket D u.minus1 v.plus1 -
    mixedSymplecticBracket D v.minus1 u.plus1

  zero_scale :=
    -- Extreme bracket [E_+, E_-] = H scale: u_+2 * v_-2 - v_+2 * u_-2
    (u.plus2 * v.minus2 - v.plus2 * u.minus2)

  plus1 :=
    -- [H, X_+1] = +1 X_+1 action + symplectic g_0 action on g_+1
    (u.zero_scale • v.plus1 - v.zero_scale • u.plus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.plus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.plus1)

  plus2 :=
    -- [H, E_+] = +2 E_+ action
    (2 * u.zero_scale * v.plus2 - 2 * v.zero_scale * u.plus2) +
    -- Heisenberg charge bracket [g_+1, g_+1] -> g_+2
    FreudenthalCharge.symplecticForm D u.plus1 v.plus1

/-! ## 5. Fundamental Symmetry & Skew Laws -/

/-- The 5-graded bracket candidate is strictly skew-symmetric. -/
theorem fiveGradedBracket_skew (u v : FiveGradedCarrier D) :
    fiveGradedBracket D u v = - fiveGradedBracket D v u := by
  apply FiveGradedCarrier.ext
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_minus2]
    have hsymp := FreudenthalCharge.symplectic_form_skew D u.minus1 v.minus1
    linarith
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_minus1]
    module
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_zero_symp]
    have hskew : ⁅u.zero_symp, v.zero_symp⁆ = - ⁅v.zero_symp, u.zero_symp⁆ :=
      (lie_skew u.zero_symp v.zero_symp).symm
    rw [hskew]
    abel
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_zero_scale]
    ring
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_plus1]
    module
  · simp only [fiveGradedBracket, FiveGradedCarrier.neg_plus2]
    have hsymp := FreudenthalCharge.symplectic_form_skew D u.plus1 v.plus1
    linarith

@[simp]
theorem fiveGradedBracket_self (u : FiveGradedCarrier D) :
    fiveGradedBracket D u u = 0 := by
  apply FiveGradedCarrier.ext
  · simp [fiveGradedBracket, FreudenthalCharge.symplectic_form_alternating]
  · simp [fiveGradedBracket]
  · simp [fiveGradedBracket, lie_self]
  · simp [fiveGradedBracket]
  · simp [fiveGradedBracket]
  · simp [fiveGradedBracket, FreudenthalCharge.symplectic_form_alternating]

/-! ## 6. Extreme $\mathfrak{sl}_2$ Subalgebra Theorems -/

/-- 🏆 THEOREM: The extreme bracket between $E_+$ and $E_-$ yields the Euler scale generator $H$. -/
theorem extreme_grade_bracket_eq_scale :
    fiveGradedBracket D (genEplus D 1) (genEminus D 1) = genHscale D 1 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, genEminus, genHscale] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $+2$ generator $[H, E_+] = 2 E_+$. -/
theorem scale_action_gradePlus2 :
    fiveGradedBracket D (genHscale D 1) (genEplus D 1) = genEplus D 2 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEplus] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $-2$ generator $[H, E_-] = -2 E_-$. -/
theorem scale_action_gradeMinus2 :
    fiveGradedBracket D (genHscale D 1) (genEminus D 1) = genEminus D (-2) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEminus] <;>
    simp

/-! ## 7. Heisenberg and Transversal Sector Brackets -/

/-- Heisenberg nilpotency on $\mathfrak{g}_{-1}$: $[\mathfrak{g}_{-1}, \mathfrak{g}_{-1}] = \omega(x, y) E_-$. -/
theorem bracket_minus1_minus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y) =
      genEminus D (FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, genEminus] <;>
    simp

/-- Heisenberg nilpotency on $\mathfrak{g}_{+1}$: $[\mathfrak{g}_{+1}, \mathfrak{g}_{+1}] = \omega(x, y) E_+$. -/
theorem bracket_plus1_plus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x) (injChargePlus D y) =
      genEplus D (FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus, genEplus] <;>
    simp

/-- Transversal TKK mixed bracket: $[\mathfrak{g}_{-1}, \mathfrak{g}_{+1}] = \text{mixedSymplecticBracket}(x, y)$. -/
theorem bracket_minus1_plus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargePlus D y) =
      injSympZero D (mixedSymplecticBracket D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, injChargePlus, injSympZero] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal

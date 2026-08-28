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

@[simp] theorem symplecticForm_neg_right (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D P (-Q) = -FreudenthalCharge.symplecticForm D P Q := by
  exact (symplecticFormLinear D P).map_neg Q

@[simp] theorem symplecticForm_neg_left (P Q : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (-P) Q = -FreudenthalCharge.symplecticForm D P Q := by
  rw [FreudenthalCharge.symplectic_form_skew, symplecticForm_neg_right,
      FreudenthalCharge.symplectic_form_skew, neg_neg]

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

instance carrierSMul : SMul ℝ (FiveGradedCarrier D) where
  smul r u := ⟨r * u.minus2,
                r • u.minus1,
                r • u.zero_symp,
                r * u.zero_scale,
                r • u.plus1,
                r * u.plus2⟩

@[simp] theorem smul_minus2 (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).minus2 = r * u.minus2 := rfl
@[simp] theorem smul_minus1 (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).minus1 = r • u.minus1 := rfl
@[simp] theorem smul_zero_symp (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).zero_symp = r • u.zero_symp := rfl
@[simp] theorem smul_zero_scale (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).zero_scale = r * u.zero_scale := rfl
@[simp] theorem smul_plus1 (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).plus1 = r • u.plus1 := rfl
@[simp] theorem smul_plus2 (r : ℝ) (u : FiveGradedCarrier D) :
    (r • u).plus2 = r * u.plus2 := rfl

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

@[simp] theorem add_minus2 (u v : FiveGradedCarrier D) :
    (u + v).minus2 = u.minus2 + v.minus2 := rfl
@[simp] theorem add_minus1 (u v : FiveGradedCarrier D) :
    (u + v).minus1 = u.minus1 + v.minus1 := rfl
@[simp] theorem add_zero_symp (u v : FiveGradedCarrier D) :
    (u + v).zero_symp = u.zero_symp + v.zero_symp := rfl
@[simp] theorem add_zero_scale (u v : FiveGradedCarrier D) :
    (u + v).zero_scale = u.zero_scale + v.zero_scale := rfl
@[simp] theorem add_plus1 (u v : FiveGradedCarrier D) :
    (u + v).plus1 = u.plus1 + v.plus1 := rfl
@[simp] theorem add_plus2 (u v : FiveGradedCarrier D) :
    (u + v).plus2 = u.plus2 + v.plus2 := rfl

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
    (2 * FreudenthalCharge.symplecticForm D u.minus1 v.minus1)

  minus1 :=
    -- [H, X_-1] = -1 X_-1 action + symplectic g_0 action on g_-1
    (-u.zero_scale • v.minus1 + v.zero_scale • u.minus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.minus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.minus1) +
    -- [g_-2, g_+1] -> g_-1 extreme action
    (u.minus2 • v.plus1 - v.minus2 • u.plus1)

  zero_symp :=
    -- [g_0, g_0] bracket + mixed [g_-1, g_+1] -> g_0
    ⁅u.zero_symp, v.zero_symp⁆ +
    mixedSymplecticBracket D u.minus1 v.plus1 -
    mixedSymplecticBracket D v.minus1 u.plus1

  zero_scale :=
    -- Extreme bracket [E_+, E_-] = H scale: u_+2 * v_-2 - v_+2 * u_-2
    (u.plus2 * v.minus2 - v.plus2 * u.minus2) +
    -- Mixed [g_-1, g_+1] -> R H scale projection
    (FreudenthalCharge.symplecticForm D u.minus1 v.plus1 -
     FreudenthalCharge.symplecticForm D v.minus1 u.plus1)

  plus1 :=
    -- [H, X_+1] = +1 X_+1 action + symplectic g_0 action on g_+1
    (u.zero_scale • v.plus1 - v.zero_scale • u.plus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.plus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.plus1) +
    -- [g_+2, g_-1] -> g_+1 Chevalley-dual action
    (-u.plus2 • v.minus1 + v.plus2 • u.minus1)

  plus2 :=
    -- [H, E_+] = +2 E_+ action
    (2 * u.zero_scale * v.plus2 - 2 * v.zero_scale * u.plus2) +
    -- Heisenberg charge bracket [g_+1, g_+1] -> g_+2
    (2 * FreudenthalCharge.symplecticForm D u.plus1 v.plus1)

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
    have hsymp1 := FreudenthalCharge.symplectic_form_skew D u.minus1 v.plus1
    have hsymp2 := FreudenthalCharge.symplectic_form_skew D v.minus1 u.plus1
    linarith
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

/-- 🏆 THEOREM: Scale action on the grade $+1$ charge generator $[H, y_+] = +1 y_+$. -/
theorem scale_action_gradePlus1 (y : FreudenthalCharge J) :
    fiveGradedBracket D (genHscale D 1) (injChargePlus D y) = injChargePlus D y := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injChargePlus] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $0$ symplectic subalgebra $[H, T_0] = 0$. -/
theorem scale_action_gradeZeroSymp (T : SymplecticTKKZero D) :
    fiveGradedBracket D (genHscale D 1) (injSympZero D T) = 0 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injSympZero] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $0$ scale generator $[H, H] = 0$. -/
theorem scale_action_gradeZeroScale :
    fiveGradedBracket D (genHscale D 1) (genHscale D 1) = 0 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $-1$ charge generator $[H, x_-] = -1 x_-$. -/
theorem scale_action_gradeMinus1 (x : FreudenthalCharge J) :
    fiveGradedBracket D (genHscale D 1) (injChargeMinus D x) = injChargeMinus D (-x) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, injChargeMinus] <;>
    simp

/-- 🏆 THEOREM: Scale action on the grade $-2$ generator $[H, E_-] = -2 E_-$. -/
theorem scale_action_gradeMinus2 :
    fiveGradedBracket D (genHscale D 1) (genEminus D 1) = genEminus D (-2) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genHscale, genEminus] <;>
    simp

/-! ## 7. Heisenberg and Transversal Sector Brackets -/

@[simp] theorem fiveGradedBracket_chargeMinus_chargeMinus (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y) =
      ⟨2 * FreudenthalCharge.symplecticForm D x y, 0, 0, 0, 0, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus] <;>
    simp

@[simp] theorem fiveGradedBracket_chargePlus_chargePlus (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x) (injChargePlus D y) =
      ⟨0, 0, 0, 0, 0, 2 * FreudenthalCharge.symplecticForm D x y⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus] <;>
    simp

@[simp] theorem fiveGradedBracket_chargeMinus_chargePlus (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargePlus D y) =
      ⟨0, 0, mixedSymplecticBracket D x y,
       FreudenthalCharge.symplecticForm D x y, 0, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, injChargePlus] <;>
    simp

@[simp] theorem fiveGradedBracket_chargePlus_chargeMinus (y x : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D y) (injChargeMinus D x) =
      ⟨0, 0, -mixedSymplecticBracket D x y,
       -FreudenthalCharge.symplecticForm D x y, 0, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, injChargePlus] <;>
    simp

@[simp] theorem fiveGradedBracket_chargeMinus_zeroBlock
    (x : FreudenthalCharge J) (T : SymplecticTKKZero D) (h : ℝ) :
    fiveGradedBracket D (injChargeMinus D x) ⟨0, 0, T, h, 0, 0⟩ =
      ⟨0, h • x - (T : Module.End ℝ (FreudenthalCharge J)) x, 0, 0, 0, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus] <;>
    simp [sub_eq_add_neg]

@[simp] theorem fiveGradedBracket_chargePlus_zeroBlock
    (x : FreudenthalCharge J) (T : SymplecticTKKZero D) (h : ℝ) :
    fiveGradedBracket D (injChargePlus D x) ⟨0, 0, T, h, 0, 0⟩ =
      ⟨0, 0, 0, 0, -h • x - (T : Module.End ℝ (FreudenthalCharge J)) x, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus] <;>
    simp [sub_eq_add_neg]

@[simp] theorem fiveGradedBracket_chargePlus_genEminus
    (z : FreudenthalCharge J) (c : ℝ) :
    fiveGradedBracket D (injChargePlus D z) ⟨c, 0, 0, 0, 0, 0⟩ =
      ⟨0, -c • z, 0, 0, 0, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus] <;>
    simp

@[simp] theorem fiveGradedBracket_chargeMinus_genEplus
    (z : FreudenthalCharge J) (c : ℝ) :
    fiveGradedBracket D (injChargeMinus D z) ⟨0, 0, 0, 0, 0, c⟩ =
      ⟨0, 0, 0, 0, c • z, 0⟩ := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus] <;>
    simp

/-- Heisenberg nilpotency on $\mathfrak{g}_{-1}$: $[\mathfrak{g}_{-1}, \mathfrak{g}_{-1}] = 2\omega(x, y) E_-$. -/
theorem bracket_minus1_minus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y) =
      genEminus D (2 * FreudenthalCharge.symplecticForm D x y) :=
  fiveGradedBracket_chargeMinus_chargeMinus D x y

/-- Heisenberg nilpotency on $\mathfrak{g}_{+1}$: $[\mathfrak{g}_{+1}, \mathfrak{g}_{+1}] = 2\omega(x, y) E_+$. -/
theorem bracket_plus1_plus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x) (injChargePlus D y) =
      genEplus D (2 * FreudenthalCharge.symplecticForm D x y) :=
  fiveGradedBracket_chargePlus_chargePlus D x y

/-- Transversal mixed bracket: $[\mathfrak{g}_{-1}, \mathfrak{g}_{+1}]$ yields mixed symplectic derivation plus scale $H$. -/
theorem bracket_minus1_plus1 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargePlus D y) =
      ⟨0, 0, mixedSymplecticBracket D x y,
       FreudenthalCharge.symplecticForm D x y, 0, 0⟩ :=
  fiveGradedBracket_chargeMinus_chargePlus D x y

/-- Extreme action of $E_-$ on $\mathfrak{g}_{+1}$: $[E_-, z_+] = z_-$. -/
theorem extreme_minus2_action_plus1 (z : FreudenthalCharge J) :
    fiveGradedBracket D (genEminus D 1) (injChargePlus D z) = injChargeMinus D z := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargePlus, injChargeMinus] <;>
    simp

/-- Extreme action of $E_+$ on $\mathfrak{g}_{-1}$: $[E_+, x_-] = -x_+$. -/
theorem extreme_plus2_action_minus1 (x : FreudenthalCharge J) :
    fiveGradedBracket D (genEplus D 1) (injChargeMinus D x) = injChargePlus D (-x) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargeMinus, injChargePlus] <;>
    simp

/-- 🏆 THEOREM: Exact cancellation of the $(-1,-1,+1)$ Jacobi obstruction in the 5-graded bracket. -/
theorem fiveGraded_minus_minus_plus_jacobi (x y z : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x)
      (fiveGradedBracket D (injChargeMinus D y) (injChargePlus D z)) +
    fiveGradedBracket D (injChargeMinus D y)
      (fiveGradedBracket D (injChargePlus D z) (injChargeMinus D x)) +
    fiveGradedBracket D (injChargePlus D z)
      (fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y)) = 0 := by
  rw [fiveGradedBracket_chargeMinus_chargePlus,
      fiveGradedBracket_chargePlus_chargeMinus,
      fiveGradedBracket_chargeMinus_chargeMinus]
  rw [fiveGradedBracket_chargeMinus_zeroBlock,
      fiveGradedBracket_chargeMinus_zeroBlock,
      fiveGradedBracket_chargePlus_genEminus]
  apply FiveGradedCarrier.ext
  · dsimp [FiveGradedCarrier.instAdd]; ring
  · dsimp [FiveGradedCarrier.instAdd]
    have hjac := symplecticRankTwo_jacobi_pattern D x y z
    calc
      (FreudenthalCharge.symplecticForm D y z • x - symplecticRankTwo D y z x) +
        (-FreudenthalCharge.symplecticForm D x z • y - -symplecticRankTwo D x z y) +
        -(2 * FreudenthalCharge.symplecticForm D x y) • z
        = (- symplecticRankTwo D y z x + symplecticRankTwo D x z y) -
          (FreudenthalCharge.symplecticForm D x z • y -
           FreudenthalCharge.symplecticForm D y z • x +
           (2 * FreudenthalCharge.symplecticForm D x y) • z) := by module
      _ = (FreudenthalCharge.symplecticForm D x z • y -
           FreudenthalCharge.symplecticForm D y z • x +
           (2 * FreudenthalCharge.symplecticForm D x y) • z) -
          (FreudenthalCharge.symplecticForm D x z • y -
           FreudenthalCharge.symplecticForm D y z • x +
           (2 * FreudenthalCharge.symplecticForm D x y) • z) := by rw [hjac]
      _ = 0 := by module
  · dsimp [FiveGradedCarrier.instAdd]; abel
  · dsimp [FiveGradedCarrier.instAdd]; ring
  · dsimp [FiveGradedCarrier.instAdd]; module
  · dsimp [FiveGradedCarrier.instAdd]; ring

/-- 🏆 THEOREM: Exact cancellation of the (+1,+1,-1) dual Jacobi obstruction in the 5-graded bracket. -/
theorem fiveGraded_plus_plus_minus_jacobi (x y z : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x)
      (fiveGradedBracket D (injChargePlus D y) (injChargeMinus D z)) +
    fiveGradedBracket D (injChargePlus D y)
      (fiveGradedBracket D (injChargeMinus D z) (injChargePlus D x)) +
    fiveGradedBracket D (injChargeMinus D z)
      (fiveGradedBracket D (injChargePlus D x) (injChargePlus D y)) = 0 := by
  rw [fiveGradedBracket_chargePlus_chargeMinus,
      fiveGradedBracket_chargeMinus_chargePlus,
      fiveGradedBracket_chargePlus_chargePlus]
  rw [fiveGradedBracket_chargePlus_zeroBlock,
      fiveGradedBracket_chargePlus_zeroBlock,
      fiveGradedBracket_chargeMinus_genEplus]
  apply FiveGradedCarrier.ext
  · dsimp [FiveGradedCarrier.instAdd]; ring
  · dsimp [FiveGradedCarrier.instAdd]; module
  · dsimp [FiveGradedCarrier.instAdd]; abel
  · dsimp [FiveGradedCarrier.instAdd]; ring
  · dsimp [FiveGradedCarrier.instAdd]
    have hswap := symplecticRankTwo_swap23 D z y x
    have hskew_zx := FreudenthalCharge.symplectic_form_skew D z x
    have hskew_zy := FreudenthalCharge.symplectic_form_skew D z y
    have hskew_yx := FreudenthalCharge.symplectic_form_skew D y x
    calc
      (- -FreudenthalCharge.symplecticForm D z y • x - -(symplecticRankTwo D z y) x) +
        (-FreudenthalCharge.symplecticForm D z x • y - symplecticRankTwo D z x y) +
        (2 * FreudenthalCharge.symplecticForm D x y) • z
        = (symplecticRankTwo D z y x - symplecticRankTwo D z x y) -
          (FreudenthalCharge.symplecticForm D z x • y -
           FreudenthalCharge.symplecticForm D z y • x +
           (2 * FreudenthalCharge.symplecticForm D y x) • z) := by
             rw [hskew_yx]
             module
      _ = (FreudenthalCharge.symplecticForm D z x • y -
           FreudenthalCharge.symplecticForm D z y • x +
           (2 * FreudenthalCharge.symplecticForm D y x) • z) -
          (FreudenthalCharge.symplecticForm D z x • y -
           FreudenthalCharge.symplecticForm D z y • x +
           (2 * FreudenthalCharge.symplecticForm D y x) • z) := by rw [hswap]
      _ = 0 := by module
  · dsimp [FiveGradedCarrier.instAdd]; ring

end InfoGeometry.Exceptional.Freudenthal

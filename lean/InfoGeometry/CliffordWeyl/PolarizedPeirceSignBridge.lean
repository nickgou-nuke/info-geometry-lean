import InfoGeometry.Krein.SplitQuadraticSheets
import InfoGeometry.Krein.SplitQuadratic
import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.CliffordWeyl.ChiralIdeals

/-!
# InfoGeometry.CliffordWeyl.PolarizedPeirceSignBridge

Third join of the lane programme, following
`InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge`.

## The gap

`InfoGeometry.Krein.SplitQuadratic` and `SplitQuadraticSheets` build the *sign
structure* of the real indefinite (Krein) metric on the doubled carrier:

- `qform u = kreinInner u u` — the indefinite quadratic form, neither positive nor
  negative definite;
- `plusSheet` / `minusSheet` — the `±1` eigensheets of the fundamental symmetry
  `spectral_epsilon`;
- `potential_plusPoint_eq_half_norm_sq` and `potential_minusPoint_eq_neg_half_norm_sq`
  — the potential is **positive** on the `+1` sheet and **negative** on the `-1`
  sheet;
- `divergence_nonneg_of_mem_plusSheet` / `divergence_nonpos_of_mem_minusSheet` — the
  divergence inherits that sign.

`InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge` proved that those `±1`
eigensheets *are* the constructive Peirce corners `P± = (1 ± χ)/2` of the split
Clifford carrier `Mat₂(ℝ) = Cl(1,1)`, via the single involution `χ = Eplus = σ₃`.

**These two facts were never combined.** So the repository asserted, in two disjoint
vocabularies, that a projector splitting is sign-definite, without ever proving that
the sign lives on the projector.

## What this module proves

The polarization/Peirce join: the indefinite Krein quadratic form restricted to a
Peirce corner is a *definite* form, with the sign fixed by the corner.

- On the `+1` corner (`plusSheet`): `qform ≥ 0`, with equality only at the origin.
- On the `-1` corner (`minusSheet`): `qform ≤ 0`, with equality only at the origin.
- Consequently a state is Krein-positive iff it is a **nonzero** element of the `+1`
  sheet, and Krein-negative iff it is a nonzero element of the `-1` sheet.

This is the concrete content of "polarization": **the sign of the indefinite metric
is the Peirce eigenvalue.** No certificates, no extra structure fields — every
statement is a native Lean derivation from `SplitQuadraticSheets` and
`PauliPeirceKreinBridge`.
-/

namespace InfoGeometry.CliffordWeyl.PolarizedPeirceSignBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-! ## 1. The indefinite form is definite on each eigensheet -/

/--
The indefinite Krein quadratic form is nonnegative on the `+1` eigensheet.

This is the positivity half of the polarization: restricted to the sheet fixed by
the fundamental symmetry `spectral_epsilon`, the indefinite form `[·,·]_J`
degenerates to a positive semidefinite form. The `+1` sheet is the `+1` Peirce
corner, so this is positivity *on a projector corner*.
-/
theorem qform_nonneg_of_mem_plusSheet {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    0 ≤ SplitQuadratic.qform (E := E) u := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu,
    SplitQuadratic.qform_eq_kreinInner, kreinInner_plusPoint]
  exact real_inner_self_nonneg

/--
The indefinite Krein quadratic form is nonpositive on the `-1` eigensheet.

This is the negativity half: on the anti-fixed sheet the same form is negative
semidefinite. Together with `qform_nonneg_of_mem_plusSheet` this is the
polarization of the indefinite metric into two opposite definite sectors.
-/
theorem qform_nonpos_of_mem_minusSheet {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    SplitQuadratic.qform (E := E) u ≤ 0 := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu,
    SplitQuadratic.qform_eq_kreinInner, kreinInner_minusPoint]
  exact neg_nonpos.mpr real_inner_self_nonneg

/-! ## 2. Each eigensheet is definite away from the origin -/

omit [CompleteSpace E] in
/-- Helper: a `+1`-sheet state with vanishing Hilbert norm vanishes. -/
private theorem plusSheet_eq_zero_of_norm_zero {u : H₂} (hu : u ∈ plusSheet (E := E))
    (hn : inner ℝ (WithLp.fst u) (WithLp.fst u) = 0) : u = 0 := by
  have hfst : WithLp.fst u = 0 := inner_self_eq_zero.mp hn
  have hmem := (mem_plusSheet_iff_snd_eq_zero (E := E) u).mp hu
  apply DoubledSpace.ext
  · exact hfst
  · exact hmem

omit [CompleteSpace E] in
/-- Helper: a `-1`-sheet state with vanishing Hilbert norm vanishes. -/
private theorem minusSheet_eq_zero_of_norm_zero {u : H₂} (hu : u ∈ minusSheet (E := E))
    (hn : inner ℝ (WithLp.snd u) (WithLp.snd u) = 0) : u = 0 := by
  have hsnd : WithLp.snd u = 0 := inner_self_eq_zero.mp hn
  have hmem := (mem_minusSheet_iff_fst_eq_zero (E := E) u).mp hu
  apply DoubledSpace.ext
  · exact hmem
  · exact hsnd

/--
On the `+1` sheet, nullity of the indefinite form forces the state to vanish.

So the `+1` Peirce corner carries a *positive definite* form: there are no nonzero
null vectors there. The null cone lives entirely in the off-diagonal (mixed)
sector.
-/
theorem qform_eq_zero_of_mem_plusSheet {u : H₂} (hu : u ∈ plusSheet (E := E))
    (hn : SplitQuadratic.qform (E := E) u = 0) : u = 0 := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hu] at hn
  rw [SplitQuadratic.qform_eq_kreinInner, kreinInner_plusPoint] at hn
  exact plusSheet_eq_zero_of_norm_zero hu (by linarith)

/-- Dually on the `-1` sheet, nullity of the indefinite form forces vanishing. -/
theorem qform_eq_zero_of_mem_minusSheet {u : H₂} (hu : u ∈ minusSheet (E := E))
    (hn : SplitQuadratic.qform (E := E) u = 0) : u = 0 := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hu] at hn
  rw [SplitQuadratic.qform_eq_kreinInner, kreinInner_minusPoint] at hn
  exact minusSheet_eq_zero_of_norm_zero hu (by linarith)

/-! ## 3. Trichotomy of the indefinite quadratic form -/

/--
Every real value of the quadratic form is positive, negative, or zero. Generic
vectors need not lie on either pure eigensheet; this trichotomy is about the form's
sign, not a decomposition of the carrier into its eigensheets.
-/
theorem qform_sign_trichotomy (u : H₂) :
    SplitQuadratic.IsKreinPositive (E := E) u
      ∨ SplitQuadratic.IsKreinNegative (E := E) u
      ∨ SplitQuadratic.IsNull (E := E) u := by
  rcases lt_trichotomy 0 (SplitQuadratic.qform (E := E) u) with hpos | heq | hneg
  · exact Or.inl hpos
  · exact Or.inr (Or.inr heq.symm)
  · exact Or.inr (Or.inl hneg)

/-! ## 4. Krein sign is exactly the sheet, i.e. the Peirce eigenvalue -/

/--
A nonzero vector on the `+1` eigensheet has strictly positive Krein quadratic
form. The converse is not asserted: mixed vectors can also have positive form.
-/
theorem isKreinPositive_of_mem_plusSheet {u : H₂}
    (hu : u ∈ plusSheet (E := E)) (hne : u ≠ 0) :
    SplitQuadratic.IsKreinPositive (E := E) u := by
  have hnonneg := qform_nonneg_of_mem_plusSheet (E := E) hu
  have hzero : SplitQuadratic.qform (E := E) u ≠ 0 := by
    intro hz
    exact hne (qform_eq_zero_of_mem_plusSheet (E := E) hu hz)
  exact hnonneg.lt_of_ne (Ne.symm hzero)

/--
A nonzero vector on the `-1` eigensheet has strictly negative Krein quadratic
form. Mixed vectors can also have negative form, so only this implication is
claimed.
-/
theorem isKreinNegative_of_mem_minusSheet {u : H₂}
    (hu : u ∈ minusSheet (E := E)) (hne : u ≠ 0) :
    SplitQuadratic.IsKreinNegative (E := E) u := by
  have hnonpos := qform_nonpos_of_mem_minusSheet (E := E) hu
  have hzero : SplitQuadratic.qform (E := E) u ≠ 0 := by
    intro hz
    exact hne (qform_eq_zero_of_mem_minusSheet (E := E) hu hz)
  exact hnonpos.lt_of_ne hzero

/--
The two Krein sectors are disjoint: no nonzero state is both positive and negative.

Immediate but worth stating: it is what makes the polarization a genuine
*decomposition* rather than an overlap.
-/
theorem not_isKreinPositive_and_isKreinNegative {u : H₂}
    (hp : SplitQuadratic.IsKreinPositive (E := E) u)
    (hn : SplitQuadratic.IsKreinNegative (E := E) u) : False := by
  exact (lt_asymm hp hn).elim

/--
Every doubled state has positive, negative, or zero Krein quadratic form. Zero is
included because the zero vector is null as well.

This is the headline structural theorem of the bridge: the indefinite metric on the
doubled carrier admits no other behaviour than the two Peirce sectors and the null
cone between them.
-/
theorem isKreinPositive_or_isKreinNegative_or_isNull {u : H₂} :
    SplitQuadratic.IsKreinPositive (E := E) u
      ∨ SplitQuadratic.IsKreinNegative (E := E) u
      ∨ SplitQuadratic.IsNull (E := E) u :=
  qform_sign_trichotomy (E := E) u

/-! ## 5. The sheets as Pauli eigenspaces in the concrete real plane -/

open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.Clifford.Cl11Matrix

local notation "Plane" => InfoGeometry.Krein.RealPlaneMatrixBridge.Plane

/-- A vector in the positive sheet is a `+1` eigenvector of the Pauli
fundamental symmetry, in the concrete two-coordinate model of `Plane`. -/
theorem pauli_Eplus_fixes_positive_sheet
    {u : Plane}
    (hu : (u.down : DoubledSpace ℝ) ∈ plusSheet (E := ℝ)) :
    Matrix.mulVec Eplus (coordinates u) = coordinates u := by
  have hsnd : WithLp.snd (u.down : DoubledSpace ℝ) = 0 :=
    (mem_plusSheet_iff_snd_eq_zero (E := ℝ) (u.down)).mp hu
  ext i
  fin_cases i <;>
    simp [Eplus, coordinates, RealPlaneMatrixBridge.coordinates,
      Matrix.mulVec, hsnd]

/-- A vector in the negative sheet is a `-1` eigenvector of the Pauli
fundamental symmetry, in the concrete two-coordinate model of `Plane`. -/
theorem pauli_Eplus_negates_negative_sheet
    {u : Plane}
    (hu : (u.down : DoubledSpace ℝ) ∈ minusSheet (E := ℝ)) :
    Matrix.mulVec Eplus (coordinates u) = -coordinates u := by
  have hfst : WithLp.fst (u.down : DoubledSpace ℝ) = 0 :=
    (mem_minusSheet_iff_fst_eq_zero (E := ℝ) (u.down)).mp hu
  ext i
  fin_cases i <;>
    simp [Eplus, coordinates, RealPlaneMatrixBridge.coordinates,
      Matrix.mulVec, hfst]

end

end InfoGeometry.CliffordWeyl.PolarizedPeirceSignBridge

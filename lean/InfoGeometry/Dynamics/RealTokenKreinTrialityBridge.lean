import InfoGeometry.Dynamics.RealTokenPhaseChirality
import InfoGeometry.Exceptional.CompositionTriality

/-!
# Real doubled token carrier and split triality slots

The finite token carrier is first restricted to real scalars and then doubled.
The resulting split form is defined explicitly on the doubled coordinate
carrier; no positive-definite metric or unproved `KreinSpace` instance is
substituted for the indefinite form.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealTokenFlatCoordinates := ((V × Fin 2) × Fin 2) → ℝ

abbrev RealTokenDoubledSpace :=
  RealTokenFlatCoordinates (V := V) × RealTokenFlatCoordinates (V := V)

def realTokenSplitPairing :
    RealTokenDoubledSpace (V := V) → RealTokenDoubledSpace (V := V) → ℝ :=
  fun x y => (∑ i, x.1 i * y.1 i) - ∑ i, x.2 i * y.2 i

@[simp] theorem realTokenSplitPairing_zero_left
    (x : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing 0 x = 0 := by
  simp [realTokenSplitPairing]

@[simp] theorem realTokenSplitPairing_zero_right
    (x : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x 0 = 0 := by
  simp [realTokenSplitPairing]

theorem realTokenSplitPairing_swap
    (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x y = realTokenSplitPairing y x := by
  simp only [realTokenSplitPairing]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem realTokenSplitPairing_add_left
    (x y z : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing (x + y) z =
      realTokenSplitPairing x z + realTokenSplitPairing y z := by
  simp only [realTokenSplitPairing, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem realTokenSplitPairing_add_right
    (x y z : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x (y + z) =
      realTokenSplitPairing x y + realTokenSplitPairing x z := by
  calc
    realTokenSplitPairing x (y + z) = realTokenSplitPairing (y + z) x :=
      realTokenSplitPairing_swap _ _
    _ = realTokenSplitPairing y x + realTokenSplitPairing z x :=
      realTokenSplitPairing_add_left _ _ _
    _ = realTokenSplitPairing x y + realTokenSplitPairing x z := by
      rw [realTokenSplitPairing_swap y x, realTokenSplitPairing_swap z x]

theorem realTokenSplitPairing_neg_left
    (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing (-x) y = -realTokenSplitPairing x y := by
  simp only [realTokenSplitPairing, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply,
    neg_mul, Finset.sum_neg_distrib]
  ring

theorem realTokenSplitPairing_neg_right
    (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x (-y) = -realTokenSplitPairing x y := by
  rw [realTokenSplitPairing_swap, realTokenSplitPairing_neg_left,
    realTokenSplitPairing_swap]

theorem realTokenSplitPairing_smul_left
    (r : ℝ) (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing (r • x) y = r * realTokenSplitPairing x y := by
  simp [realTokenSplitPairing, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc, mul_sub]

theorem realTokenSplitPairing_smul_right
    (r : ℝ) (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x (r • y) = r * realTokenSplitPairing x y := by
  rw [realTokenSplitPairing_swap, realTokenSplitPairing_smul_left,
    realTokenSplitPairing_swap]

abbrev RealTokenSPlus := RealTokenFlatCoordinates (V := V)
abbrev RealTokenSMinus := RealTokenFlatCoordinates (V := V)
abbrev RealTokenVector := RealTokenFlatCoordinates (V := V)

noncomputable def realTokenFlatCoordinateOf
    (ψ : RealTokenHilbertSpace (V := V)) : RealTokenFlatCoordinates (V := V) :=
  fun i => if i.2 = 0 then Complex.re (ψ i.1) else Complex.im (ψ i.1)

@[simp] theorem realTokenFlatCoordinateOf_zero_component
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    realTokenFlatCoordinateOf ψ (i, 0) = Complex.re (ψ i) := by
  simp [realTokenFlatCoordinateOf]

@[simp] theorem realTokenFlatCoordinateOf_one_component
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    realTokenFlatCoordinateOf ψ (i, 1) = Complex.im (ψ i) := by
  simp [realTokenFlatCoordinateOf]

theorem realTokenFlatCoordinateOf_pair_readout
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    (realTokenFlatCoordinateOf ψ (i, 0),
      realTokenFlatCoordinateOf ψ (i, 1)) =
      (Complex.re (ψ i), Complex.im (ψ i)) := by
  simp

/-! A witness-gated triality interface on the three real token slots. -/
structure RealTokenTrialityDatum where
  mul : RealTokenSPlus (V := V) →ₗ[ℝ]
    RealTokenSMinus (V := V) →ₗ[ℝ] RealTokenVector (V := V)
  tPlus : RealTokenSPlus (V := V) →ₗ[ℝ] RealTokenSPlus (V := V)
  tMinus : RealTokenSMinus (V := V) →ₗ[ℝ] RealTokenSMinus (V := V)
  tVector : RealTokenVector (V := V) →ₗ[ℝ] RealTokenVector (V := V)
  triality : ∀ x y,
    tVector (mul x y) = mul (tPlus x) y + mul x (tMinus y)

theorem realTokenTrialityDatum_triality
    (T : RealTokenTrialityDatum (V := V))
    (x : RealTokenSPlus (V := V)) (y : RealTokenSMinus (V := V)) :
    T.tVector (T.mul x y) = T.mul (T.tPlus x) y + T.mul x (T.tMinus y) :=
  T.triality x y

noncomputable def realTokenPlusEmbedding :
    RealTokenFlatCoordinates (V := V) → RealTokenDoubledSpace (V := V) :=
  fun ψ => (ψ, 0)

noncomputable def realTokenMinusEmbedding :
    RealTokenFlatCoordinates (V := V) → RealTokenDoubledSpace (V := V) :=
  fun ψ => (0, ψ)

@[simp] theorem realTokenPlusEmbedding_eq_pair
    (ψ : RealTokenFlatCoordinates (V := V)) :
    realTokenPlusEmbedding ψ = (ψ, 0) := rfl

@[simp] theorem realTokenMinusEmbedding_eq_pair
    (ψ : RealTokenFlatCoordinates (V := V)) :
    realTokenMinusEmbedding ψ = (0, ψ) := rfl

theorem realTokenDoubled_decompose
    (x : RealTokenDoubledSpace (V := V)) :
    realTokenPlusEmbedding x.1 + realTokenMinusEmbedding x.2 = x := by
  rcases x with ⟨xplus, xminus⟩
  ext i <;> simp [realTokenPlusEmbedding, realTokenMinusEmbedding]

theorem realTokenSplitPairing_self
    (x : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x x =
      (∑ i, x.1 i * x.1 i) - ∑ i, x.2 i * x.2 i := rfl

theorem realTokenDoubled_krein_is_split_form
    (ψ φ : RealTokenFlatCoordinates (V := V)) :
    realTokenSplitPairing (realTokenPlusEmbedding ψ) (realTokenPlusEmbedding φ) =
      ∑ i, ψ i * φ i := by
  simp [realTokenSplitPairing, realTokenPlusEmbedding]

theorem realTokenDoubled_minus_is_split_form
    (ψ φ : RealTokenFlatCoordinates (V := V)) :
    realTokenSplitPairing (realTokenMinusEmbedding ψ) (realTokenMinusEmbedding φ) =
      -(∑ i, ψ i * φ i) := by
  simp [realTokenSplitPairing, realTokenMinusEmbedding]

theorem realTokenDoubled_plus_minus_null
    (ψ φ : RealTokenFlatCoordinates (V := V)) :
    realTokenSplitPairing (realTokenPlusEmbedding ψ) (realTokenMinusEmbedding φ) = 0 := by
  simp [realTokenSplitPairing, realTokenPlusEmbedding, realTokenMinusEmbedding]

theorem realTokenDoubled_minus_plus_null
    (ψ φ : RealTokenFlatCoordinates (V := V)) :
    realTokenSplitPairing (realTokenMinusEmbedding ψ) (realTokenPlusEmbedding φ) = 0 := by
  rw [realTokenSplitPairing_swap, realTokenDoubled_plus_minus_null]

theorem realTokenSplitPairing_decompose
    (x y : RealTokenDoubledSpace (V := V)) :
    realTokenSplitPairing x y =
      realTokenSplitPairing (realTokenPlusEmbedding x.1)
        (realTokenPlusEmbedding y.1) +
    realTokenSplitPairing (realTokenMinusEmbedding x.2)
        (realTokenMinusEmbedding y.2) := by
  simp [realTokenSplitPairing, realTokenPlusEmbedding,
    realTokenMinusEmbedding]
  ring

end
end InfoGeometry.Dynamics

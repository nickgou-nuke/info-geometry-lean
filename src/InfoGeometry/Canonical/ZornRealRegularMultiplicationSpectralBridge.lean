import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Regular multiplication on the explicit real Zorn carrier

This owner treats a Zorn element as a linear operator only through its regular
actions.  It records the quadratic operator law available on the explicit
coordinate carrier.  No associative matrix multiplication or generic Krein
spectral quartet is asserted here.
-/

namespace InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev Carrier := ZornCoord

noncomputable def discriminant (X : Carrier) : ℝ := zornTrace X ^ 2 - 4 * zornNorm X

def leftRegular (X : Carrier) : Carrier →ₗ[ℝ] Carrier where
  toFun := fun Y => zornMul X Y
  map_add' := by
    intro Y Z
    rcases X with ⟨a, b, x, y⟩
    rcases Y with ⟨c, d, u, v⟩
    rcases Z with ⟨e, f, r, s⟩
    ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;> ring
  map_smul' := by
    intro c Y
    rcases X with ⟨a, b, x, y⟩
    rcases Y with ⟨d, e, u, v⟩
    ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;> ring

@[simp] theorem leftRegular_apply (X Y : Carrier) :
    leftRegular X Y = zornMul X Y := rfl

noncomputable def centeredLeftRegular (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  leftRegular X - (zornTrace X / 2) • LinearMap.id

def rightRegular (X : Carrier) : Carrier →ₗ[ℝ] Carrier where
  toFun := fun Y => zornMul Y X
  map_add' := by
    intro Y Z
    rcases X with ⟨a, b, x, y⟩
    rcases Y with ⟨c, d, u, v⟩
    rcases Z with ⟨e, f, r, s⟩
    ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;> ring
  map_smul' := by
    intro c Y
    rcases X with ⟨a, b, x, y⟩
    rcases Y with ⟨d, e, u, v⟩
    ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;> ring

@[simp] theorem rightRegular_apply (X Y : Carrier) :
    rightRegular X Y = zornMul Y X := rfl

/-! The right-regular action has the same native quadratic envelope. -/

theorem zornMul_right_alternative (X Y : Carrier) :
    zornMul (zornMul Y X) X = zornMul Y (zornMul X X) := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext <;>
    simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;>
    ring

theorem zornMul_add_right (X Y Z : Carrier) :
    zornMul X (Y + Z) = zornMul X Y + zornMul X Z := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  rcases Z with ⟨e, f, r, s⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_sub_right (X Y Z : Carrier) :
    zornMul X (Y - Z) = zornMul X Y - zornMul X Z := by
  rw [sub_eq_add_neg, zornMul_add_right]
  rcases X with ⟨a, b, x, y⟩
  rcases Z with ⟨c, d, u, v⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_smul_right (r : ℝ) (X Y : Carrier) :
    zornMul X (r • Y) = r • zornMul X Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_scalarZorn_right (r : ℝ) (Y : Carrier) :
    zornMul Y (scalarZorn r) = r • Y := by
  rcases Y with ⟨a, b, x, y⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · dsimp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]; ring
  · dsimp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]; ring
  · ext i; fin_cases i <;> simp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]
  · ext i; fin_cases i <;> simp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]

theorem zornMul_one_right (Y : Carrier) :
    zornMul Y zornOne = Y := by
  simpa [zornOne_eq_scalarZorn_one] using zornMul_scalarZorn_right 1 Y

theorem zornMul_zero_right (Y : Carrier) :
    zornMul Y 0 = 0 := by
  rcases Y with ⟨a, b, x, y⟩
  simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]
theorem rightRegular_quadratic (X Y : Carrier) :
    rightRegular X (rightRegular X Y) -
        zornTrace X • rightRegular X Y +
        zornNorm X • Y = 0 := by
  rw [rightRegular_apply, rightRegular_apply, zornMul_right_alternative]
  have h := zornMul_self_quadratic_rank X
  change zornMul Y (zornMul X X) -
      zornTrace X • zornMul Y X + zornNorm X • Y = 0
  calc
    zornMul Y (zornMul X X) -
          zornTrace X • zornMul Y X + zornNorm X • Y =
        zornMul Y
          (zornMul X X - zornTrace X • X + zornNorm X • zornOne) := by
      rw [zornMul_add_right, zornMul_sub_right,
        zornMul_smul_right, zornMul_smul_right,
        zornMul_one_right]
    _ = 0 := by
      rw [h]
      exact zornMul_zero_right Y

theorem rightRegular_trace_zero_norm_zero (X : Carrier)
    (htrace : zornTrace X = 0) (hnorm : zornNorm X = 0) :
    rightRegular X ∘ₗ rightRegular X = 0 := by
  apply LinearMap.ext
  intro Y
  have h := rightRegular_quadratic X Y
  simpa [htrace, hnorm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

theorem rightRegular_trace_zero_square (X : Carrier)
    (htrace : zornTrace X = 0) :
    rightRegular X ∘ₗ rightRegular X =
      (-zornNorm X) • LinearMap.id := by
  apply LinearMap.ext
  intro Y
  have h := rightRegular_quadratic X Y
  have h' : rightRegular X (rightRegular X Y) + zornNorm X • Y = 0 := by
    simpa [htrace, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have h'' := eq_neg_of_add_eq_zero_left h'
  simpa [smul_neg] using h''

noncomputable def centeredRightRegular (X : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  rightRegular X - (zornTrace X / 2) • LinearMap.id

theorem centeredRightRegular_square (X : Carrier) :
    centeredRightRegular X ∘ₗ centeredRightRegular X =
      (discriminant X / 4) • LinearMap.id := by
  apply LinearMap.ext
  intro Y
  have h := rightRegular_quadratic X Y
  simp only [centeredRightRegular, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply]
  have h_exp : rightRegular X (rightRegular X Y - (zornTrace X / 2) • Y) -
      (zornTrace X / 2) • (rightRegular X Y - (zornTrace X / 2) • Y) =
      (rightRegular X (rightRegular X Y) - zornTrace X • (rightRegular X Y)) +
      ((zornTrace X / 2) ^ 2) • Y := by
    rw [map_sub, map_smul, smul_sub]
    have h_mid : (zornTrace X / 2) • rightRegular X Y +
        (zornTrace X / 2) • rightRegular X Y = zornTrace X • rightRegular X Y := by
      rw [← add_smul]
      have : zornTrace X / 2 + zornTrace X / 2 = zornTrace X := by ring
      rw [this]
    have h_sq : (zornTrace X / 2) • ((zornTrace X / 2) • Y) =
        ((zornTrace X / 2) ^ 2) • Y := by
      rw [smul_smul, pow_two]
    rw [h_sq]
    calc
      rightRegular X (rightRegular X Y) - (zornTrace X / 2) • rightRegular X Y -
          ((zornTrace X / 2) • rightRegular X Y - ((zornTrace X / 2) ^ 2) • Y) =
        (rightRegular X (rightRegular X Y) -
          ((zornTrace X / 2) • rightRegular X Y +
            (zornTrace X / 2) • rightRegular X Y)) +
          ((zornTrace X / 2) ^ 2) • Y := by abel
      _ = (rightRegular X (rightRegular X Y) - zornTrace X • rightRegular X Y) +
          ((zornTrace X / 2) ^ 2) • Y := by rw [h_mid]
  rw [h_exp]
  have h_left : rightRegular X (rightRegular X Y) - zornTrace X • rightRegular X Y =
      - (zornNorm X • Y) := by
    calc
      rightRegular X (rightRegular X Y) - zornTrace X • rightRegular X Y =
          (rightRegular X (rightRegular X Y) - zornTrace X • rightRegular X Y +
            zornNorm X • Y) - zornNorm X • Y := by abel
      _ = 0 - zornNorm X • Y := by rw [h]
      _ = - (zornNorm X • Y) := by abel
  rw [h_left]
  dsimp [discriminant]
  have h_coef : - zornNorm X + (zornTrace X / 2) ^ 2 =
      (zornTrace X ^ 2 - 4 * zornNorm X) / 4 := by ring
  calc
    -(zornNorm X • Y) + ((zornTrace X / 2) ^ 2) • Y =
        (-zornNorm X) • Y + ((zornTrace X / 2) ^ 2) • Y := by rw [neg_smul]
    _ = (-zornNorm X + (zornTrace X / 2) ^ 2) • Y := by rw [← add_smul]
    _ = ((zornTrace X ^ 2 - 4 * zornNorm X) / 4) • Y := by rw [h_coef]

/-! The repeated-left associator vanishes on the explicit Zorn product. -/
theorem zornMul_left_alternative (X Y : Carrier) :
    zornMul X (zornMul X Y) = zornMul (zornMul X X) Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext <;>
    simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
      cross3] <;>
    ring

theorem zornMul_add_left (X Y Z : Carrier) :
    zornMul (X + Y) Z = zornMul X Z + zornMul Y Z := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  rcases Z with ⟨e, f, r, s⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_sub_left (X Y Z : Carrier) :
    zornMul (X - Y) Z = zornMul X Z - zornMul Y Z := by
  rw [sub_eq_add_neg, zornMul_add_left]
  rcases Y with ⟨a, b, x, y⟩
  rcases Z with ⟨c, d, u, v⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_smul_left (r : ℝ) (X Y : Carrier) :
    zornMul (r • X) Y = r • zornMul X Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases Y with ⟨c, d, u, v⟩
  ext <;> simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3,
    cross3] <;> ring

theorem zornMul_scalarZorn_left (r : ℝ) (Y : Carrier) :
    zornMul (scalarZorn r) Y = r • Y := by
  rcases Y with ⟨a, b, x, y⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · dsimp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]; ring
  · dsimp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]; ring
  · ext i; fin_cases i <;> simp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]
  · ext i; fin_cases i <;> simp [scalarZorn, zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]

theorem zornMul_one_left (Y : Carrier) :
    zornMul zornOne Y = Y := by
  simpa [zornOne_eq_scalarZorn_one] using zornMul_scalarZorn_left 1 Y

theorem zornMul_zero_left (Y : Carrier) :
    zornMul 0 Y = 0 := by
  rcases Y with ⟨a, b, x, y⟩
  simp [zornMul, zornA, zornB, zornX, zornY, zornMk, dot3, cross3]

/-! The scalar quadratic identity is the native coordinate rank identity. -/
theorem leftRegular_quadratic (X Y : Carrier) :
    leftRegular X (leftRegular X Y) -
        zornTrace X • leftRegular X Y +
        zornNorm X • Y = 0 := by
  rw [leftRegular_apply, leftRegular_apply, zornMul_left_alternative]
  have h := zornMul_self_quadratic_rank X
  change zornMul (zornMul X X) Y -
      zornTrace X • zornMul X Y + zornNorm X • Y = 0
  calc
    zornMul (zornMul X X) Y -
          zornTrace X • zornMul X Y + zornNorm X • Y =
        zornMul
          (zornMul X X - zornTrace X • X + zornNorm X • zornOne) Y := by
      rw [zornMul_add_left, zornMul_sub_left,
        zornMul_smul_left, zornMul_smul_left,
        zornMul_one_left]
    _ = 0 := by
      rw [h]
      exact zornMul_zero_left Y

/-! Trace-zero slices expose the three norm-controlled operator regimes. -/
theorem leftRegular_trace_zero_norm_zero (X : Carrier)
    (htrace : zornTrace X = 0) (hnorm : zornNorm X = 0) :
    leftRegular X ∘ₗ leftRegular X = 0 := by
  apply LinearMap.ext
  intro Y
  have h := leftRegular_quadratic X Y
  simpa [htrace, hnorm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

theorem leftRegular_trace_zero_square (X : Carrier) (htrace : zornTrace X = 0) :
    leftRegular X ∘ₗ leftRegular X =
      (-zornNorm X) • LinearMap.id := by
  apply LinearMap.ext
  intro Y
  have h := leftRegular_quadratic X Y
  have h' : leftRegular X (leftRegular X Y) + zornNorm X • Y = 0 := by
    simpa [htrace, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have h'' := eq_neg_of_add_eq_zero_left h'
  simpa [smul_neg] using h''

theorem centeredLeftRegular_square (X : Carrier) :
    centeredLeftRegular X ∘ₗ centeredLeftRegular X =
      (discriminant X / 4) • LinearMap.id := by
  apply LinearMap.ext
  intro Y
  have h := leftRegular_quadratic X Y
  simp only [centeredLeftRegular, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply]
  have h_exp : leftRegular X (leftRegular X Y - (zornTrace X / 2) • Y) -
      (zornTrace X / 2) • (leftRegular X Y - (zornTrace X / 2) • Y) =
      (leftRegular X (leftRegular X Y) - zornTrace X • (leftRegular X Y)) +
      ((zornTrace X / 2) ^ 2) • Y := by
    rw [map_sub, map_smul, smul_sub]
    have h_mid : (zornTrace X / 2) • leftRegular X Y + (zornTrace X / 2) • leftRegular X Y =
        zornTrace X • leftRegular X Y := by
      rw [← add_smul]
      have : zornTrace X / 2 + zornTrace X / 2 = zornTrace X := by ring
      rw [this]
    have h_sq : (zornTrace X / 2) • ((zornTrace X / 2) • Y) = ((zornTrace X / 2) ^ 2) • Y := by
      rw [smul_smul, pow_two]
    rw [h_sq]
    calc
      leftRegular X (leftRegular X Y) - (zornTrace X / 2) • leftRegular X Y -
          ((zornTrace X / 2) • leftRegular X Y - ((zornTrace X / 2) ^ 2) • Y) =
        (leftRegular X (leftRegular X Y) - ((zornTrace X / 2) • leftRegular X Y + (zornTrace X / 2) • leftRegular X Y)) +
          ((zornTrace X / 2) ^ 2) • Y := by abel
      _ = (leftRegular X (leftRegular X Y) - zornTrace X • leftRegular X Y) + ((zornTrace X / 2) ^ 2) • Y := by rw [h_mid]
  rw [h_exp]
  have h_left : leftRegular X (leftRegular X Y) - zornTrace X • leftRegular X Y = - (zornNorm X • Y) := by
    calc
      leftRegular X (leftRegular X Y) - zornTrace X • leftRegular X Y =
          (leftRegular X (leftRegular X Y) - zornTrace X • leftRegular X Y + zornNorm X • Y) - zornNorm X • Y := by abel
      _ = 0 - zornNorm X • Y := by rw [h]
      _ = - (zornNorm X • Y) := by abel
  rw [h_left]
  dsimp [discriminant]
  have h_coef : - zornNorm X + (zornTrace X / 2) ^ 2 = (zornTrace X ^ 2 - 4 * zornNorm X) / 4 := by ring
  calc
    -(zornNorm X • Y) + ((zornTrace X / 2) ^ 2) • Y = (- zornNorm X) • Y + ((zornTrace X / 2) ^ 2) • Y := by rw [neg_smul]
    _ = (- zornNorm X + (zornTrace X / 2) ^ 2) • Y := by rw [← add_smul]
    _ = ((zornTrace X ^ 2 - 4 * zornNorm X) / 4) • Y := by rw [h_coef]

/-! Idempotent Zorn elements induce genuine projection operators through both
regular actions.  This is the concrete Peirce seed; no eigenspace
identification is asserted here. -/

theorem leftRegular_idempotent_of_mul_self (X : Carrier)
    (hX : zornMul X X = X) :
    leftRegular X ∘ₗ leftRegular X = leftRegular X := by
  apply LinearMap.ext
  intro Y
  change zornMul X (zornMul X Y) = zornMul X Y
  rw [zornMul_left_alternative, hX]

theorem rightRegular_idempotent_of_mul_self (X : Carrier)
    (hX : zornMul X X = X) :
    rightRegular X ∘ₗ rightRegular X = rightRegular X := by
  apply LinearMap.ext
  intro Y
  change zornMul (zornMul Y X) X = zornMul Y X
  rw [zornMul_right_alternative, hX]

theorem zornMul_pPlus_self : zornMul pPlus pPlus = pPlus := by
  ext <;>
    simp [pPlus, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3,
      cross3]
  · rename_i i
    fin_cases i <;> simp
  · rename_i i
    fin_cases i <;> simp

theorem zornMul_pMinus_self : zornMul pMinus pMinus = pMinus := by
  ext <;>
    simp [pMinus, zornMul, zornMk, zornA, zornB, zornX, zornY, dot3,
      cross3]
  · rename_i i
    fin_cases i <;> simp
  · rename_i i
    fin_cases i <;> simp

theorem leftRegular_pPlus_idempotent :
    leftRegular pPlus ∘ₗ leftRegular pPlus = leftRegular pPlus := by
  exact leftRegular_idempotent_of_mul_self pPlus zornMul_pPlus_self

theorem rightRegular_pPlus_idempotent :
    rightRegular pPlus ∘ₗ rightRegular pPlus = rightRegular pPlus := by
  exact rightRegular_idempotent_of_mul_self pPlus zornMul_pPlus_self

theorem leftRegular_pMinus_idempotent :
    leftRegular pMinus ∘ₗ leftRegular pMinus = leftRegular pMinus := by
  exact leftRegular_idempotent_of_mul_self pMinus zornMul_pMinus_self

theorem rightRegular_pMinus_idempotent :
    rightRegular pMinus ∘ₗ rightRegular pMinus = rightRegular pMinus := by
  exact rightRegular_idempotent_of_mul_self pMinus zornMul_pMinus_self

end InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge

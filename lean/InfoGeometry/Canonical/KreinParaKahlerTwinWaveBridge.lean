import Mathlib
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.HestenesKreinResolventColimit

/-!
# Krein--para-Kaehler twin-wave bridge

This module fixes the sign convention for the real two-channel carrier and
connects it to the repository-native doubled Krein space.

For a coordinate pair u = (x,y), use

  L(x,y) = (-x,y),
  K(x,y) = (y,x),
  J(x,y) = (-y,x).

Thus L = -sigma_z, K = sigma_x, and J = -i sigma_y in the convention of the
source note. The repository owner DoubledSpace uses spectral_epsilon =
sigma_z, hence L is minus spectral_epsilon.

The exact products are

  J K = L,   K J = -L,
  K L = -J,  L K = J,
  L J = K,   J L = -K.

Consequently, for the Krein form [u,v]_L = u^T L v and
omega(u,v) = u^T J v,

  omega(u,v) = [u,Kv]_L = -[Ku,v]_L.

The conventional Wronskian x dy - y dx is minus omega(u,du) with this J.
Transversality of the null cone is proved only from an explicit nonzero
Wronskian premise. Positivity of the Wronskian, nonvanishing of a paired Xi
state, and statements about Riemann zeros are not asserted here.
-/

namespace InfoGeometry.Canonical.KreinParaKahlerTwinWaveBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesKreinResolventColimit

/-- Concrete real cosine/current coordinate carrier. -/
abbrev PairState := ℝ × ℝ

/-- The source convention L = -sigma_z. -/
def kreinSign (u : PairState) : PairState :=
  (-u.1, u.2)

/-- The para-complex branch swap K = sigma_x. -/
def paraSwap (u : PairState) : PairState :=
  (u.2, u.1)

/-- The symplectic complex structure J = -i sigma_y. -/
def symplecticComplex (u : PairState) : PairState :=
  (-u.2, u.1)

@[simp] theorem kreinSign_sq (u : PairState) :
    kreinSign (kreinSign u) = u := by
  rcases u with ⟨x, y⟩
  simp [kreinSign]

@[simp] theorem paraSwap_sq (u : PairState) :
    paraSwap (paraSwap u) = u := by
  rcases u with ⟨x, y⟩
  simp [kreinSign, symplecticComplex, paraSwap]

@[simp] theorem symplecticComplex_sq (u : PairState) :
    symplecticComplex (symplecticComplex u) = -u := by
  rcases u with ⟨x, y⟩
  simp [symplecticComplex]

theorem symplecticComplex_paraSwap (u : PairState) :
    symplecticComplex (paraSwap u) = kreinSign u := by
  rcases u with ⟨x, y⟩
  rfl

theorem paraSwap_symplecticComplex (u : PairState) :
    paraSwap (symplecticComplex u) = -kreinSign u := by
  rcases u with ⟨x, y⟩
  simp [paraSwap, symplecticComplex, kreinSign]

theorem paraSwap_kreinSign (u : PairState) :
    paraSwap (kreinSign u) = -symplecticComplex u := by
  rcases u with ⟨x, y⟩
  simp [paraSwap, symplecticComplex, kreinSign]

theorem kreinSign_paraSwap (u : PairState) :
    kreinSign (paraSwap u) = symplecticComplex u := by
  rcases u with ⟨x, y⟩
  rfl

theorem kreinSign_symplecticComplex (u : PairState) :
    kreinSign (symplecticComplex u) = paraSwap u := by
  rcases u with ⟨x, y⟩
  simp [kreinSign, symplecticComplex, paraSwap]

theorem symplecticComplex_kreinSign (u : PairState) :
    symplecticComplex (kreinSign u) = -paraSwap u := by
  rcases u with ⟨x, y⟩
  simp [paraSwap, symplecticComplex, kreinSign]

/-! ## Identification with the native doubled Krein carrier -/

/-- Coordinate inclusion into the one-dimensional doubled Hilbert carrier. -/
noncomputable def toDoubled (u : PairState) : DoubledSpace ℝ :=
  to_doubled u.1 u.2

theorem toDoubled_paraSwap (u : PairState) :
    toDoubled (paraSwap u) =
      modular_j (E := ℝ) (toDoubled u) := by
  rcases u with ⟨x, y⟩
  simp [toDoubled, paraSwap]

theorem toDoubled_kreinSign (u : PairState) :
    toDoubled (kreinSign u) =
      -(spectral_epsilon (E := ℝ) (toDoubled u)) := by
  rcases u with ⟨x, y⟩
  apply DoubledSpace.ext <;>
    simp [toDoubled, kreinSign, spectral_epsilon]

theorem toDoubled_symplecticComplex (u : PairState) :
    toDoubled (symplecticComplex u) =
      complex_i (E := ℝ) (toDoubled u) := by
  rcases u with ⟨x, y⟩
  simp [toDoubled, symplecticComplex]

/-! ## Bilinear forms and the corrected binding identity -/

def hilbertPairing (u v : PairState) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def kreinPairing (u v : PairState) : ℝ :=
  hilbertPairing u (kreinSign v)

def symplecticPairing (u v : PairState) : ℝ :=
  hilbertPairing u (symplecticComplex v)

theorem kreinPairing_eq (u v : PairState) :
    kreinPairing u v = -u.1 * v.1 + u.2 * v.2 := by
  simp [kreinPairing, hilbertPairing, kreinSign]

theorem symplecticPairing_eq (u v : PairState) :
    symplecticPairing u v = -u.1 * v.2 + u.2 * v.1 := by
  simp [symplecticPairing, hilbertPairing, symplecticComplex]

theorem symplecticPairing_skew (u v : PairState) :
    symplecticPairing u v = -symplecticPairing v u := by
  rw [symplecticPairing_eq, symplecticPairing_eq]
  ring

@[simp] theorem symplecticPairing_self (u : PairState) :
    symplecticPairing u u = 0 := by
  rw [symplecticPairing_eq]
  ring

/-- Correct right-polarization identity: omega(u,v) = [u,Kv]_L. -/
theorem symplectic_eq_krein_right_paraSwap (u v : PairState) :
    symplecticPairing u v = kreinPairing u (paraSwap v) := by
  rw [symplecticPairing_eq, kreinPairing_eq]
  simp [paraSwap]

/-- Moving K to the first slot introduces the required minus sign. -/
theorem krein_left_paraSwap_eq_neg_symplectic (u v : PairState) :
    kreinPairing (paraSwap u) v = -symplecticPairing u v := by
  rw [kreinPairing_eq, symplecticPairing_eq]
  simp [paraSwap]

theorem master_binding_identity (u v : PairState) :
    symplecticPairing u v = kreinPairing u (paraSwap v) ∧
      kreinPairing (paraSwap u) v = -symplecticPairing u v :=
  ⟨symplectic_eq_krein_right_paraSwap u v,
    krein_left_paraSwap_eq_neg_symplectic u v⟩

/-! ## Quadratic readouts and null-cone transversality -/

def kreinQuadratic (u : PairState) : ℝ :=
  kreinPairing u u

def hilbertQuadratic (u : PairState) : ℝ :=
  hilbertPairing u u

def paraPolarization (u : PairState) : ℝ :=
  hilbertPairing u (paraSwap u)

def wronskian (u du : PairState) : ℝ :=
  u.1 * du.2 - u.2 * du.1

def kreinRate (u du : PairState) : ℝ :=
  -2 * u.1 * du.1 + 2 * u.2 * du.2

theorem kreinQuadratic_eq (u : PairState) :
    kreinQuadratic u = -u.1 ^ 2 + u.2 ^ 2 := by
  rw [kreinQuadratic, kreinPairing_eq]
  ring

theorem hilbertQuadratic_eq (u : PairState) :
    hilbertQuadratic u = u.1 ^ 2 + u.2 ^ 2 := by
  simp [hilbertQuadratic, hilbertPairing]
  ring

theorem paraPolarization_eq (u : PairState) :
    paraPolarization u = 2 * u.1 * u.2 := by
  simp [paraPolarization, hilbertPairing, paraSwap]
  ring

/-- With J = -i sigma_y, the conventional Wronskian is -omega(u,du). -/
theorem symplecticPairing_eq_neg_wronskian (u du : PairState) :
    symplecticPairing u du = -wronskian u du := by
  rw [symplecticPairing_eq]
  simp [wronskian]
  ring

theorem cosine_dominant_is_krein_negative
    (u : PairState) (h : u.2 ^ 2 < u.1 ^ 2) :
    kreinQuadratic u < 0 := by
  rw [kreinQuadratic_eq]
  linarith

theorem sine_dominant_is_krein_positive
    (u : PairState) (h : u.1 ^ 2 < u.2 ^ 2) :
    0 < kreinQuadratic u := by
  rw [kreinQuadratic_eq]
  linarith

theorem cosine_zero_is_krein_positive
    (y : ℝ) (hy : y ≠ 0) :
    0 < kreinQuadratic (0, y) := by
  rw [kreinQuadratic_eq]
  simp
  exact sq_pos_of_ne_zero hy

/--
A nonzero Wronskian forces a nonzero derivative of the Krein quadratic form at
a null state. This is the exact conditional transversality statement.
-/
theorem null_wronskian_nonzero_implies_kreinRate_ne_zero
    (u du : PairState)
    (hnull : kreinQuadratic u = 0)
    (hW : wronskian u du ≠ 0) :
    kreinRate u du ≠ 0 := by
  intro hrate
  apply hW
  rcases u with ⟨x, y⟩
  rcases du with ⟨dx, dy⟩
  simp only [kreinQuadratic_eq, Prod.fst, Prod.snd] at hnull
  simp only [kreinRate, Prod.fst, Prod.snd] at hrate
  simp only [wronskian, Prod.fst, Prod.snd]
  have hfactor : (y - x) * (y + x) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have hyx : y = x := by linarith
    subst y
    nlinarith
  · have hyx : y = -x := by linarith
    subst y
    nlinarith

theorem null_positive_wronskian_implies_transverse
    (u du : PairState)
    (hnull : kreinQuadratic u = 0)
    (hW : 0 < wronskian u du) :
    kreinRate u du ≠ 0 :=
  null_wronskian_nonzero_implies_kreinRate_ne_zero u du hnull (ne_of_gt hW)

/-- The algebraic rate is the derivative of the split quadratic trajectory. -/
theorem hasDerivAt_kreinQuadratic_trajectory
    (x y : ℝ → ℝ) (t dx dy : ℝ)
    (hx : HasDerivAt x dx t) (hy : HasDerivAt y dy t) :
    HasDerivAt
      (fun s => kreinQuadratic (x s, y s))
      (kreinRate (x t, y t) (dx, dy)) t := by
  have hxx := hx.mul hx
  have hyy := hy.mul hy
  convert hyy.sub hxx using 1
  · funext s
    simp only [kreinQuadratic_eq, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [kreinRate, Prod.fst, Prod.snd]
    ring

/-! ## Existing pointwise twin-wave parity packet -/

noncomputable def pairedTwinMode (t spectral : ℝ) : PairState :=
  (twinEven t spectral, twinOdd t spectral)

theorem pairedTwinMode_eq_two_cos_sin (t spectral : ℝ) :
    pairedTwinMode t spectral =
      (2 * Real.cos (t * spectral), 2 * Real.sin (t * spectral)) := by
  simp [pairedTwinMode, twinEven_eq_two_cos, twinOdd_eq_two_sin]

theorem pairedTwinMode_zero (spectral : ℝ) :
    pairedTwinMode 0 spectral = (2, 0) := by
  simp [pairedTwinMode, twinEven_zero, twinOdd_zero]

end InfoGeometry.Canonical.KreinParaKahlerTwinWaveBridge

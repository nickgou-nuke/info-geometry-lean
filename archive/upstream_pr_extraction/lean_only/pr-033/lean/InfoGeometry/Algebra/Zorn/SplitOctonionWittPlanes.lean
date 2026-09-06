import InfoGeometry.Algebra.Zorn.SplitQuaternionCore
import InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1500000

/-!
# Witt planes in the real split-octonion carrier

Complementary coordinate owner for the decomposition

`O_s = H ⊕ l H` and `(4,4) = (1,1)⁴`.

This file deliberately adds a theorem surface to the existing canonical Zorn
carrier.  It does not replace the Zorn multiplication or the split-quaternion
core.  The four quaternion directions are represented by the scalar direction
and the three standard imaginary coordinate directions; `l` supplies the
opposite-sign partner in each plane.
-/

namespace InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
open InfoGeometry.Canonical.ZornMatrix

abbrev CZ := CanonicalZorn

def jUnit : CZ :=
  { a := 0, b := 0, x := ![0, 1, 0], y := ![0, -1, 0] }

def kQuaternionUnit : CZ :=
  { a := 0, b := 0, x := ![0, 0, 1], y := ![0, 0, -1] }

def quaternionBasis : Fin 4 → CZ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => iUnit
  | ⟨2, _⟩ => jUnit
  | ⟨3, _⟩ => kQuaternionUnit
  | _ => 1

def ellBasis (a : Fin 4) : CZ :=
  zMul lUnit (quaternionBasis a)

noncomputable def chiralNull (a : Fin 4) (ε : ℝ) : CZ :=
  (1 / 2 : ℝ) • (quaternionBasis a + ε • ellBasis a)

@[simp] theorem j_sq : zMul jUnit jUnit = -1 := by
  ext i <;>
    simp [jUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

@[simp] theorem kQuaternion_sq :
    zMul kQuaternionUnit kQuaternionUnit = -1 := by
  ext i <;>
    simp [kQuaternionUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem ell_basis_left_square (a : Fin 4) :
    zMul lUnit (ellBasis a) = quaternionBasis a := by
  fin_cases a <;>
    ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
        zMul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

/-! The `i` split plane and its null basis.  These are finite algebraic
coordinates on the existing Zorn carrier; no loxodromic commutation claim is
made here. -/

def splitPlaneI (a b : ℝ) : CZ :=
  a • quaternionBasis 1 + b • ellBasis 1

theorem i_ell_i_anticommute :
    zMul (quaternionBasis 1) (ellBasis 1) +
        zMul (ellBasis 1) (quaternionBasis 1) = 0 := by
  ext i <;>
    simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem splitPlaneI_sq (a b : ℝ) :
    zMul (splitPlaneI a b) (splitPlaneI a b) =
      (b ^ 2 - a ^ 2) • (1 : CZ) := by
  have hEll : zMul (ellBasis 1) (ellBasis 1) = (1 : CZ) := by
    ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals fin_cases i <;> norm_num
  simp only [splitPlaneI, zMul_add_left, zMul_add_right, zMul_smul_left,
    zMul_smul_right]
  change a • (a • zMul iUnit iUnit + b • zMul (ellBasis 1) iUnit) +
    b • (a • zMul iUnit (ellBasis 1) + b • zMul (ellBasis 1) (ellBasis 1)) =
      (b ^ 2 - a ^ 2) • (1 : CZ)
  have hcross : zMul (ellBasis 1) iUnit = -zMul iUnit (ellBasis 1) := by
    ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
  rw [i_sq, hEll, hcross]
  module

theorem splitPlaneI_sq_eq_neg_splitPlaneQuadratic (a b : ℝ) :
    zMul (splitPlaneI a b) (splitPlaneI a b) =
      (-splitPlaneQuadratic a b) • (1 : CZ) := by
  rw [splitPlaneI_sq]
  simp [splitPlaneQuadratic]

/-! The three imaginary quaternion directions carry the same split-plane
quadratic law.  The scalar direction is intentionally excluded: its two
coordinate generators are idempotent rather than square-zero. -/

def imaginarySplitPlane (a : Fin 3) (x y : ℝ) : CZ :=
  x • quaternionBasis a.succ + y • ellBasis a.succ

noncomputable def imaginarySplitPlaneNullPlus (a : Fin 3) : CZ :=
  (1 / 2 : ℝ) • (quaternionBasis a.succ + ellBasis a.succ)

noncomputable def imaginarySplitPlaneNullMinus (a : Fin 3) : CZ :=
  (1 / 2 : ℝ) • (quaternionBasis a.succ - ellBasis a.succ)

theorem imaginarySplitPlane_sq (a : Fin 3) (x y : ℝ) :
    zMul (imaginarySplitPlane a x y) (imaginarySplitPlane a x y) =
      (y ^ 2 - x ^ 2) • (1 : CZ) := by
  have hQ : ∀ a : Fin 3,
      zMul (quaternionBasis a.succ) (quaternionBasis a.succ) = -1 := by
    intro a
    fin_cases a
    · exact i_sq
    · exact j_sq
    · exact kQuaternion_sq
  have hE : ∀ a : Fin 3,
      zMul (ellBasis a.succ) (ellBasis a.succ) = 1 := by
    intro a
    fin_cases a <;>
      ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
        zMul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals fin_cases i <;> norm_num
  have hC : ∀ a : Fin 3,
      zMul (ellBasis a.succ) (quaternionBasis a.succ) =
        -zMul (quaternionBasis a.succ) (ellBasis a.succ) := by
    intro a
    fin_cases a <;>
      ext i <;>
      simp [ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
        zMul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
  simp only [imaginarySplitPlane, zMul_add_left, zMul_add_right,
    zMul_smul_left, zMul_smul_right]
  change x • (x • zMul (quaternionBasis a.succ) (quaternionBasis a.succ) +
      y • zMul (ellBasis a.succ) (quaternionBasis a.succ)) +
    y • (x • zMul (quaternionBasis a.succ) (ellBasis a.succ) +
      y • zMul (ellBasis a.succ) (ellBasis a.succ)) =
    (y ^ 2 - x ^ 2) • (1 : CZ)
  rw [hQ a, hE a, hC a]
  module

theorem imaginarySplitPlane_sq_eq_splitPlaneQuadratic
    (a : Fin 3) (x y : ℝ) :
    zMul (imaginarySplitPlane a x y) (imaginarySplitPlane a x y) =
      splitPlaneQuadratic y x • (1 : CZ) := by
  rw [imaginarySplitPlane_sq]
  simp [splitPlaneQuadratic]

theorem imaginarySplitPlaneNullPlus_sq (a : Fin 3) :
    zMul (imaginarySplitPlaneNullPlus a)
      (imaginarySplitPlaneNullPlus a) = 0 := by
  rw [imaginarySplitPlaneNullPlus, zMul_smul_left, zMul_smul_right]
  have hEq : quaternionBasis a.succ + ellBasis a.succ =
      imaginarySplitPlane a 1 1 := by
    simp [imaginarySplitPlane]
  rw [hEq, imaginarySplitPlane_sq]
  norm_num

theorem imaginarySplitPlaneNullMinus_sq (a : Fin 3) :
    zMul (imaginarySplitPlaneNullMinus a)
      (imaginarySplitPlaneNullMinus a) = 0 := by
  rw [imaginarySplitPlaneNullMinus, zMul_smul_left, zMul_smul_right]
  have hEq : quaternionBasis a.succ - ellBasis a.succ =
      imaginarySplitPlane a 1 (-1) := by
    simp [imaginarySplitPlane, sub_eq_add_neg]
  rw [hEq, imaginarySplitPlane_sq]
  norm_num

theorem imaginarySplitPlane_reconstruct (a : Fin 3) (x y : ℝ) :
    imaginarySplitPlane a x y =
      (x + y) • imaginarySplitPlaneNullPlus a +
        (x - y) • imaginarySplitPlaneNullMinus a := by
  unfold imaginarySplitPlane imaginarySplitPlaneNullPlus
    imaginarySplitPlaneNullMinus
  module

theorem imaginarySplitPlaneNullPlus_add_minus (a : Fin 3) :
    imaginarySplitPlaneNullPlus a + imaginarySplitPlaneNullMinus a =
      quaternionBasis a.succ := by
  unfold imaginarySplitPlaneNullPlus imaginarySplitPlaneNullMinus
  module

theorem imaginarySplitPlaneNullPlus_sub_minus (a : Fin 3) :
    imaginarySplitPlaneNullPlus a - imaginarySplitPlaneNullMinus a =
      ellBasis a.succ := by
  unfold imaginarySplitPlaneNullPlus imaginarySplitPlaneNullMinus
  module

noncomputable def splitPlaneINullPlus : CZ := (1 / 2 : ℝ) •
  (quaternionBasis 1 + ellBasis 1)

noncomputable def splitPlaneINullMinus : CZ := (1 / 2 : ℝ) •
  (quaternionBasis 1 - ellBasis 1)

theorem splitPlaneINullPlus_sq :
    zMul splitPlaneINullPlus splitPlaneINullPlus = 0 := by
  rw [splitPlaneINullPlus, zMul_smul_left, zMul_smul_right]
  have hEq : quaternionBasis 1 + ellBasis 1 = splitPlaneI 1 1 := by
    simp [splitPlaneI]
  rw [hEq, splitPlaneI_sq]
  norm_num

theorem splitPlaneINullMinus_sq :
    zMul splitPlaneINullMinus splitPlaneINullMinus = 0 := by
  rw [splitPlaneINullMinus, zMul_smul_left, zMul_smul_right]
  have hEq : quaternionBasis 1 - ellBasis 1 = splitPlaneI 1 (-1) := by
    simp [splitPlaneI, sub_eq_add_neg]
  rw [hEq, splitPlaneI_sq]
  norm_num

theorem splitPlaneI_reconstruct_quaternion :
    splitPlaneINullPlus + splitPlaneINullMinus = quaternionBasis 1 := by
  unfold splitPlaneINullPlus splitPlaneINullMinus
  module

theorem splitPlaneI_reconstruct_ell :
    splitPlaneINullPlus - splitPlaneINullMinus = ellBasis 1 := by
  unfold splitPlaneINullPlus splitPlaneINullMinus
  module

theorem chiralNull_left_ell_eigenvector
    (a : Fin 4) (ε : ℝ) (hε : ε ^ 2 = 1) :
    zMul lUnit (chiralNull a ε) = ε • chiralNull a ε := by
  rw [chiralNull, zMul_smul_right, zMul_add_right, zMul_smul_right]
  change (1 / 2 : ℝ) • (ellBasis a + ε • zMul lUnit (ellBasis a)) =
    ε • ((1 / 2 : ℝ) • (quaternionBasis a + ε • ellBasis a))
  rw [ell_basis_left_square]
  simp only [smul_add, smul_smul]
  ring_nf
  rw [hε]
  module

@[simp] theorem lUnit_left_chiralNull_plus (a : Fin 4) :
    zMul lUnit (chiralNull a 1) = chiralNull a 1 := by
  simpa using chiralNull_left_ell_eigenvector a 1 (by norm_num)

@[simp] theorem lUnit_left_chiralNull_minus (a : Fin 4) :
    zMul lUnit (chiralNull a (-1)) = -(chiralNull a (-1)) := by
  simpa using chiralNull_left_ell_eigenvector a (-1) (by norm_num)

/-! The chosen split direction acts as a genuine involution on the full
Zorn carrier.  This is a coordinate theorem for `lUnit`, not a claim that an
arbitrary norm involution comes from octonion multiplication. -/

theorem lUnit_left_mul_left_mul (X : CZ) :
    zMul lUnit (zMul lUnit X) = X := by
  ext i <;>
    simp [lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> simp

/-! Left multiplication by the chosen split unit reverses the canonical
determinant quadratic form.  This is the concrete para-metric sign law for
the selected axis. -/
theorem lUnit_left_det_neg (X : CZ) :
    ZornMatrix.detZ (zMul lUnit X) = -ZornMatrix.detZ X := by
  simp [ZornMatrix.detZ, zMul, lUnit,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    smul_eq_mul]
  ring

/-! Bilinear subtraction identities used by the concrete rank-one root
calculation below. -/
theorem zMul_sub_left (X Y Z : CZ) :
    zMul (X - Y) Z = zMul X Z - zMul Y Z := by
  rw [sub_eq_add_neg, zMul_add_left,
    show -Y = (-1 : ℝ) • Y by module, zMul_smul_left]
  module

theorem zMul_sub_right (X Y Z : CZ) :
    zMul X (Y - Z) = zMul X Y - zMul X Z := by
  rw [sub_eq_add_neg, zMul_add_right,
    show -Z = (-1 : ℝ) • Z by module, zMul_smul_right]
  module

/-! The chosen `i`-axis is an explicit split-quaternion slice.  These are
coordinate/product lemmas, not ambient associativity assumptions. -/
theorem ellBasis_i_right_mul :
    zMul (ellBasis 1) iUnit = -lUnit := by
  ext i <;>
    simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> norm_num

theorem i_ellBasis_i_mul :
    zMul iUnit (ellBasis 1) = lUnit := by
  have h := i_ell_i_anticommute
  change zMul iUnit (ellBasis 1) + zMul (ellBasis 1) iUnit = 0 at h
  rw [ellBasis_i_right_mul] at h
  have hz : zMul iUnit (ellBasis 1) - lUnit = 0 := by
    simpa [sub_eq_add_neg] using h
  exact sub_eq_zero.mp hz

theorem ellBasis_i_square :
    zMul (ellBasis 1) (ellBasis 1) = (1 : CZ) := by
  ext i <;>
    simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> norm_num

theorem ellBasis_i_left_mul :
    zMul lUnit (ellBasis 1) = iUnit :=
  ell_basis_left_square 1

theorem lUnit_i_right_mul :
    zMul lUnit iUnit = ellBasis 1 := rfl

theorem ellBasis_i_right_lUnit :
    zMul (ellBasis 1) lUnit = -iUnit := by
  ext i <;>
    simp [ellBasis, quaternionBasis, iUnit, lUnit, zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> norm_num

theorem i_right_lUnit :
    zMul iUnit lUnit = -ellBasis 1 :=
  il_eq_neg_li

noncomputable def splitPlaneINullNegativeRoot : CZ :=
  (1 / 2 : ℝ) • (ellBasis 1 - iUnit)

theorem lUnit_comm_splitPlaneINullPlus :
    zMul lUnit splitPlaneINullPlus -
        zMul splitPlaneINullPlus lUnit =
      (2 : ℝ) • splitPlaneINullPlus := by
  rw [splitPlaneINullPlus]
  rw [show quaternionBasis 1 = iUnit by rfl]
  rw [zMul_smul_right, zMul_add_right,
    lUnit_i_right_mul, ellBasis_i_left_mul,
    zMul_smul_left, zMul_add_left, i_right_lUnit,
    ellBasis_i_right_lUnit]
  module

theorem lUnit_comm_splitPlaneINullNegativeRoot :
    zMul lUnit splitPlaneINullNegativeRoot -
        zMul splitPlaneINullNegativeRoot lUnit =
      (-2 : ℝ) • splitPlaneINullNegativeRoot := by
  rw [splitPlaneINullNegativeRoot, zMul_smul_right,
    zMul_sub_right, ellBasis_i_left_mul, lUnit_i_right_mul,
    zMul_smul_left, zMul_sub_left, ellBasis_i_right_lUnit,
    i_right_lUnit]
  module

theorem splitPlaneINullPlus_comm_splitPlaneINullNegativeRoot :
    zMul splitPlaneINullPlus splitPlaneINullNegativeRoot -
        zMul splitPlaneINullNegativeRoot splitPlaneINullPlus = lUnit := by
  rw [splitPlaneINullPlus, splitPlaneINullNegativeRoot]
  rw [show quaternionBasis 1 = iUnit by rfl]
  rw [
    zMul_smul_left, zMul_smul_right, zMul_add_left, zMul_sub_right,
    zMul_sub_right, zMul_smul_left, zMul_smul_right,
    zMul_sub_left, zMul_add_right,
    zMul_add_right, i_sq, i_ellBasis_i_mul,
    ellBasis_i_square, ellBasis_i_right_mul]
  module

theorem splitPlaneINullPlus_anticomm_splitPlaneINullNegativeRoot :
    zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
        zMul splitPlaneINullNegativeRoot splitPlaneINullPlus = (1 : CZ) := by
  rw [splitPlaneINullPlus, splitPlaneINullNegativeRoot]
  rw [show quaternionBasis 1 = iUnit by rfl]
  rw [
    zMul_smul_left, zMul_smul_right, zMul_add_left, zMul_sub_right,
    zMul_sub_right, zMul_smul_left, zMul_smul_right,
    zMul_sub_left, zMul_add_right,
    zMul_add_right, i_sq, i_ellBasis_i_mul,
    ellBasis_i_square, ellBasis_i_right_mul]
  module

theorem splitPlaneINullPlus_mul_splitPlaneINullNegativeRoot :
    zMul splitPlaneINullPlus splitPlaneINullNegativeRoot =
      (1 / 2 : ℝ) • (1 + lUnit) := by
  have hc := splitPlaneINullPlus_comm_splitPlaneINullNegativeRoot
  have ha := splitPlaneINullPlus_anticomm_splitPlaneINullNegativeRoot
  have hsum :
      zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
          zMul splitPlaneINullPlus splitPlaneINullNegativeRoot =
        1 + lUnit := by
    calc
      zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
          zMul splitPlaneINullPlus splitPlaneINullNegativeRoot =
        (zMul splitPlaneINullPlus splitPlaneINullNegativeRoot -
            zMul splitPlaneINullNegativeRoot splitPlaneINullPlus) +
          (zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
            zMul splitPlaneINullNegativeRoot splitPlaneINullPlus) := by
              module
      _ = lUnit + 1 := by rw [hc, ha]
      _ = 1 + lUnit := by module
  calc
    zMul splitPlaneINullPlus splitPlaneINullNegativeRoot =
        (1 / 2 : ℝ) •
          (zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
            zMul splitPlaneINullPlus splitPlaneINullNegativeRoot) := by
              module
    _ = (1 / 2 : ℝ) • (1 + lUnit) := by rw [hsum]

theorem splitPlaneINullNegativeRoot_mul_splitPlaneINullPlus :
    zMul splitPlaneINullNegativeRoot splitPlaneINullPlus =
      (1 / 2 : ℝ) • (1 - lUnit) := by
  have hc := splitPlaneINullPlus_comm_splitPlaneINullNegativeRoot
  have ha := splitPlaneINullPlus_anticomm_splitPlaneINullNegativeRoot
  have hsum :
      zMul splitPlaneINullNegativeRoot splitPlaneINullPlus +
          zMul splitPlaneINullNegativeRoot splitPlaneINullPlus =
        1 - lUnit := by
    calc
      zMul splitPlaneINullNegativeRoot splitPlaneINullPlus +
          zMul splitPlaneINullNegativeRoot splitPlaneINullPlus =
        (zMul splitPlaneINullPlus splitPlaneINullNegativeRoot +
            zMul splitPlaneINullNegativeRoot splitPlaneINullPlus) -
          (zMul splitPlaneINullPlus splitPlaneINullNegativeRoot -
            zMul splitPlaneINullNegativeRoot splitPlaneINullPlus) := by
              module
      _ = 1 - lUnit := by rw [ha, hc]
  calc
    zMul splitPlaneINullNegativeRoot splitPlaneINullPlus =
        (1 / 2 : ℝ) •
          (zMul splitPlaneINullNegativeRoot splitPlaneINullPlus +
            zMul splitPlaneINullNegativeRoot splitPlaneINullPlus) := by
              module
    _ = (1 / 2 : ℝ) • (1 - lUnit) := by rw [hsum]

theorem splitPlaneINullNegativeRoot_sq :
    zMul splitPlaneINullNegativeRoot splitPlaneINullNegativeRoot = 0 := by
  rw [splitPlaneINullNegativeRoot, zMul_smul_left, zMul_smul_right,
    zMul_sub_left, zMul_sub_right, zMul_sub_right,
    ellBasis_i_square, ellBasis_i_right_mul,
    i_ellBasis_i_mul, i_sq]
  module

theorem chiralNull_reconstruct_quaternion (a : Fin 4) :
    chiralNull a 1 + chiralNull a (-1) = quaternionBasis a := by
  unfold chiralNull
  module

theorem chiralNull_reconstruct_ell (a : Fin 4) :
    chiralNull a 1 - chiralNull a (-1) = ellBasis a := by
  unfold chiralNull
  module

/-! Composition automorphisms fix the unit but transport the chosen
split-complex polarization. -/

theorem realZornCompositionAut_maps_ellBasis
    (φ : realZornCompositionAut) (a : Fin 4) :
    (φ : CanonicalLinearAut) (ellBasis a) =
      zMul ((φ : CanonicalLinearAut) lUnit)
        ((φ : CanonicalLinearAut) (quaternionBasis a)) := by
  unfold ellBasis
  rw [realZornCompositionAut_preserves_mul]

theorem realZornCompositionAut_maps_chiralNull
    (φ : realZornCompositionAut) (a : Fin 4) (ε : ℝ) :
    (φ : CanonicalLinearAut) (chiralNull a ε) =
      (1 / 2 : ℝ) •
        ((φ : CanonicalLinearAut) (quaternionBasis a) +
          ε • zMul ((φ : CanonicalLinearAut) lUnit)
            ((φ : CanonicalLinearAut) (quaternionBasis a))) := by
  unfold chiralNull
  rw [map_smul, map_add, map_smul]
  rw [realZornCompositionAut_maps_ellBasis]

theorem realZornCompositionAut_maps_scalarChiralNull
    (φ : realZornCompositionAut) (ε : ℝ) :
    (φ : CanonicalLinearAut) (chiralNull ⟨0, by decide⟩ ε) =
      (1 / 2 : ℝ) •
        ((1 : CZ) + ε • (φ : CanonicalLinearAut) lUnit) := by
  rw [realZornCompositionAut_maps_chiralNull]
  simp only [quaternionBasis, realZornCompositionAut_fix_one]
  rw [zMul_one]

theorem realZornCompositionAut_maps_chiralNull_sum
    (φ : realZornCompositionAut) (a : Fin 4) :
    (φ : CanonicalLinearAut) (chiralNull a 1 + chiralNull a (-1)) =
      (φ : CanonicalLinearAut) (quaternionBasis a) := by
  rw [chiralNull_reconstruct_quaternion]

theorem realZornCompositionAut_maps_chiralNull_difference
    (φ : realZornCompositionAut) (a : Fin 4) :
    (φ : CanonicalLinearAut) (chiralNull a 1 - chiralNull a (-1)) =
      (φ : CanonicalLinearAut) (ellBasis a) := by
  rw [chiralNull_reconstruct_ell]

@[simp] theorem ellBasis_zero :
    ellBasis ⟨0, by decide⟩ = lUnit := by
  change zMul lUnit 1 = lUnit
  exact zMul_one lUnit

@[simp] theorem scalar_chiralNull_plus_idempotent :
    chiralNull ⟨0, by decide⟩ 1 = (1 / 2 : ℝ) • (1 + lUnit) := by
  rw [chiralNull]
  simp only [quaternionBasis, one_smul]
  rw [ellBasis_zero]

@[simp] theorem scalar_chiralNull_minus_idempotent :
    chiralNull ⟨0, by decide⟩ (-1) = (1 / 2 : ℝ) • (1 - lUnit) := by
  rw [chiralNull]
  simp only [quaternionBasis, neg_one_smul]
  rw [ellBasis_zero]
  rfl

theorem one_add_ell_sq :
    zMul (1 + lUnit) (1 + lUnit) = (2 : ℝ) • (1 + lUnit) := by
  ext i <;>
    simp [zMul, lUnit, smul_eq_mul, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem one_sub_ell_sq :
    zMul (1 - lUnit) (1 - lUnit) = (2 : ℝ) • (1 - lUnit) := by
  ext i <;>
    simp [zMul, lUnit, smul_eq_mul, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem ell_idempotent_plus :
    zMul ((1 / 2 : ℝ) • (1 + lUnit)) ((1 / 2 : ℝ) • (1 + lUnit)) =
      (1 / 2 : ℝ) • (1 + lUnit) := by
  rw [zMul_smul_left, zMul_smul_right, one_add_ell_sq]
  module

theorem ell_idempotent_minus :
    zMul ((1 / 2 : ℝ) • (1 - lUnit)) ((1 / 2 : ℝ) • (1 - lUnit)) =
      (1 / 2 : ℝ) • (1 - lUnit) := by
  rw [zMul_smul_left, zMul_smul_right, one_sub_ell_sq]
  module

theorem ell_idempotent_plus_mul_minus :
    zMul ((1 / 2 : ℝ) • (1 + lUnit)) ((1 / 2 : ℝ) • (1 - lUnit)) = 0 := by
  ext i <;>
    simp [zMul, lUnit, smul_eq_mul, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem ell_idempotent_minus_mul_plus :
    zMul ((1 / 2 : ℝ) • (1 - lUnit)) ((1 / 2 : ℝ) • (1 + lUnit)) = 0 := by
  ext i <;>
    simp [zMul, lUnit, smul_eq_mul, Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

end InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes

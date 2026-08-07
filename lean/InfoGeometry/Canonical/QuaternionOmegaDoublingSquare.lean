import Mathlib.Algebra.Quaternion
import Mathlib.Tactic
import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# The central quaternion-doubling branch

This owner records the associative central sibling of the hyperbolic
Cayley--Dickson doubling.  The parameter `ε` controls the square of the
central doubling unit; the product is kept explicit rather than installing a
new algebra structure on the pair carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionOmegaDoublingSquare

open InfoGeometry.Canonical.AlbertCayleyDickson

/-!
The native Albert parameter is retained separately from `CentralDouble`:
the former supplies the conjugation-twisted Cayley--Dickson product, while the
latter supplies the associative central product.  These declarations expose
the common doubling-unit calculations without identifying the two products.
-/

instance : SMulCommClass ℝ (Quaternion ℝ) (Quaternion ℝ) where
  smul_comm r a b := by
    ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul] <;> ring

instance : IsScalarTower ℝ (Quaternion ℝ) (Quaternion ℝ) where
  smul_assoc r a b := by
    ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul] <;> ring

abbrev ParamQuaternionDouble (ε : ℝ) :=
  AlbertStep ℝ (Quaternion ℝ) ε

def paramDoublingUnit (ε : ℝ) : ParamQuaternionDouble ε :=
  ⟨0, 1⟩

def paramQuaternionEmbed (ε : ℝ) (a : Quaternion ℝ) :
    ParamQuaternionDouble ε :=
  ⟨a, 0⟩

theorem paramDoublingUnit_sq (ε : ℝ) :
    AlbertStep.mul (paramDoublingUnit ε) (paramDoublingUnit ε) =
      ⟨ε, 0⟩ := by
  ext <;> simp [paramDoublingUnit, AlbertStep.mul]

theorem paramDoublingUnit_mul_embed (ε : ℝ) (a : Quaternion ℝ) :
    AlbertStep.mul (paramDoublingUnit ε) (paramQuaternionEmbed ε a) =
      ⟨0, star a⟩ := by
  ext <;> simp [paramDoublingUnit, paramQuaternionEmbed, AlbertStep.mul]

theorem paramEmbed_mul_doublingUnit (ε : ℝ) (a : Quaternion ℝ) :
    AlbertStep.mul (paramQuaternionEmbed ε a) (paramDoublingUnit ε) =
      ⟨0, a⟩ := by
  ext <;> simp [paramDoublingUnit, paramQuaternionEmbed, AlbertStep.mul]

@[ext] structure CentralDouble where
  p : Quaternion ℝ
  q : Quaternion ℝ

def centralZero : CentralDouble :=
  ⟨0, 0⟩

def centralOne : CentralDouble :=
  ⟨1, 0⟩

def centralEmbed (a : Quaternion ℝ) : CentralDouble :=
  ⟨a, 0⟩

def centralPart (a : Quaternion ℝ) : CentralDouble :=
  ⟨0, a⟩

def centralUnit : CentralDouble :=
  centralPart 1

def centralMul (ε : ℝ) (x y : CentralDouble) : CentralDouble :=
  ⟨x.p * y.p + ε • (x.q * y.q),
    x.p * y.q + x.q * y.p⟩

theorem centralMul_one_assoc (x y z : CentralDouble) :
    centralMul 1 (centralMul 1 x y) z =
      centralMul 1 x (centralMul 1 y z) := by
  ext <;> simp [centralMul] <;> noncomm_ring

theorem centralMul_neg_one_assoc (x y z : CentralDouble) :
    centralMul (-1) (centralMul (-1) x y) z =
      centralMul (-1) x (centralMul (-1) y z) := by
  ext <;> simp [centralMul] <;> noncomm_ring

theorem centralMul_assoc_of_sq_eq_one (ε : ℝ) (hε : ε ^ 2 = 1)
    (x y z : CentralDouble) :
    centralMul ε (centralMul ε x y) z =
      centralMul ε x (centralMul ε y z) := by
  rcases (sq_eq_one_iff.mp hε) with h | h
  · simpa [h] using centralMul_one_assoc x y z
  · simpa [h] using centralMul_neg_one_assoc x y z

@[simp] theorem centralZero_p : centralZero.p = 0 := rfl

@[simp] theorem centralZero_q : centralZero.q = 0 := rfl

@[simp] theorem centralOne_p : centralOne.p = 1 := rfl

@[simp] theorem centralOne_q : centralOne.q = 0 := rfl

@[simp] theorem centralEmbed_p (a : Quaternion ℝ) :
    (centralEmbed a).p = a := rfl

@[simp] theorem centralEmbed_q (a : Quaternion ℝ) :
    (centralEmbed a).q = 0 := rfl

@[simp] theorem centralPart_p (a : Quaternion ℝ) :
    (centralPart a).p = 0 := rfl

@[simp] theorem centralPart_q (a : Quaternion ℝ) :
    (centralPart a).q = a := rfl

@[simp] theorem centralUnit_p : centralUnit.p = 0 := rfl

@[simp] theorem centralUnit_q : centralUnit.q = 1 := rfl

theorem central_decomposition (x : CentralDouble) :
    x = ⟨x.p, x.q⟩ := by
  rfl

theorem centralEmbed_mul (ε : ℝ) (a b : Quaternion ℝ) :
    centralMul ε (centralEmbed a) (centralEmbed b) =
      centralEmbed (a * b) := by
  ext <;> simp [centralMul, centralEmbed]

theorem centralMul_centralOne_left (ε : ℝ) (x : CentralDouble) :
    centralMul ε centralOne x = x := by
  ext <;> simp [centralMul, centralOne]

theorem centralMul_centralOne_right (ε : ℝ) (x : CentralDouble) :
    centralMul ε x centralOne = x := by
  ext <;> simp [centralMul, centralOne]

theorem centralUnit_sq (ε : ℝ) :
    centralMul ε centralUnit centralUnit =
      ⟨ε, 0⟩ := by
  ext <;> simp [centralMul, centralUnit, centralPart]

theorem centralUnit_mul_embed (ε : ℝ) (a : Quaternion ℝ) :
    centralMul ε centralUnit (centralEmbed a) = centralPart a := by
  ext <;> simp [centralMul, centralUnit, centralPart, centralEmbed]

theorem centralEmbed_mul_unit (ε : ℝ) (a : Quaternion ℝ) :
    centralMul ε (centralEmbed a) centralUnit = centralPart a := by
  ext <;> simp [centralMul, centralUnit, centralPart, centralEmbed]

theorem centralUnit_commutes_with_embed (ε : ℝ) (a : Quaternion ℝ) :
    centralMul ε centralUnit (centralEmbed a) =
      centralMul ε (centralEmbed a) centralUnit := by
  rw [centralUnit_mul_embed, centralEmbed_mul_unit]

theorem centralUnit_fourth (ε : ℝ) (hε : ε ^ 2 = 1) :
    centralMul ε (centralMul ε centralUnit centralUnit)
        (centralMul ε centralUnit centralUnit) = centralOne := by
  calc
    centralMul ε (centralMul ε centralUnit centralUnit)
        (centralMul ε centralUnit centralUnit) =
        centralMul ε ⟨ε, 0⟩ ⟨ε, 0⟩ := by rw [centralUnit_sq]
    _ = ⟨ε * ε, 0⟩ := by
      ext <;> simp [centralMul]
    _ = centralOne := by
      ext <;> simp [centralOne]
      simpa [pow_two] using hε

def centralPlus : CentralDouble :=
  ⟨⟨(1 / 2 : ℝ), 0, 0, 0⟩, ⟨(1 / 2 : ℝ), 0, 0, 0⟩⟩

def centralMinus : CentralDouble :=
  ⟨⟨(1 / 2 : ℝ), 0, 0, 0⟩, ⟨-(1 / 2 : ℝ), 0, 0, 0⟩⟩

theorem centralPlus_idempotent :
    centralMul 1 centralPlus centralPlus = centralPlus := by
  ext <;>
    simp [centralMul, centralPlus] <;>
    norm_num [div_eq_mul_inv]

theorem centralMinus_idempotent :
    centralMul 1 centralMinus centralMinus = centralMinus := by
  ext <;>
    simp [centralMul, centralMinus] <;>
    norm_num [div_eq_mul_inv]

theorem centralPlus_mul_minus :
    centralMul 1 centralPlus centralMinus = centralZero := by
  ext <;>
    simp [centralMul, centralPlus, centralMinus, centralZero]

theorem centralMinus_mul_plus :
    centralMul 1 centralMinus centralPlus = centralZero := by
  ext <;>
    simp [centralMul, centralPlus, centralMinus, centralZero]

theorem centralPlus_add_minus :
    centralPlus.p + centralMinus.p = 1 ∧
      centralPlus.q + centralMinus.q = 0 := by
  constructor
  · ext <;> norm_num [centralPlus, centralMinus]
  · ext <;> norm_num [centralPlus, centralMinus]

end InfoGeometry.Canonical.QuaternionOmegaDoublingSquare

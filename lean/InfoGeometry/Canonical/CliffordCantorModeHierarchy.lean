import InfoGeometry.Clifford.SplitQ11
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Canonical.CliffordCantorModeHierarchy

Local split `Cl(1,1)` seed facts for the corrected hierarchy corridor.

This file owns only the finite split-quaternion and projector surface that is
kernel-backed in the repository.
-/

namespace CliffordCantorModeHierarchy

open InfoGeometry.Clifford

abbrev Alg := CliffordAlgebra splitQ11

/-- The `J` generator of the split `Cl(1,1)` atom. -/
noncomputable def jGen : Alg :=
  CliffordAlgebra.ι splitQ11 (1, 0)

/-- The `K` generator of the split `Cl(1,1)` atom. -/
noncomputable def kGen : Alg :=
  CliffordAlgebra.ι splitQ11 (0, 1)

/-- The pseudoscalar `ε = JK`. -/
noncomputable def epsGen : Alg :=
  jGen * kGen

/-- The lightlike `u_-` vector in the split head factor. -/
noncomputable def nullMinusVec : ℝ × ℝ :=
  ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- The lightlike `u_+` vector in the split head factor. -/
noncomputable def nullPlusVec : ℝ × ℝ :=
  ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))

/-- The lifted `u_-` Clifford generator. -/
noncomputable def nullMinus : Alg :=
  CliffordAlgebra.ι splitQ11 nullMinusVec

/-- The lifted `u_+` Clifford generator. -/
noncomputable def nullPlus : Alg :=
  CliffordAlgebra.ι splitQ11 nullPlusVec

/-- The negative `ε` spectral projector. -/
noncomputable def epsMinusProjector : Alg :=
  nullMinus * nullPlus

/-- The positive `ε` spectral projector. -/
noncomputable def epsPlusProjector : Alg :=
  nullPlus * nullMinus

/-- Prose-facing square-minus split-quaternion unit. -/
noncomputable def splitQuaternionI : Alg :=
  kGen

/-- Prose-facing first square-plus split-quaternion unit. -/
noncomputable def splitQuaternionJ : Alg :=
  epsGen

/-- Prose-facing second square-plus split-quaternion unit. -/
noncomputable def splitQuaternionK : Alg :=
  jGen

@[simp] theorem jGen_sq :
    jGen * jGen = 1 := by
  simp [jGen, splitQ11_apply]

@[simp] theorem kGen_sq :
    kGen * kGen = -(1 : Alg) := by
  simp [kGen, splitQ11_apply]

@[simp] theorem jGen_mul_kGen_add_swap :
    jGen * kGen + kGen * jGen = 0 := by
  have hpolar : QuadraticMap.polar splitQ11 ((1 : ℝ), 0) ((0 : ℝ), 1) = 0 := by
    simp [QuadraticMap.polar, splitQ11_apply]
  simpa [jGen, kGen, hpolar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := splitQ11) ((1 : ℝ), 0) ((0 : ℝ), 1))

@[simp] theorem kGen_mul_jGen :
    kGen * jGen = -epsGen := by
  exact eq_neg_of_add_eq_zero_left (by
    simp [epsGen, add_comm, jGen_mul_kGen_add_swap])

@[simp] theorem epsGen_mul_kGen :
    epsGen * kGen = -jGen := by
  unfold epsGen
  calc
    (jGen * kGen) * kGen = jGen * (kGen * kGen) := by rw [mul_assoc]
    _ = -jGen := by simp [kGen_sq]

@[simp] theorem kGen_mul_epsGen :
    kGen * epsGen = jGen := by
  unfold epsGen
  calc
    kGen * (jGen * kGen) = (kGen * jGen) * kGen := by rw [← mul_assoc]
    _ = (-epsGen) * kGen := by rw [kGen_mul_jGen]
    _ = -(epsGen * kGen) := by simp
    _ = jGen := by rw [epsGen_mul_kGen]; simp

@[simp] theorem epsGen_sq :
    epsGen * epsGen = 1 := by
  unfold epsGen
  calc
    (jGen * kGen) * (jGen * kGen)
        = jGen * (kGen * (jGen * kGen)) := by simp [mul_assoc]
    _ = jGen * (kGen * epsGen) := by rfl
    _ = jGen * jGen := by rw [kGen_mul_epsGen]
    _ = 1 := by simp [jGen_sq]

@[simp] theorem nullMinus_eq_half_jGen_add_kGen :
    nullMinus = (1 / 2 : ℝ) • (jGen + kGen) := by
  have hvec :
      nullMinusVec = (1 / 2 : ℝ) • ((1 : ℝ), 0) + (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num [nullMinusVec]
  rw [nullMinus, hvec, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  simp [jGen, kGen, smul_add]

@[simp] theorem nullPlus_eq_half_jGen_sub_kGen :
    nullPlus = (1 / 2 : ℝ) • (jGen - kGen) := by
  have hvec :
      nullPlusVec = (1 / 2 : ℝ) • ((1 : ℝ), 0) - (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num [nullPlusVec]
  rw [nullPlus, hvec, sub_eq_add_neg, LinearMap.map_add, LinearMap.map_smul,
    LinearMap.map_neg, LinearMap.map_smul]
  simp [jGen, kGen, sub_eq_add_neg, smul_add]

@[simp] theorem nullMinus_sq :
    nullMinus * nullMinus = 0 := by
  rw [nullMinus, CliffordAlgebra.ι_sq_scalar]
  simp [nullMinusVec, splitQ11_apply]

@[simp] theorem nullPlus_sq :
    nullPlus * nullPlus = 0 := by
  rw [nullPlus, CliffordAlgebra.ι_sq_scalar]
  simp [nullPlusVec, splitQ11_apply]

@[simp] theorem nullMinus_mul_nullPlus_add_swap :
    nullMinus * nullPlus + nullPlus * nullMinus = 1 := by
  have hpolar : QuadraticMap.polar splitQ11 nullMinusVec nullPlusVec = 1 := by
    simp [QuadraticMap.polar, nullMinusVec, nullPlusVec, splitQ11_apply]
    norm_num
  simpa [nullMinus, nullPlus, hpolar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := splitQ11) nullMinusVec nullPlusVec)

@[simp] theorem epsMinusProjector_eq_half_one_sub_eps :
    epsMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - epsGen) := by
  unfold epsMinusProjector
  rw [nullMinus_eq_half_jGen_add_kGen, nullPlus_eq_half_jGen_sub_kGen]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    kGen_mul_jGen, jGen_sq, kGen_sq, epsGen]
  module

@[simp] theorem epsPlusProjector_eq_half_one_add_eps :
    epsPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + epsGen) := by
  unfold epsPlusProjector
  rw [nullPlus_eq_half_jGen_sub_kGen, nullMinus_eq_half_jGen_add_kGen]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    kGen_mul_jGen, jGen_sq, kGen_sq, epsGen]
  module

@[simp] theorem epsMinusProjector_add_epsPlusProjector :
    epsMinusProjector + epsPlusProjector = 1 := by
  unfold epsMinusProjector epsPlusProjector
  simpa [add_comm] using nullMinus_mul_nullPlus_add_swap

@[simp] theorem epsMinusProjector_mul_epsPlusProjector :
    epsMinusProjector * epsPlusProjector = 0 := by
  rw [epsMinusProjector_eq_half_one_sub_eps, epsPlusProjector_eq_half_one_add_eps]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, epsGen_sq]
  module

@[simp] theorem epsPlusProjector_mul_epsMinusProjector :
    epsPlusProjector * epsMinusProjector = 0 := by
  rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, epsGen_sq]
  module

@[simp] theorem epsMinusProjector_idempotent :
    epsMinusProjector * epsMinusProjector = epsMinusProjector := by
  have h :
      epsMinusProjector = epsMinusProjector * epsMinusProjector := by
    calc
      epsMinusProjector
          = epsMinusProjector * (epsMinusProjector + epsPlusProjector) := by
              rw [epsMinusProjector_add_epsPlusProjector, mul_one]
      _ = epsMinusProjector * epsMinusProjector +
          epsMinusProjector * epsPlusProjector := by
              rw [mul_add]
      _ = epsMinusProjector * epsMinusProjector := by
              rw [epsMinusProjector_mul_epsPlusProjector, add_zero]
  exact h.symm

@[simp] theorem epsPlusProjector_idempotent :
    epsPlusProjector * epsPlusProjector = epsPlusProjector := by
  have h :
      epsPlusProjector = epsPlusProjector * epsPlusProjector := by
    calc
      epsPlusProjector
          = epsPlusProjector * (epsMinusProjector + epsPlusProjector) := by
              rw [epsMinusProjector_add_epsPlusProjector, mul_one]
      _ = epsPlusProjector * epsMinusProjector +
          epsPlusProjector * epsPlusProjector := by
              rw [mul_add]
      _ = epsPlusProjector * epsPlusProjector := by
              rw [epsPlusProjector_mul_epsMinusProjector, zero_add]
  exact h.symm

@[simp] theorem split_quaternion_basis_laws :
    splitQuaternionI * splitQuaternionI = -(1 : Alg)
      ∧ splitQuaternionJ * splitQuaternionJ = (1 : Alg)
      ∧ splitQuaternionK * splitQuaternionK = (1 : Alg)
      ∧ splitQuaternionI * splitQuaternionJ = splitQuaternionK
      ∧ splitQuaternionJ * splitQuaternionI = -splitQuaternionK := by
  exact ⟨by simp [splitQuaternionI], by simp [splitQuaternionJ],
    by simp [splitQuaternionK], by simp [splitQuaternionI, splitQuaternionJ, splitQuaternionK],
    by simp [splitQuaternionI, splitQuaternionJ, splitQuaternionK]⟩

/-- The split-null commutator in the local `Cl(1,1)` seed is the `ε` axis. -/
theorem splitNull_commutator_eq_eps :
    nullPlus * nullMinus - nullMinus * nullPlus = epsGen := by
  calc
    nullPlus * nullMinus - nullMinus * nullPlus
        = epsPlusProjector - epsMinusProjector := by rfl
    _ = epsGen := by
      rw [epsPlusProjector_eq_half_one_add_eps, epsMinusProjector_eq_half_one_sub_eps]
      rw [← smul_sub]
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      rw [← add_smul]
      norm_num

/--
Finite local seed for the split-quaternion/`Cl(1,1)` block.
-/
theorem local_split_quaternion_seed_laws :
    jGen * jGen = (1 : Alg)
      ∧ kGen * kGen = -(1 : Alg)
      ∧ epsGen * epsGen = (1 : Alg)
      ∧ nullPlus * nullPlus = 0
      ∧ nullMinus * nullMinus = 0
      ∧ nullMinus * nullPlus + nullPlus * nullMinus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen
      ∧ epsMinusProjector * epsMinusProjector = epsMinusProjector
      ∧ epsPlusProjector * epsPlusProjector = epsPlusProjector := by
  exact ⟨jGen_sq, kGen_sq, epsGen_sq, nullPlus_sq, nullMinus_sq,
    nullMinus_mul_nullPlus_add_swap, splitNull_commutator_eq_eps,
    epsMinusProjector_idempotent, epsPlusProjector_idempotent⟩

/-- Null products and the `p± = (1 ± ε) / 2` projector formulas. -/
theorem local_null_projector_formula_laws :
    nullPlus * nullMinus = epsPlusProjector
      ∧ nullMinus * nullPlus = epsMinusProjector
      ∧ epsPlusProjector = (1 / 2 : ℝ) • ((1 : Alg) + epsGen)
      ∧ epsMinusProjector = (1 / 2 : ℝ) • ((1 : Alg) - epsGen)
      ∧ nullPlus * nullMinus + nullMinus * nullPlus = (1 : Alg)
      ∧ nullPlus * nullMinus - nullMinus * nullPlus = epsGen := by
  exact ⟨rfl, rfl,
    epsPlusProjector_eq_half_one_add_eps,
    epsMinusProjector_eq_half_one_sub_eps,
    by simpa [add_comm] using nullMinus_mul_nullPlus_add_swap,
    splitNull_commutator_eq_eps⟩

end CliffordCantorModeHierarchy

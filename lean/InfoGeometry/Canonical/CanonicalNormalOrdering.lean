import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Order

/-!
# Canonical Polarized Fermionic Fock Space and Normal Ordering

This file proves the first exterior-Fock layers directly from exterior
multiplication and Clifford contraction.

The Fock space is the exterior algebra `ExteriorAlgebra R M`, implemented in
mathlib as the Clifford algebra of the zero quadratic form.  The vacuum is
`1`; the vacuum coefficient is the algebra map induced by the zero
one-particle functional; creation is left exterior multiplication;
annihilation is mathlib's Clifford/exterior
contraction `CliffordAlgebra.contractLeft`.

Problem 1 is the constructed CAR layer: creation and annihilation operators are
defined from exterior multiplication and contraction, then the polarized
integer modes satisfy the real CAR.

Problem 2 computes the raw contraction
`epsilon_0 (psiPlus a * psiMinus(-b) · Omega)` from these canonical
definitions and then proves that subtracting that computed contraction gives
zero vacuum coefficient.
-/

namespace InfoGeometry.Canonical.CanonicalNormalOrdering

open CliffordAlgebra

variable {R M : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- Fermionic Fock space as the exterior algebra. -/
abbrev Fock : Type _ :=
  ExteriorAlgebra R M

/-- Endomorphisms of exterior Fock space. -/
abbrev EndFock : Type _ :=
  Module.End R (Fock (R := R) (M := M))

/--
Canonical vacuum coefficient `epsilon_0 : Λ M → R`.

This is mathlib's left inverse to `algebraMap`; it is induced by the zero
linear map on one-particle generators.
-/
noncomputable def vacuumCoeff : Fock (R := R) (M := M) →ₐ[R] R :=
  ExteriorAlgebra.lift R
    ⟨(0 : M →ₗ[R] R), by
      intro m
      simp⟩

@[simp]
theorem vacuumCoeff_one :
    vacuumCoeff (R := R) (M := M) 1 = 1 := by
  simp [vacuumCoeff]

@[simp]
theorem vacuumCoeff_ι (v : M) :
    vacuumCoeff (R := R) (M := M) (ExteriorAlgebra.ι R v) = 0 := by
  simp [vacuumCoeff]

/--
Vacuum expectation of a Fock endomorphism: apply it to `Ω = 1`, then take the
scalar/vacuum coefficient.
-/
noncomputable def vacuumExpectEnd : EndFock (R := R) (M := M) →ₗ[R] R where
  toFun T := vacuumCoeff (R := R) (M := M) (T 1)
  map_add' T U := by
    simp [map_add]
  map_smul' r T := by
    simp

/--
Algebraic vacuum bracket `<Ω, T Ω>` in the exterior-Fock model.

No Hilbert completion or inner product is installed here; this is the canonical
vacuum coefficient of `T` applied to `Ω = 1`.
-/
noncomputable abbrev vacuumBracket (T : EndFock (R := R) (M := M)) : R :=
  vacuumExpectEnd (R := R) (M := M) T

@[simp]
theorem vacuumExpectEnd_one :
    vacuumExpectEnd (R := R) (M := M) 1 = 1 := by
  simp [vacuumExpectEnd]

/-- Creation by left exterior multiplication. -/
noncomputable def create (v : M) : EndFock (R := R) (M := M) :=
  Algebra.lmul R (Fock (R := R) (M := M)) (ExteriorAlgebra.ι R v)

/-- Annihilation by Clifford/exterior left contraction. -/
noncomputable def annih (d : Module.Dual R M) : EndFock (R := R) (M := M) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d

/--
Exterior-Fock CAR: annihilation followed by creation plus the reverse order is
the dual pairing times the identity.
-/
theorem annih_create_anticomm (d : Module.Dual R M) (v : M) :
    annih (R := R) (M := M) d * create (R := R) (M := M) v +
      create (R := R) (M := M) v * annih (R := R) (M := M) d =
        d v • (1 : EndFock (R := R) (M := M)) := by
  ext x
  simp [annih, create, CliffordAlgebra.contractLeft_ι_mul]

/--
Exterior-Fock CAR in the opposite displayed order.
-/
theorem create_annih_anticomm (v : M) (d : Module.Dual R M) :
    create (R := R) (M := M) v * annih (R := R) (M := M) d +
      annih (R := R) (M := M) d * create (R := R) (M := M) v =
        d v • (1 : EndFock (R := R) (M := M)) := by
  rw [add_comm]
  exact annih_create_anticomm (R := R) (M := M) d v

/--
Exterior-Fock CAR: two creators anticommute.
-/
theorem create_create_anticomm (v w : M) :
    create (R := R) (M := M) v * create (R := R) (M := M) w +
      create (R := R) (M := M) w * create (R := R) (M := M) v =
        (0 : EndFock (R := R) (M := M)) := by
  ext x
  simp [create]
  rw [← mul_assoc, ← mul_assoc, ← add_mul]
  rw [ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/--
Exterior-Fock CAR: two annihilators anticommute.
-/
theorem annih_annih_anticomm (d e : Module.Dual R M) :
    annih (R := R) (M := M) d * annih (R := R) (M := M) e +
      annih (R := R) (M := M) e * annih (R := R) (M := M) d =
        (0 : EndFock (R := R) (M := M)) := by
  ext x
  change CliffordAlgebra.contractLeft d (CliffordAlgebra.contractLeft e x) +
      CliffordAlgebra.contractLeft e (CliffordAlgebra.contractLeft d x) = 0
  rw [CliffordAlgebra.contractLeft_comm (Q := (0 : QuadraticForm R M)) d e x]
  simp

@[simp]
theorem annih_vacuum (d : Module.Dual R M) :
    annih (R := R) (M := M) d 1 = 0 := by
  simp [annih]

@[simp]
theorem create_vacuum (v : M) :
    create (R := R) (M := M) v 1 = ExteriorAlgebra.ι R v := by
  simp [create]

@[simp]
theorem annih_create_vacuum (d : Module.Dual R M) (v : M) :
    annih (R := R) (M := M) d (create (R := R) (M := M) v 1) =
      algebraMap R (Fock (R := R) (M := M)) (d v) := by
  simp [annih, create]

/-- Anticommutator of Fock endomorphisms, using composition. -/
noncomputable def carAnticommutator
    (S T : EndFock (R := R) (M := M)) : EndFock (R := R) (M := M) :=
  S.comp T + T.comp S

/-- The Fock anticommutator is symmetric. -/
theorem carAnticommutator_comm
    (S T : EndFock (R := R) (M := M)) :
    carAnticommutator (R := R) (M := M) S T =
      carAnticommutator (R := R) (M := M) T S := by
  ext x
  simp [carAnticommutator, add_comm]

/-- Contraction and exterior multiplication satisfy the canonical CAR. -/
theorem annih_create_CAR (d : Module.Dual R M) (v : M) :
    carAnticommutator (R := R) (M := M)
        (annih (R := R) (M := M) d)
        (create (R := R) (M := M) v) =
      (d v) • (1 : EndFock (R := R) (M := M)) := by
  ext x
  simp [carAnticommutator, annih, create, CliffordAlgebra.contractLeft_ι_mul,
    sub_eq_add_neg, add_left_comm, add_comm, Algebra.smul_def]

/-- Exterior multiplication operators anticommute. -/
theorem create_create_CAR (v w : M) :
    carAnticommutator (R := R) (M := M)
        (create (R := R) (M := M) v)
        (create (R := R) (M := M) w) =
      0 := by
  ext x
  simp only [carAnticommutator, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  change (ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * x)) +
      (ExteriorAlgebra.ι R w * (ExteriorAlgebra.ι R v * x)) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- Contraction operators anticommute. -/
theorem annih_annih_CAR (d e : Module.Dual R M) :
    carAnticommutator (R := R) (M := M)
        (annih (R := R) (M := M) d)
        (annih (R := R) (M := M) e) =
      0 := by
  ext x
  simp only [carAnticommutator, annih, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  rw [CliffordAlgebra.contractLeft_comm (Q := (0 : QuadraticForm R M))
    (d := d) (d' := e) (x := x)]
  simp

section PolarizedSea

variable (B : Module.Basis ℤ R M)

/-- Mode vector selected by the integer-indexed basis. -/
noncomputable def modeVec (a : ℤ) : M :=
  B a

/-- Dual mode selected by the coordinate functional of the basis. -/
noncomputable def modeDual (a : ℤ) : Module.Dual R M :=
  B.coord a

/-- Negative-mode occupation indicator. -/
def occMinus (a : ℤ) : R :=
  if a < 0 then 1 else 0

/-- Coordinate pairing of a basis mode and its dual. -/
theorem modeDual_modeVec (a b : ℤ) :
    modeDual (R := R) B a (modeVec (R := R) B b) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    simp [modeVec, modeDual, Module.Basis.coord_apply]
  · simp [modeVec, modeDual, Module.Basis.coord_apply, h]

/--
Sea-polarized plus modes.

Negative modes are treated as annihilators; nonnegative modes as creators.
-/
noncomputable def psiPlus (a : ℤ) : EndFock (R := R) (M := M) :=
  if a < 0 then annih (R := R) (M := M) (modeDual (R := R) B a)
  else create (R := R) (M := M) (modeVec (R := R) B a)

/--
Sea-polarized minus modes in the shifted notation `psiMinus(-b)`.

Negative occupied labels create a hole; nonnegative labels annihilate the
vacuum.
-/
noncomputable def psiMinusNeg (b : ℤ) : EndFock (R := R) (M := M) :=
  if b < 0 then create (R := R) (M := M) (modeVec (R := R) B b)
  else annih (R := R) (M := M) (modeDual (R := R) B b)

/--
Sea-polarized minus modes in the unshifted notation `psiMinus r`.

This is `psiMinusNeg (-r)`, so the CAR is written as
`{psiMinus r, psiPlus s} = δ_{r+s,0}`.
-/
noncomputable def psiMinus (r : ℤ) : EndFock (R := R) (M := M) :=
  psiMinusNeg (R := R) (M := M) B (-r)

/--
Shifted mixed CAR for the sea-polarized modes:
`{psiMinus(-b), psiPlus c} = δ_{bc} I`.
-/
theorem psiMinusNeg_psiPlus_anticomm (b c : ℤ) :
    psiMinusNeg (R := R) (M := M) B b * psiPlus (R := R) (M := M) B c +
      psiPlus (R := R) (M := M) B c * psiMinusNeg (R := R) (M := M) B b =
        (if b = c then 1 else 0) := by
  by_cases hb : b < 0
  · by_cases hc : c < 0
    · rw [psiMinusNeg, if_pos hb, psiPlus, if_pos hc, create_annih_anticomm,
        modeDual_modeVec]
      by_cases h : b = c
      · subst c
        simp
      · have hcb : c ≠ b := fun hcb => h hcb.symm
        simp [h, hcb]
    · have hbc : b ≠ c := by omega
      rw [psiMinusNeg, if_pos hb, psiPlus, if_neg hc, create_create_anticomm]
      simp [hbc]
  · by_cases hc : c < 0
    · have hbc : b ≠ c := by omega
      rw [psiMinusNeg, if_neg hb, psiPlus, if_pos hc, annih_annih_anticomm]
      simp [hbc]
    · rw [psiMinusNeg, if_neg hb, psiPlus, if_neg hc, annih_create_anticomm,
        modeDual_modeVec]
      simp

/--
Problem 1, mixed CAR: the sea-polarized exterior-Fock modes satisfy
`{psiMinus r, psiPlus s} = δ_{r+s,0} I`.
-/
theorem psiMinus_psiPlus_anticomm (r s : ℤ) :
    psiMinus (R := R) (M := M) B r * psiPlus (R := R) (M := M) B s +
      psiPlus (R := R) (M := M) B s * psiMinus (R := R) (M := M) B r =
        (if r + s = 0 then 1 else 0) := by
  unfold psiMinus psiPlus psiMinusNeg
  by_cases hs : s < 0
  · by_cases hr : 0 < r
    · simp [hs, hr]
      rw [create_annih_anticomm]
      by_cases hsum : r + s = 0
      · have hidx : s = -r := by omega
        simp [hidx, modeDual_modeVec]
      · have hidx : s ≠ -r := by omega
        simp [hsum, hidx, modeDual_modeVec]
    · simp [hs, hr]
      rw [annih_annih_anticomm]
      have hsum : r + s ≠ 0 := by omega
      simp [hsum]
  · by_cases hr : 0 < r
    · simp [hs, hr]
      rw [create_create_anticomm]
      have hsum : r + s ≠ 0 := by omega
      simp [hsum]
    · simp [hs, hr]
      rw [annih_create_anticomm]
      by_cases hsum : r + s = 0
      · have hidx : -r = s := by omega
        simp [hsum, hidx, modeDual_modeVec]
      · have hidx : -r ≠ s := by omega
        simp [hsum, hidx, modeDual_modeVec]

/--
Problem 1, plus-plus CAR: the sea-polarized plus modes anticommute.
-/
theorem psiPlus_psiPlus_anticomm (r s : ℤ) :
    psiPlus (R := R) (M := M) B r * psiPlus (R := R) (M := M) B s +
      psiPlus (R := R) (M := M) B s * psiPlus (R := R) (M := M) B r =
        (0 : EndFock (R := R) (M := M)) := by
  unfold psiPlus
  by_cases hr : r < 0
  · by_cases hs : s < 0
    · simp [hr, hs]
      exact annih_annih_anticomm (R := R) (M := M)
          (modeDual (R := R) B r) (modeDual (R := R) B s)
    · simp [hr, hs]
      rw [annih_create_anticomm]
      have hidx : r ≠ s := by omega
      simp [modeDual_modeVec, hidx]
  · by_cases hs : s < 0
    · simp [hr, hs]
      rw [create_annih_anticomm]
      have hidx : s ≠ r := by omega
      simp [modeDual_modeVec, hidx]
    · simp [hr, hs]
      exact create_create_anticomm (R := R) (M := M)
          (modeVec (R := R) B r) (modeVec (R := R) B s)

/--
Problem 1, minus-minus CAR: the sea-polarized minus modes anticommute.
-/
theorem psiMinus_psiMinus_anticomm (r s : ℤ) :
    psiMinus (R := R) (M := M) B r * psiMinus (R := R) (M := M) B s +
      psiMinus (R := R) (M := M) B s * psiMinus (R := R) (M := M) B r =
        (0 : EndFock (R := R) (M := M)) := by
  unfold psiMinus psiMinusNeg
  by_cases hr : 0 < r
  · by_cases hs : 0 < s
    · simp [hr, hs]
      exact create_create_anticomm (R := R) (M := M)
          (modeVec (R := R) B (-r)) (modeVec (R := R) B (-s))
    · simp [hr, hs]
      rw [create_annih_anticomm]
      have hidx : -s ≠ -r := by omega
      simp [modeDual_modeVec, hidx]
  · by_cases hs : 0 < s
    · simp [hr, hs]
      rw [annih_create_anticomm]
      have hidx : -r ≠ -s := by omega
      simp [modeDual_modeVec, hidx]
    · simp [hr, hs]
      exact annih_annih_anticomm (R := R) (M := M)
          (modeDual (R := R) B (-r)) (modeDual (R := R) B (-s))

/--
Problem 1 existence package: from an integer-indexed basis of the one-particle
space, the exterior-Fock construction supplies polarized fermion modes
satisfying the normalized CAR.

This is an existence theorem over `ExteriorAlgebra R M`.  The vacuum is
`1 : ExteriorAlgebra R M`, with negative sea encoded by the definitions of
`psiPlus` and `psiMinus`.
-/
theorem exists_polarizedFermionicFock_CAR (B : Module.Basis ℤ R M) :
    ∃ plus minus : ℤ → EndFock (R := R) (M := M),
      (∀ r s : ℤ,
        minus r * plus s + plus s * minus r =
          (if r + s = 0 then 1 else 0)) ∧
      (∀ r s : ℤ,
        plus r * plus s + plus s * plus r =
          (0 : EndFock (R := R) (M := M))) ∧
      (∀ r s : ℤ,
        minus r * minus s + minus s * minus r =
          (0 : EndFock (R := R) (M := M))) := by
  refine ⟨psiPlus (R := R) (M := M) B, psiMinus (R := R) (M := M) B, ?_, ?_, ?_⟩
  · exact psiMinus_psiPlus_anticomm (R := R) (M := M) B
  · exact psiPlus_psiPlus_anticomm (R := R) (M := M) B
  · exact psiMinus_psiMinus_anticomm (R := R) (M := M) B

/--
Concrete bundled CAR theorem for the constructed polarized modes.
-/
theorem polarizedFermionicFock_realCAR (r s : ℤ) :
    psiMinus (R := R) (M := M) B r * psiPlus (R := R) (M := M) B s +
        psiPlus (R := R) (M := M) B s * psiMinus (R := R) (M := M) B r =
          (if r + s = 0 then 1 else 0) ∧
      psiPlus (R := R) (M := M) B r * psiPlus (R := R) (M := M) B s +
          psiPlus (R := R) (M := M) B s * psiPlus (R := R) (M := M) B r =
            (0 : EndFock (R := R) (M := M)) ∧
      psiMinus (R := R) (M := M) B r * psiMinus (R := R) (M := M) B s +
          psiMinus (R := R) (M := M) B s * psiMinus (R := R) (M := M) B r =
            (0 : EndFock (R := R) (M := M)) := by
  exact ⟨psiMinus_psiPlus_anticomm (R := R) (M := M) B r s,
    psiPlus_psiPlus_anticomm (R := R) (M := M) B r s,
    psiMinus_psiMinus_anticomm (R := R) (M := M) B r s⟩

/-- Raw bilinear matrix unit `psiPlus a ∘ psiMinus(-b)`. -/
noncomputable def rawMatrixUnit (a b : ℤ) : EndFock (R := R) (M := M) :=
  (psiPlus (R := R) (M := M) B a).comp (psiMinusNeg (R := R) (M := M) B b)

/--
Computed contraction coefficient of the raw bilinear.

This is defined from the basis-dual pairing, not supplied as a field.
-/
noncomputable def contractionCoeff (a b : ℤ) : R :=
  if a < 0 then modeDual (R := R) B a (modeVec (R := R) B b) else 0

/--
Canonical raw contraction theorem.

The vacuum coefficient of the raw bilinear is computed from the exterior-Fock
definitions and mathlib's contraction identities.
-/
theorem rawMatrixUnit_vacuumExpect_eq_contractionCoeff (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := M) (rawMatrixUnit (R := R) (M := M) B a b) =
      contractionCoeff (R := R) B a b := by
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · simp [rawMatrixUnit, psiPlus, psiMinusNeg, contractionCoeff,
        vacuumExpectEnd, ha, hb, vacuumCoeff, create, annih]
    · have hne : a ≠ b := by omega
      have hp : modeDual (R := R) B a (modeVec (R := R) B b) = 0 := by
        simp [modeDual_modeVec, hne]
      simpa [rawMatrixUnit, psiPlus, psiMinusNeg, contractionCoeff,
        vacuumExpectEnd, ha, hb, vacuumCoeff, annih] using hp.symm
  · by_cases hb : b < 0
    · simp [rawMatrixUnit, psiPlus, psiMinusNeg, contractionCoeff,
        vacuumExpectEnd, ha, hb, vacuumCoeff, create]
    · simp [rawMatrixUnit, psiPlus, psiMinusNeg, contractionCoeff,
        vacuumExpectEnd, ha, hb, vacuumCoeff, create, annih]

/--
Compatibility spelling for the canonical raw contraction theorem.

Despite the name, the left-hand side is the endomorphism vacuum coefficient
`epsilon_0 (E Ω)`, implemented by `vacuumExpectEnd`.
-/
theorem rawMatrixUnit_vacuumCoeff_eq_contractionCoeff (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := M) (rawMatrixUnit (R := R) (M := M) B a b) =
      contractionCoeff (R := R) B a b :=
  rawMatrixUnit_vacuumExpect_eq_contractionCoeff (R := R) (M := M) B a b

/--
Coefficient form of the raw contraction theorem:
`epsilon_0 ((psiPlus a psiMinus(-b)) Omega)` is computed from the exterior-Fock
model.
-/
theorem rawMatrixUnit_vacuumCoeff_apply_vacuum_eq_contractionCoeff (a b : ℤ) :
    vacuumCoeff (R := R) (M := M) (rawMatrixUnit (R := R) (M := M) B a b 1) =
      contractionCoeff (R := R) B a b :=
  rawMatrixUnit_vacuumExpect_eq_contractionCoeff (R := R) (M := M) B a b

/-- The computed contraction is the Kronecker delta times the negative-mode occupation. -/
theorem contractionCoeff_eq_delta_occ (a b : ℤ) :
    contractionCoeff (R := R) B a b = if a = b then occMinus (R := R) a else 0 := by
  by_cases ha : a < 0
  · by_cases hab : a = b
    · subst b
      simp [contractionCoeff, occMinus, modeDual_modeVec, ha]
    · simp [contractionCoeff, modeDual_modeVec, ha, hab]
  · simp [contractionCoeff, occMinus, ha]

/--
Canonical normal-ordered matrix unit: subtract the computed vacuum contraction.
-/
noncomputable def normalMatrixUnit (a b : ℤ) : EndFock (R := R) (M := M) :=
  rawMatrixUnit (R := R) (M := M) B a b -
    contractionCoeff (R := R) B a b • (1 : EndFock (R := R) (M := M))

/--
Normal ordering is subtraction of the raw vacuum coefficient times the identity.
-/
theorem normalMatrixUnit_eq_raw_sub_vacuumContraction (a b : ℤ) :
    normalMatrixUnit (R := R) (M := M) B a b =
      rawMatrixUnit (R := R) (M := M) B a b -
        vacuumExpectEnd (R := R) (M := M)
            (rawMatrixUnit (R := R) (M := M) B a b) •
          (1 : EndFock (R := R) (M := M)) := by
  rw [normalMatrixUnit, rawMatrixUnit_vacuumExpect_eq_contractionCoeff]

/--
Normal ordering in Kronecker-delta form:
`E_ab = E_ab^raw - delta_ab * chi_-(a) * I`.
-/
theorem normalMatrixUnit_eq_raw_sub_delta_occ (a b : ℤ) :
    normalMatrixUnit (R := R) (M := M) B a b =
      rawMatrixUnit (R := R) (M := M) B a b -
        (if a = b then occMinus (R := R) a else 0) •
          (1 : EndFock (R := R) (M := M)) := by
  rw [normalMatrixUnit, contractionCoeff_eq_delta_occ]

/--
Problem 2: the normal-ordered matrix unit has zero vacuum coefficient.
-/
theorem normalMatrixUnit_vacuumExpect_zero (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := M)
        (normalMatrixUnit (R := R) (M := M) B a b) = 0 := by
  rw [normalMatrixUnit]
  simp only [LinearMap.map_sub, LinearMap.map_smul]
  rw [rawMatrixUnit_vacuumExpect_eq_contractionCoeff]
  simp [vacuumExpectEnd, vacuumCoeff]

/-- Compatibility spelling for the zero one-point function of normal ordering. -/
theorem normalMatrixUnit_vacuumCoeff_zero (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := M)
        (normalMatrixUnit (R := R) (M := M) B a b) = 0 :=
  normalMatrixUnit_vacuumExpect_zero (R := R) (M := M) B a b

/--
Problem 2 in coefficient form: the normal-ordered matrix unit has zero vacuum
coefficient after acting on `Omega = 1`.
-/
theorem normalMatrixUnit_vacuumCoeff_apply_vacuum_zero (a b : ℤ) :
    vacuumCoeff (R := R) (M := M) (normalMatrixUnit (R := R) (M := M) B a b 1) =
      0 :=
  normalMatrixUnit_vacuumExpect_zero (R := R) (M := M) B a b

/--
Equivalent Kronecker-delta form of the raw contraction.
-/
theorem rawMatrixUnit_vacuumExpect_eq_delta_occ (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := M) (rawMatrixUnit (R := R) (M := M) B a b) =
      if a = b then occMinus (R := R) a else 0 := by
  rw [rawMatrixUnit_vacuumExpect_eq_contractionCoeff, contractionCoeff_eq_delta_occ]

end PolarizedSea

section IntegerDirectSum

/--
The canonical integer-mode one-particle space
`⊕ r : ℤ, R e_r`, implemented as finitely supported functions.
-/
abbrev IntModeSpace (R : Type*) [Zero R] : Type _ :=
  ℤ →₀ R

/-- The canonical basis vector family `e_r` of `⊕ r : ℤ, R e_r`. -/
noncomputable abbrev intModeBasis (R : Type*) [Semiring R] :
    Module.Basis ℤ R (IntModeSpace R) :=
  Finsupp.basisSingleOne

/--
Problem 1 for the literal direct-sum mode space.

For `V = ⊕ r : ℤ, R e_r`, the constructed exterior Fock space
`ExteriorAlgebra R V` carries sea-polarized modes satisfying the normalized CAR.
This is obtained from `Finsupp.basisSingleOne`, exterior multiplication, and
Clifford/exterior contraction.
-/
theorem exists_polarizedFermionicFock_CAR_directSum (R : Type*) [CommRing R] :
    ∃ plus minus : ℤ → EndFock (R := R) (M := IntModeSpace R),
      (∀ r s : ℤ,
        minus r * plus s + plus s * minus r =
          (if r + s = 0 then 1 else 0)) ∧
      (∀ r s : ℤ,
        plus r * plus s + plus s * plus r =
          (0 : EndFock (R := R) (M := IntModeSpace R))) ∧
      (∀ r s : ℤ,
        minus r * minus s + minus s * minus r =
          (0 : EndFock (R := R) (M := IntModeSpace R))) :=
  exists_polarizedFermionicFock_CAR
    (R := R) (M := IntModeSpace R) (intModeBasis R)

/--
Problem 2, direct-sum raw contraction.

For `V = ⊕ r : ℤ, R e_r`, the vacuum coefficient of the raw bilinear
`psiPlus a * psiMinus(-b)` is exactly the Kronecker delta times the negative
occupation indicator.  This is computed from exterior multiplication,
Clifford/exterior contraction, and `Finsupp.basisSingleOne`.
-/
theorem rawMatrixUnit_vacuumExpect_eq_delta_occ_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := IntModeSpace R)
        (rawMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b) =
      if a = b then occMinus (R := R) a else 0 :=
  rawMatrixUnit_vacuumExpect_eq_delta_occ
    (R := R) (M := IntModeSpace R) (intModeBasis R) a b

/--
Direct-sum normal ordering is subtraction of the actual computed vacuum
contraction of the raw bilinear, not an arbitrary scalar.
-/
theorem normalMatrixUnit_eq_raw_sub_vacuumContraction_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    normalMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b =
      rawMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b -
        vacuumExpectEnd (R := R) (M := IntModeSpace R)
            (rawMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b) •
          (1 : EndFock (R := R) (M := IntModeSpace R)) :=
  normalMatrixUnit_eq_raw_sub_vacuumContraction
    (R := R) (M := IntModeSpace R) (intModeBasis R) a b

/--
Direct-sum normal ordering in Kronecker/occupation form:
`E_ab = E_ab^raw - δ_ab χ_-(a) I`.
-/
theorem normalMatrixUnit_eq_raw_sub_delta_occ_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    normalMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b =
      rawMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b -
        (if a = b then occMinus (R := R) a else 0) •
          (1 : EndFock (R := R) (M := IntModeSpace R)) :=
  normalMatrixUnit_eq_raw_sub_delta_occ
    (R := R) (M := IntModeSpace R) (intModeBasis R) a b

/--
Problem 2 for the literal direct-sum mode space:
normal ordering subtracts the computed raw contraction, and the normal-ordered
matrix unit has zero vacuum coefficient.
-/
theorem normalMatrixUnit_vacuumExpect_zero_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    vacuumExpectEnd (R := R) (M := IntModeSpace R)
        (normalMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b) = 0 :=
  normalMatrixUnit_vacuumExpect_zero
    (R := R) (M := IntModeSpace R) (intModeBasis R) a b

/--
Problem 2 in bracket notation for the literal direct-sum mode space:
`<Ω, E_ab Ω> = 0`, where the bracket is the canonical algebraic vacuum
coefficient.
-/
theorem normalMatrixUnit_vacuumBracket_zero_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    vacuumBracket (R := R) (M := IntModeSpace R)
        (normalMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b) = 0 :=
  normalMatrixUnit_vacuumExpect_zero_directSum R a b

/--
Problem 2 in coefficient form for the literal direct-sum mode space.
-/
theorem normalMatrixUnit_vacuumCoeff_apply_vacuum_zero_directSum
    (R : Type*) [CommRing R] (a b : ℤ) :
    vacuumCoeff (R := R) (M := IntModeSpace R)
        (normalMatrixUnit (R := R) (M := IntModeSpace R) (intModeBasis R) a b 1) = 0 :=
  normalMatrixUnit_vacuumCoeff_apply_vacuum_zero
    (R := R) (M := IntModeSpace R) (intModeBasis R) a b

end IntegerDirectSum

end InfoGeometry.Canonical.CanonicalNormalOrdering

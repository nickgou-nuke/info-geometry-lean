import Mathlib.Tactic
import InfoGeometry.Canonical.ArtinBraidFilteredColimit
import InfoGeometry.Canonical.GNSCARColimit

/-!
# Artin braid colimit represented by Jordan--Wigner Majorana operators

The countable Jordan--Wigner CAR family already exists in the algebraic
`Cl(1,1)` tensor-tower direct limit.  This owner turns that family into the
standard Majorana braid representation.

For each mode

`γᵢ = aᵢ† + aᵢ`

we prove `γᵢ² = 1` and pairwise anticommutation.  Hence the adjacent bivector
`βᵢ = γᵢ γᵢ₊₁` satisfies `βᵢ² = -1`.  The algebraic braid gate

`Rᵢ = 1 + βᵢ`

is a unit, with inverse `(1/2)(1-βᵢ)`.  The gates satisfy the adjacent Artin
relation and distant commutation.  Therefore each finite presented braid group
acts by units of the tensor-tower direct limit, the actions are compatible
with stabilization, and the universal property of the filtered colimit gives
a genuine representation

`B∞ -> Units(Cl(1,1)_∞)`.

No completion or analytic exponential is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation

open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Canonical.GNSCARColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open PresentedGroup

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- Stable Majorana mode in the algebraic tensor-tower direct limit. -/
def majoranaMode (i : ℕ) : Limit :=
  limit_u i + limit_v i

@[simp] theorem majoranaMode_sq (i : ℕ) :
    majoranaMode i * majoranaMode i = 1 := by
  change (limit_u i + limit_v i) * (limit_u i + limit_v i) = 1
  simp only [add_mul, mul_add]
  rw [limit_u_sq_zero i, limit_v_sq_zero i]
  simpa only [zero_add, add_zero, add_assoc, add_comm, add_left_comm] using
    (limit_uv_anticomm i)

/-- Distinct stable Majorana modes anticommute. -/
private theorem add_add_anticommute_of_pairwise
    {A : Type*} [Ring A] (a b c d : A)
    (hac : a * c + c * a = 0) (had : a * d + d * a = 0)
    (hbc : b * c + c * b = 0) (hbd : b * d + d * b = 0) :
    (a + b) * (c + d) + (c + d) * (a + b) = 0 := by
  calc
    (a + b) * (c + d) + (c + d) * (a + b) =
        (a * c + c * a) + (a * d + d * a) +
          (b * c + c * b) + (b * d + d * b) := by
            noncomm_ring
    _ = 0 := by rw [hac, had, hbc, hbd]; simp

theorem majoranaMode_anticommute {i j : ℕ} (hij : i ≠ j) :
    majoranaMode i * majoranaMode j + majoranaMode j * majoranaMode i = 0 := by
  apply add_add_anticommute_of_pairwise
  · exact limit_u_cross_site_anticommute hij
  · exact limit_u_v_cross_site_anticommute hij
  · exact limit_v_u_cross_site_anticommute hij
  · exact limit_v_cross_site_anticommute hij

/-- Adjacent Majorana bivector. -/
def majoranaBivector (i : ℕ) : Limit :=
  majoranaMode i * majoranaMode (i + 1)

@[simp] theorem majoranaBivector_sq (i : ℕ) :
    majoranaBivector i * majoranaBivector i = -1 := by
  have hanti := majoranaMode_anticommute (i := i) (j := i + 1) (by omega)
  have hswap :
      majoranaMode (i + 1) * majoranaMode i =
        -(majoranaMode i * majoranaMode (i + 1)) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hanti)
  calc
    majoranaBivector i * majoranaBivector i =
        majoranaMode i *
          (majoranaMode (i + 1) * majoranaMode i) *
          majoranaMode (i + 1) := by
            simp [majoranaBivector, mul_assoc]
    _ = majoranaMode i *
          (-(majoranaMode i * majoranaMode (i + 1))) *
          majoranaMode (i + 1) := by rw [hswap]
    _ = -(majoranaMode i * majoranaMode i) *
          (majoranaMode (i + 1) * majoranaMode (i + 1)) := by
            noncomm_ring
    _ = -1 := by rw [majoranaMode_sq, majoranaMode_sq]; simp

/-- Algebraic unnormalised braid gate.  It differs from the usual unitary gate
by the central scalar `sqrt 2`; the Artin relation is unchanged. -/
def majoranaBraidVal (i : ℕ) : Limit :=
  1 + majoranaBivector i

private theorem majoranaBraidVal_mul_inverseNumerator (i : ℕ) :
    majoranaBraidVal i * (1 - majoranaBivector i) =
      (2 : ℝ) • (1 : Limit) := by
  calc
    majoranaBraidVal i * (1 - majoranaBivector i) =
        1 - majoranaBivector i * majoranaBivector i := by
          let B := majoranaBivector i
          change (1 + B) * (1 - B) = 1 - B * B
          noncomm_ring
    _ = (2 : ℝ) • (1 : Limit) := by
      rw [majoranaBivector_sq i]
      simp [two_smul]

private theorem inverseNumerator_mul_majoranaBraidVal (i : ℕ) :
    (1 - majoranaBivector i) * majoranaBraidVal i =
      (2 : ℝ) • (1 : Limit) := by
  calc
    (1 - majoranaBivector i) * majoranaBraidVal i =
        1 - majoranaBivector i * majoranaBivector i := by
          let B := majoranaBivector i
          change (1 - B) * (1 + B) = 1 - B * B
          noncomm_ring
    _ = (2 : ℝ) • (1 : Limit) := by
      rw [majoranaBivector_sq i]
      simp [two_smul]

/-- The braid gate is a genuine unit of the algebraic tensor-tower colimit. -/
def majoranaBraidUnit (i : ℕ) : Limitˣ where
  val := majoranaBraidVal i
  inv := (1 / 2 : ℝ) • (1 - majoranaBivector i)
  val_inv := by
    rw [mul_smul_comm, majoranaBraidVal_mul_inverseNumerator]
    simp only [Algebra.smul_def]
    simp only [mul_one]
    rw [← map_mul]
    norm_num
  inv_val := by
    rw [smul_mul_assoc, inverseNumerator_mul_majoranaBraidVal]
    simp only [Algebra.smul_def]
    simp only [mul_one]
    rw [← map_mul]
    norm_num

@[simp] theorem majoranaBraidUnit_val (i : ℕ) :
    (majoranaBraidUnit i : Limit) = majoranaBraidVal i :=
  rfl

/-! Algebraic Clifford lemmas used by the Artin calculation. -/

private theorem adjacent_majorana_artin
    {A : Type*} [Ring A] (a b c : A)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b + b * a = 0)
    (hbc : b * c + c * b = 0)
    (hac : a * c + c * a = 0) :
    (1 + a * b) * (1 + b * c) * (1 + a * b) =
      (1 + b * c) * (1 + a * b) * (1 + b * c) := by
  have hba : b * a = -(a * b) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hab)
  have hcb : c * b = -(b * c) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hbc)
  have hca : c * a = -(a * c) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hac)
  have hab2 : (a * b) * (a * b) = -1 := by
    calc
      (a * b) * (a * b) = a * (b * a) * b := by simp [mul_assoc]
      _ = a * (-(a * b)) * b := by rw [hba]
      _ = -(a * a) * (b * b) := by noncomm_ring
      _ = -1 := by rw [ha, hb]; simp
  have hbc2 : (b * c) * (b * c) = -1 := by
    calc
      (b * c) * (b * c) = b * (c * b) * c := by simp [mul_assoc]
      _ = b * (-(b * c)) * c := by rw [hcb]
      _ = -(b * b) * (c * c) := by noncomm_ring
      _ = -1 := by rw [hb, hc]; simp
  have habbc : (a * b) * (b * c) = a * c := by
    calc
      (a * b) * (b * c) = a * (b * b) * c := by simp [mul_assoc]
      _ = a * c := by rw [hb]; simp
  have hbcab : (b * c) * (a * b) = -(a * c) := by
    calc
      (b * c) * (a * b) = b * (c * a) * b := by simp [mul_assoc]
      _ = b * (-(a * c)) * b := by rw [hca]
      _ = -(b * a) * (c * b) := by noncomm_ring
      _ = -(-(a * b)) * (-(b * c)) := by rw [hba, hcb]
      _ = -(a * c) := by
        simp only [neg_neg, mul_neg]
        rw [habbc]
  have hacab : (a * c) * (a * b) = b * c := by
    calc
      (a * c) * (a * b) = a * (c * a) * b := by simp [mul_assoc]
      _ = a * (-(a * c)) * b := by rw [hca]
      _ = -(a * a) * (c * b) := by noncomm_ring
      _ = -(c * b) := by rw [ha]; simp
      _ = b * c := by rw [hcb]; simp
  have hnegacbc : (-(a * c)) * (b * c) = a * b := by
    calc
      (-(a * c)) * (b * c) = -(a * (c * b) * c) := by simp [mul_assoc]
      _ = -(a * (-(b * c)) * c) := by rw [hcb]
      _ = a * b * (c * c) := by simp [mul_assoc]
      _ = a * b := by rw [hc]; simp
  calc
    (1 + a * b) * (1 + b * c) * (1 + a * b) =
        1 + a * b + b * c + (a * b) * (b * c) +
          a * b + (a * b) * (a * b) +
          (b * c) * (a * b) + ((a * b) * (b * c)) * (a * b) := by
            noncomm_ring
    _ = 2 • (a * b + b * c) := by
      rw [habbc, hab2, hbcab, hacab]
      abel
    _ = 1 + b * c + a * b + (b * c) * (a * b) +
          b * c + (b * c) * (b * c) +
          (a * b) * (b * c) + ((b * c) * (a * b)) * (b * c) := by
      rw [hbcab, hbc2, habbc, hnegacbc]
      abel
    _ = (1 + b * c) * (1 + a * b) * (1 + b * c) := by
      noncomm_ring

private theorem separated_bivectors_commute
    {A : Type*} [Ring A] (a b c d : A)
    (hac : a * c + c * a = 0)
    (had : a * d + d * a = 0)
    (hbc : b * c + c * b = 0)
    (hbd : b * d + d * b = 0) :
    (a * b) * (c * d) = (c * d) * (a * b) := by
  have hca : c * a = -(a * c) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hac)
  have hda : d * a = -(a * d) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using had)
  have hcb : c * b = -(b * c) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hbc)
  have hdb : d * b = -(b * d) :=
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hbd)
  calc
    (a * b) * (c * d) = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (-(c * b)) * d := by rw [hcb]; simp
    _ = -(a * c) * b * d := by simp [mul_assoc]
    _ = c * a * b * d := by rw [hca]
    _ = c * a * (-(d * b)) := by rw [hdb]; simp [mul_assoc]
    _ = -(c * a * d) * b := by simp [mul_assoc]
    _ = -(c * (a * d) * b) := by simp [mul_assoc]
    _ = c * (-(a * d)) * b := by noncomm_ring
    _ = c * (d * a) * b := by rw [hda]
    _ = c * d * a * b := by simp [mul_assoc]
    _ = (c * d) * (a * b) := by simp [mul_assoc]

/-- Adjacent tensor-colimit Majorana gates satisfy the Artin relation. -/
theorem majoranaBraidVal_artin (i : ℕ) :
    majoranaBraidVal i * majoranaBraidVal (i + 1) * majoranaBraidVal i =
      majoranaBraidVal (i + 1) * majoranaBraidVal i * majoranaBraidVal (i + 1) := by
  apply adjacent_majorana_artin
  · exact majoranaMode_sq i
  · exact majoranaMode_sq (i + 1)
  · exact majoranaMode_sq (i + 2)
  · exact majoranaMode_anticommute (by omega)
  · exact majoranaMode_anticommute (by omega)
  · exact majoranaMode_anticommute (by omega)

/-- Distant tensor-colimit Majorana gates commute. -/
theorem majoranaBraidVal_commute {i j : ℕ} (hij : i + 1 < j) :
    majoranaBraidVal i * majoranaBraidVal j =
      majoranaBraidVal j * majoranaBraidVal i := by
  have hbi : majoranaBivector i * majoranaBivector j =
      majoranaBivector j * majoranaBivector i := by
    apply separated_bivectors_commute
    · exact majoranaMode_anticommute (by omega)
    · exact majoranaMode_anticommute (by omega)
    · exact majoranaMode_anticommute (by omega)
    · exact majoranaMode_anticommute (by omega)
  unfold majoranaBraidVal
  rw [mul_add, add_mul, mul_add, add_mul]
  rw [hbi]
  noncomm_ring

/-- Unit-valued adjacent Artin relation. -/
theorem majoranaBraidUnit_artin (i : ℕ) :
    majoranaBraidUnit i * majoranaBraidUnit (i + 1) * majoranaBraidUnit i =
      majoranaBraidUnit (i + 1) * majoranaBraidUnit i * majoranaBraidUnit (i + 1) := by
  apply Units.ext
  exact majoranaBraidVal_artin i

/-- Unit-valued distant Artin commutation. -/
theorem majoranaBraidUnit_commute {i j : ℕ} (hij : i + 1 < j) :
    majoranaBraidUnit i * majoranaBraidUnit j =
      majoranaBraidUnit j * majoranaBraidUnit i := by
  apply Units.ext
  exact majoranaBraidVal_commute hij

private theorem units_adjacent_relator {x y : Limitˣ}
    (hxy : x * y * x = y * x * y) :
    (x * y * x) * (y * x * y)⁻¹ = 1 := by
  rw [hxy]
  exact mul_inv_cancel (y * x * y)

private theorem units_commuting_relator {x y : Limitˣ}
    (hxy : x * y = y * x) :
    (x * y) * (y * x)⁻¹ = 1 := by
  rw [hxy]
  exact mul_inv_cancel (y * x)

/-- The stable Majorana gates satisfy every defining relation of finite
`ArtinBraid n`. -/
theorem majoranaBraid_relations (n : ℕ) :
    ∀ r ∈ artinRelations n,
      FreeGroup.lift (fun i : ArtinGen n => majoranaBraidUnit i.1) r = 1 := by
  intro r hr
  rcases hr with hr | hr
  · rcases hr with ⟨i, j, hij, rfl⟩
    simp only [adjacentWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact units_adjacent_relator
      (x := majoranaBraidUnit (i : ℕ))
      (y := majoranaBraidUnit (j : ℕ))
      (by simpa only [hij] using majoranaBraidUnit_artin (i : ℕ))
  · rcases hr with ⟨i, j, hij, rfl⟩
    simp only [distantWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact units_commuting_relator
      (x := majoranaBraidUnit (i : ℕ))
      (y := majoranaBraidUnit (j : ℕ))
      (majoranaBraidUnit_commute hij)

/-- Finite Artin braid representation on the algebraic Jordan--Wigner tensor
colimit. -/
def finiteTensorBraidRepresentation (n : ℕ) :
    ArtinBraid n →* Limitˣ :=
  PresentedGroup.toGroup (majoranaBraid_relations n)

@[simp] theorem finiteTensorBraidRepresentation_generator
    (n : ℕ) (i : ArtinGen n) :
    finiteTensorBraidRepresentation n (PresentedGroup.of i) =
      majoranaBraidUnit i.1 := by
  exact PresentedGroup.toGroup.of (majoranaBraid_relations n)

/-- The finite tensor-colimit representations are compatible with the Artin
stabilization maps. -/
theorem finiteTensorBraidRepresentation_compatible
    {n m : ℕ} (h : n ≤ m) :
    (finiteTensorBraidRepresentation m).comp (artinStageMap h) =
      finiteTensorBraidRepresentation n := by
  apply PresentedGroup.ext
  intro i
  simp [finiteTensorBraidRepresentation_generator, generatorCast]

/-- The genuine infinite Artin braid representation obtained by descending the
compatible finite tensor-colimit representations through `B∞`. -/
def bInfinityTensorRepresentation : BInfinity →* Limitˣ :=
  bInfinityDesc finiteTensorBraidRepresentation
    (fun h => finiteTensorBraidRepresentation_compatible h)

@[simp] theorem bInfinityTensorRepresentation_sigma (i : ℕ) :
    bInfinityTensorRepresentation (sigmaInfinity i) = majoranaBraidUnit i := by
  change bInfinityDesc finiteTensorBraidRepresentation
      (fun h => finiteTensorBraidRepresentation_compatible h)
      (toBInfinity (i + 1)
        (PresentedGroup.of ⟨i, Nat.lt_succ_self i⟩ : ArtinBraid (i + 1))) = _
  rw [bInfinityDesc_stage]
  simp

/-- The infinite braid generator therefore acts by the concrete tensor-colimit
Majorana gate `1 + γᵢγᵢ₊₁`. -/
theorem bInfinityTensorRepresentation_sigma_val (i : ℕ) :
    ((bInfinityTensorRepresentation (sigmaInfinity i) : Limitˣ) : Limit) =
      1 + majoranaMode i * majoranaMode (i + 1) := by
  rw [bInfinityTensorRepresentation_sigma]
  rfl

end InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation

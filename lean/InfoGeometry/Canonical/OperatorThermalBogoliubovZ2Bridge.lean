import InfoGeometry.Canonical.ModularZ2CubeGrading
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR

/-!
# Thermal CAR transport and independent operator gradings

This file supplies the noncommutative bridge between the algebraic thermal CAR
transport and the already existing `ℤ₂³` grading.  The coefficients are
central only in the sense supplied by the `ℂ`-algebra structure; the operator
products themselves remain products in an arbitrary (possibly
noncommutative) ring.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

private lemma hasGrading_smul
    {Γ X : A} {b : Bool}
    (hX : ModularZ2CubeGrading.hasGrading Γ X b) (r : ℂ) :
    ModularZ2CubeGrading.hasGrading Γ (r • X) b := by
  simpa only [Algebra.smul_def] using
    (ModularZ2CubeGrading.hasGrading_mul_of_commute
      (Γ := Γ) (X := X) (c := algebraMap ℂ A r) hX
      (Algebra.commutes r Γ))

private lemma isHomogeneous_smul
    {Γ_R Γ_χ Γ_N X : A}
    (hX : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N X bR bχ bN)
    (r : ℂ) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N (r • X) bR bχ bN := by
  rcases hX with ⟨hR, hχ, hN⟩
  exact ⟨hasGrading_smul hR r, hasGrading_smul hχ r, hasGrading_smul hN r⟩

omit [Algebra ℂ A] in
private lemma isHomogeneous_add
    {Γ_R Γ_χ Γ_N X Y : A}
    (hX : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N X bR bχ bN)
    (hY : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N Y bR bχ bN) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N (X + Y) bR bχ bN := by
  rcases hX with ⟨hXR, hXχ, hXN⟩
  rcases hY with ⟨hYR, hYχ, hYN⟩
  exact ⟨ModularZ2CubeGrading.hasGrading_add hXR hYR,
    ModularZ2CubeGrading.hasGrading_add hXχ hYχ,
    ModularZ2CubeGrading.hasGrading_add hXN hYN⟩

private lemma hasGrading_map
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) {Γ X : A} {Γ' : B}
    (hΓ : φ Γ = Γ') {b : Bool}
    (hX : ModularZ2CubeGrading.hasGrading Γ X b) :
    ModularZ2CubeGrading.hasGrading Γ' (φ X) b := by
  unfold ModularZ2CubeGrading.hasGrading at hX ⊢
  cases b
  · calc
      Γ' * φ X = φ Γ * φ X := by rw [hΓ]
      _ = φ (Γ * X) := (φ.map_mul Γ X).symm
      _ = φ (X * Γ) := congrArg φ hX
      _ = φ X * φ Γ := φ.map_mul X Γ
      _ = φ X * Γ' := by rw [hΓ]
  · calc
      Γ' * φ X + φ X * Γ' =
          φ Γ * φ X + φ X * φ Γ := by rw [hΓ]
      _ = φ (Γ * X) + φ (X * Γ) :=
        congrArg₂ (fun p q : B => p + q)
          (φ.map_mul Γ X).symm (φ.map_mul X Γ).symm
      _ = φ (Γ * X + X * Γ) := (φ.map_add _ _).symm
      _ = φ 0 := congrArg φ hX
      _ = 0 := φ.map_zero

theorem isHomogeneous_map
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B)
    {Γ_R Γ_χ Γ_N X : A} {Γ'_R Γ'_χ Γ'_N : B}
    (hΓ_R : φ Γ_R = Γ'_R) (hΓ_χ : φ Γ_χ = Γ'_χ)
    (hΓ_N : φ Γ_N = Γ'_N)
    (hX : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N X bR bχ bN) :
    ModularZ2CubeGrading.isHomogeneous Γ'_R Γ'_χ Γ'_N (φ X) bR bχ bN := by
  rcases hX with ⟨hR, hχ, hN⟩
  exact ⟨hasGrading_map φ hΓ_R hR, hasGrading_map φ hΓ_χ hχ,
    hasGrading_map φ hΓ_N hN⟩

theorem thermal_annihilator_is_fully_odd
    {Γ_R Γ_χ Γ_N a d : A}
    (ha : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N a)
    (hd : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N d)
    (u v : ℂ) :
    ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N
      (thermalAnnihilator a d u v) := by
  unfold ModularZ2CubeGrading.isFullyOdd at *
  unfold thermalAnnihilator
  exact isHomogeneous_add (isHomogeneous_smul ha u) (isHomogeneous_smul hd v)

theorem thermal_creator_is_fully_odd
    {Γ_R Γ_χ Γ_N c b : A}
    (hc : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N c)
    (hb : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N b)
    (u v : ℂ) :
    ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N
      (thermalCreator c b u v) := by
  unfold ModularZ2CubeGrading.isFullyOdd at *
  unfold thermalCreator
  exact isHomogeneous_add (isHomogeneous_smul hc u) (isHomogeneous_smul hb v)

theorem thermal_annihilator_is_homogeneous
    {Γ_R Γ_χ Γ_N a d : A}
    (ha : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N a bR bχ bN)
    (hd : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N d bR bχ bN)
    (u v : ℂ) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N
      (thermalAnnihilator a d u v) bR bχ bN := by
  unfold thermalAnnihilator
  exact isHomogeneous_add (isHomogeneous_smul ha u) (isHomogeneous_smul hd v)

theorem thermal_creator_is_homogeneous
    {Γ_R Γ_χ Γ_N c b : A}
    (hc : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N c bR bχ bN)
    (hb : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N b bR bχ bN)
    (u v : ℂ) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N
      (thermalCreator c b u v) bR bχ bN := by
  unfold thermalCreator
  exact isHomogeneous_add (isHomogeneous_smul hc u) (isHomogeneous_smul hb v)

/-! ## Operator-valued coefficients

The coefficient operators are not assumed commutative.  Their grading is an
explicit input: fully-even coefficients preserve the degree of the CAR
generators under multiplication.  The CAR identity itself additionally
requires the centrality hypotheses used by the operator-valued expansion.
-/

omit [Algebra ℂ A] in
theorem operator_thermal_annihilator_is_homogeneous
    {Γ_R Γ_χ Γ_N a d u v : A}
    (hu : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N u)
    (hv : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N v)
    (ha : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N a bR bχ bN)
    (hd : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N d bR bχ bN) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N
      (operatorThermalAnnihilator a d u v) bR bχ bN := by
  unfold operatorThermalAnnihilator
  unfold ModularZ2CubeGrading.isFullyEven at hu hv
  simpa using isHomogeneous_add
    (ModularZ2CubeGrading.isHomogeneous_mul hu ha)
    (ModularZ2CubeGrading.isHomogeneous_mul hv hd)

omit [Algebra ℂ A] in
theorem operator_thermal_creator_is_homogeneous
    {Γ_R Γ_χ Γ_N c b u v : A}
    (hu : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N u)
    (hv : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N v)
    (hc : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N c bR bχ bN)
    (hb : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N b bR bχ bN) :
    ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N
      (operatorThermalCreator c b u v) bR bχ bN := by
  unfold operatorThermalCreator
  unfold ModularZ2CubeGrading.isFullyEven at hu hv
  simpa using isHomogeneous_add
    (ModularZ2CubeGrading.isHomogeneous_mul hu hc)
    (ModularZ2CubeGrading.isHomogeneous_mul hv hb)

omit [Algebra ℂ A] in
theorem operator_thermal_bogoliubov_car_is_fully_even
    {Γ_R Γ_χ Γ_N a c b d u v : A}
    (hu : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N u)
    (hv : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N v)
    (ha : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N a)
    (hc : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N c)
    (hb : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N b)
    (hd : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N d) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (thermalAnticommutator
        (operatorThermalAnnihilator a d u v)
        (operatorThermalCreator c b u v)) := by
  unfold ModularZ2CubeGrading.isFullyOdd at ha hc hb hd
  exact ModularZ2CubeGrading.anticommutator_of_same_homogeneous_is_fully_even
    (X := operatorThermalAnnihilator a d u v)
    (Y := operatorThermalCreator c b u v)
    (hX := operator_thermal_annihilator_is_homogeneous hu hv ha hd)
    (hY := operator_thermal_creator_is_homogeneous hu hv hc hb)

omit [Algebra ℂ A] in
theorem operator_thermal_bogoliubov_car_eq_one_and_fully_even
    {Γ_R Γ_χ Γ_N a c b d u v : A}
    (hu : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N u)
    (hv : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N v)
    (ha : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N a)
    (hc : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N c)
    (hb : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N b)
    (hd : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N d)
    (huc : ∀ z : A, z * u = u * z)
    (hvc : ∀ z : A, z * v = v * z)
    (huv : u * u + v * v = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    thermalAnticommutator
        (operatorThermalAnnihilator a d u v)
        (operatorThermalCreator c b u v) = 1 ∧
      ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
        (thermalAnticommutator
          (operatorThermalAnnihilator a d u v)
          (operatorThermalCreator c b u v)) := by
  exact ⟨operator_thermal_bogoliubov_car_preserved a c b d u v
      huc hvc huv hac hbd hab hcd,
    operator_thermal_bogoliubov_car_is_fully_even hu hv ha hc hb hd⟩

theorem thermal_bogoliubov_anticommutator_is_fully_even_of_same_degree
    {Γ_R Γ_χ Γ_N a c b d : A}
    (ha : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N a bR bχ bN)
    (hc : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N c bR bχ bN)
    (hb : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N b bR bχ bN)
    (hd : ModularZ2CubeGrading.isHomogeneous Γ_R Γ_χ Γ_N d bR bχ bN)
    (u v : ℂ) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (thermalAnticommutator
        (thermalAnnihilator a d u v)
        (thermalCreator c b u v)) := by
  exact ModularZ2CubeGrading.anticommutator_of_same_homogeneous_is_fully_even
    (Γ_R := Γ_R) (Γ_χ := Γ_χ) (Γ_N := Γ_N)
    (thermal_annihilator_is_homogeneous ha hd u v)
    (thermal_creator_is_homogeneous hc hb u v)

theorem thermal_bogoliubov_car_is_fully_even
    {Γ_R Γ_χ Γ_N a c b d : A}
    (ha : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N a)
    (hc : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N c)
    (hb : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N b)
    (hd : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N d)
    (u v : ℂ) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
      (thermalAnticommutator
        (thermalAnnihilator a d u v)
        (thermalCreator c b u v)) := by
  have hA := thermal_annihilator_is_fully_odd ha hd u v
  have hC := thermal_creator_is_fully_odd hc hb u v
  exact ModularZ2CubeGrading.anticommutator_of_fully_odd_is_fully_even
    (Γ_R := Γ_R) (Γ_χ := Γ_χ) (Γ_N := Γ_N)
    (X := thermalAnnihilator a d u v) (Y := thermalCreator c b u v)
    hA hC

theorem thermal_bogoliubov_car_eq_one_and_fully_even
    {Γ_R Γ_χ Γ_N a c b d : A}
    (ha : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N a)
    (hc : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N c)
    (hb : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N b)
    (hd : ModularZ2CubeGrading.isFullyOdd Γ_R Γ_χ Γ_N d)
    (u v : ℂ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    thermalAnticommutator
        (thermalAnnihilator a d u v)
        (thermalCreator c b u v) = 1 ∧
      ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
        (thermalAnticommutator
          (thermalAnnihilator a d u v)
          (thermalCreator c b u v)) := by
  exact ⟨thermal_bogoliubov_car_preserved a c b d u v huv hac hbd hab hcd,
    thermal_bogoliubov_car_is_fully_even ha hc hb hd u v⟩

end InfoGeometry.Canonical

import InfoGeometry.Algebra.MaximalSplitOrder
import InfoGeometry.Algebra.ZornDerivationBridge

namespace InfoGeometry.Algebra.ZornVectorMatrix

open scoped BigOperators

variable {R : Type*} [CommRing R]

def polar (X Y : ZornVectorMatrix ℚ) : ℚ :=
  X.a * Y.b + Y.a * X.b -
    (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2 +
      Y.v 0 * X.w 0 + Y.v 1 * X.w 1 + Y.v 2 * X.w 2)

lemma polar_self (X : ZornVectorMatrix ℚ) :
    polar X X = 2 * norm X := by
  simp only [polar, norm]
  rw [ZornVec3.dot_eq_sum_coords]
  ring

lemma polar_symm (X Y : ZornVectorMatrix ℚ) :
    polar X Y = polar Y X := by
  simp only [polar]
  ring

lemma polar_add_left (X Y Z : ZornVectorMatrix ℚ) :
    polar (X + Y) Z = polar X Z + polar Y Z := by
  change polar (ZornVectorMatrix.add X Y) Z = polar X Z + polar Y Z
  simp only [polar, ZornVectorMatrix.add]
  ring

lemma polar_neg_left (X Y : ZornVectorMatrix ℚ) :
    polar (-X) Y = -polar X Y := by
  change polar (ZornVectorMatrix.neg X) Y = -polar X Y
  simp only [polar, ZornVectorMatrix.neg]
  ring

lemma polar_add_right (X Y Z : ZornVectorMatrix ℚ) :
    polar X (Y + Z) = polar X Y + polar X Z := by
  change polar X (ZornVectorMatrix.add Y Z) = polar X Y + polar X Z
  simp only [polar, ZornVectorMatrix.add]
  ring

lemma polar_smul_left (r : ℚ) (X Y : ZornVectorMatrix ℚ) :
    polar (r • X) Y = r * polar X Y := by
  change polar (ZornVectorMatrix.smul r X) Y = r * polar X Y
  simp only [polar, ZornVectorMatrix.smul]
  ring

lemma polar_smul_right (r : ℚ) (X Y : ZornVectorMatrix ℚ) :
    polar X (r • Y) = r * polar X Y := by
  change polar X (ZornVectorMatrix.smul r Y) = r * polar X Y
  simp only [polar, ZornVectorMatrix.smul]
  ring

def polarBilinear :
    ZornVectorMatrix ℚ →ₗ[ℚ] ZornVectorMatrix ℚ →ₗ[ℚ] ℚ :=
  { toFun := fun X =>
      { toFun := fun Y => polar X Y
        map_add' := fun Y Z => polar_add_right X Y Z
        map_smul' := fun r Y => by
          simpa [smul_eq_mul] using polar_smul_right r X Y }
    map_add' := fun X Y => by
      apply LinearMap.ext
      intro Z
      exact polar_add_left X Y Z
    map_smul' := fun r X => by
      apply LinearMap.ext
      intro Y
      simpa [smul_eq_mul] using polar_smul_left r X Y }

lemma polarBilinear_symm (X Y : ZornVectorMatrix ℚ) :
    polarBilinear X Y = polarBilinear Y X := by
  exact polar_symm X Y

def dualLattice (L : AddSubgroup (ZornVectorMatrix ℚ)) :
    AddSubgroup (ZornVectorMatrix ℚ) where
  carrier := {X | ∀ Y ∈ L, ∃ n : ℤ, polar X Y = (n : ℚ)}
  zero_mem' := by
    intro Y hY
    refine ⟨0, ?_⟩
    change polar (ZornVectorMatrix.zero : ZornVectorMatrix ℚ) Y = (0 : ℚ)
    simp [polar, ZornVectorMatrix.zero]
  add_mem' := by
    intro X X' hX hX' Y hY
    rcases hX Y hY with ⟨m, hm⟩
    rcases hX' Y hY with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    rw [polar_add_left, hm, hn]
    norm_num
  neg_mem' := by
    intro X hX Y hY
    rcases hX Y hY with ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [polar_neg_left, hn]
    norm_num

def IsIntegralLattice (L : AddSubgroup (ZornVectorMatrix ℚ)) : Prop :=
  L ≤ dualLattice L

def integralLattice : AddSubgroup (ZornVectorMatrix ℚ) where
  carrier := {X | isMaximalSplitOrder X}
  zero_mem' := zero_isMaximalSplitOrder
  add_mem' := add_isMaximalSplitOrder
  neg_mem' := by
    intro X hX
    rcases hX with ⟨hhalf, ⟨t, ht⟩, ⟨n, hn⟩, hbilin⟩
    rcases hhalf with ⟨a, b, v, w, ha, hb, hv, hw⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨-a, -b, (fun i => -v i), (fun i => -w i), ?_, ?_, ?_, ?_⟩
      · change -X.a = (-a : ℚ) / 2
        rw [ha]
        ring
      · change -X.b = (-b : ℚ) / 2
        rw [hb]
        ring
      · intro i
        change -X.v i = (-(v i) : ℚ) / 2
        rw [hv i]
        ring
      · intro i
        change -X.w i = (-(w i) : ℚ) / 2
        rw [hw i]
        ring
    · refine ⟨-t, ?_⟩
      change -X.a + -X.b = (-t : ℚ)
      rw [← neg_add]
      rw [ht]
    · refine ⟨n, ?_⟩
      change (-X.a) * (-X.b) -
        ((-X.v 0) * (-X.w 0) + (-X.v 1) * (-X.w 1) + (-X.v 2) * (-X.w 2)) = (n : ℚ)
      calc
        (-X.a) * (-X.b) -
            ((-X.v 0) * (-X.w 0) + (-X.v 1) * (-X.w 1) + (-X.v 2) * (-X.w 2)) =
            X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) := by ring
        _ = (n : ℚ) := hn
    · intro Y hYhalf hYtrace hYnorm
      rcases hbilin Y hYhalf hYtrace hYnorm with ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      have hm' : polar X Y = (m : ℚ) := by
        simpa [polar, mul_comm] using hm
      calc
        (-X).a * Y.b + (-X).b * Y.a -
            ((-X).v 0 * Y.w 0 + (-X).v 1 * Y.w 1 + (-X).v 2 * Y.w 2 +
              Y.v 0 * (-X).w 0 + Y.v 1 * (-X).w 1 + Y.v 2 * (-X).w 2) =
            -polar X Y := by
              simp [polar, ZornVectorMatrix.neg]
              ring
        _ = ((-m : ℤ) : ℚ) := by
          rw [hm']
          norm_num

lemma integralLattice_is_integral : IsIntegralLattice integralLattice := by
  intro X hX Y hY
  rcases hX with ⟨_, _, _, hXbilin⟩
  rcases hXbilin Y hY.1 hY.2.1 hY.2.2.1 with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [polar, mul_comm] using hm

end InfoGeometry.Algebra.ZornVectorMatrix

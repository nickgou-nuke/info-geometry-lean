import InfoGeometry.RootSystem.D4WeylGroup

noncomputable section

/-!
# D₄ outer diagram maps on the integral root lattice

The carrier is the even-coordinate-sum subgroup of `ℤ⁴`, with the simple-root
basis owned by `D4RootLattice`. This file constructs reflections and a
permutation-indexed additive map on that lattice. The current results do not
establish preservation of the inner product or the root predicate by every
map, faithfulness, or an action by Lie-algebra automorphisms on `Out(D₄)`.
-/

namespace InfoGeometry.RootSystem.D4DynkinOuterReflectionCandidate

open InfoGeometry.RootSystem.D4

def outerRootDifference : Ambient := simpleRoot 0 - simpleRoot 2

theorem outerRootDifference_norm : dot outerRootDifference outerRootDifference = 4 := by
  norm_num [outerRootDifference, dot, simpleRoot, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem outerRootDifference_coordinateSum :
    coordinateSum outerRootDifference = 0 := by
  norm_num [outerRootDifference, coordinateSum, simpleRoot,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem outerPairing_even (x : Lattice) : Even (dot x.1 outerRootDifference) := by
  rcases Int.even_iff.mpr x.2 with ⟨k, hk⟩
  refine ⟨k - x.1 1 - x.1 2, ?_⟩
  have hpair : dot x.1 outerRootDifference =
      coordinateSum x.1 - 2 * x.1 1 - 2 * x.1 2 := by
    norm_num [outerRootDifference, dot, coordinateSum, simpleRoot,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
  rw [hpair, hk]
  ring

def halfOuterPairing (x : Lattice) : ℤ :=
  Classical.choose (outerPairing_even x)

theorem halfOuterPairing_spec (x : Lattice) :
    dot x.1 outerRootDifference =
      halfOuterPairing x + halfOuterPairing x :=
  Classical.choose_spec (outerPairing_even x)

theorem halfOuterPairing_add (x y : Lattice) :
    halfOuterPairing (x + y) = halfOuterPairing x + halfOuterPairing y := by
  have hxy : dot (x.1 + y.1) outerRootDifference =
      dot x.1 outerRootDifference + dot y.1 outerRootDifference := by
    simp [dot, Finset.sum_add_distrib, add_mul]
  have hx := halfOuterPairing_spec x
  have hy := halfOuterPairing_spec y
  have hxy' := halfOuterPairing_spec (x + y)
  change dot (x.1 + y.1) outerRootDifference = _ at hxy'
  rw [hxy, hx, hy] at hxy'
  omega

def reflectedAmbient (x : Lattice) : Ambient :=
  x.1 - halfOuterPairing x • outerRootDifference

theorem coordinateSum_smul (a : ℤ) (v : Ambient) :
    coordinateSum (a • v) = a * coordinateSum v := by
  simp [coordinateSum, Fin.sum_univ_four, Pi.smul_apply,
    zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem coordinateSum_sub (v w : Ambient) :
    coordinateSum (v - w) = coordinateSum v - coordinateSum w := by
  unfold coordinateSum
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]

theorem reflectedAmbient_coordinateSum (x : Lattice) :
    coordinateSum (reflectedAmbient x) = coordinateSum x.1 := by
  rw [reflectedAmbient, coordinateSum_sub, coordinateSum_smul,
    outerRootDifference_coordinateSum]
  simp

theorem reflectedAmbient_mem (x : Lattice) :
    IsD4 (reflectedAmbient x) := by
  change coordinateSum (reflectedAmbient x) % 2 = 0
  rw [reflectedAmbient_coordinateSum]
  exact x.2

def outerRootReflection (x : Lattice) : Lattice :=
  ⟨reflectedAmbient x, reflectedAmbient_mem x⟩

theorem dot_reflected_difference (x : Lattice) :
    dot (reflectedAmbient x) outerRootDifference =
      -(halfOuterPairing x + halfOuterPairing x) := by
  rw [reflectedAmbient, dot_sub_left, dot_smul_left,
    outerRootDifference_norm, halfOuterPairing_spec]
  ring

theorem halfOuterPairing_reflected (x : Lattice) :
    halfOuterPairing (outerRootReflection x) = -halfOuterPairing x := by
  have h := halfOuterPairing_spec (outerRootReflection x)
  change dot (reflectedAmbient x) outerRootDifference = _ at h
  rw [dot_reflected_difference] at h
  have h' : halfOuterPairing (outerRootReflection x) +
      halfOuterPairing (outerRootReflection x) =
        -(halfOuterPairing x + halfOuterPairing x) := h.symm
  omega

theorem outerRootReflection_involutive (x : Lattice) :
    outerRootReflection (outerRootReflection x) = x := by
  apply Subtype.ext
  change reflectedAmbient (outerRootReflection x) = x.1
  rw [reflectedAmbient, halfOuterPairing_reflected]
  simp only [outerRootReflection, Subtype.coe_mk, reflectedAmbient]
  funext i
  fin_cases i <;>
    simp [outerRootDifference, simpleRoot, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    rfl

theorem outerRootReflection_map_add (x y : Lattice) :
    outerRootReflection (x + y) = outerRootReflection x + outerRootReflection y := by
  apply Subtype.ext
  change reflectedAmbient (x + y) = reflectedAmbient x + reflectedAmbient y
  simp only [reflectedAmbient, halfOuterPairing_add, AddSubgroup.coe_add]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, add_zsmul]
  module

/-- The actual additive automorphism of the integral D₄ lattice induced by
the outer-root transposition. -/
def outerRootReflectionAddEquiv : Lattice ≃+ Lattice where
  toFun := outerRootReflection
  invFun := outerRootReflection
  left_inv := outerRootReflection_involutive
  right_inv := outerRootReflection_involutive
  map_add' := outerRootReflection_map_add

theorem outerRootReflection_simpleRoot_zero :
    outerRootReflectionAddEquiv (simpleRootLattice 0) = simpleRootLattice 2 := by
  apply Subtype.ext
  change reflectedAmbient (simpleRootLattice 0) = simpleRoot 2
  have hp : dot (simpleRoot 0) outerRootDifference = 2 := by
    norm_num [outerRootDifference, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh := halfOuterPairing_spec (simpleRootLattice 0)
  change dot (simpleRoot 0) outerRootDifference = _ at hh
  rw [hp] at hh
  have hhalf : halfOuterPairing (simpleRootLattice 0) = 1 := by omega
  rw [reflectedAmbient, hhalf]
  apply funext
  intro i
  fin_cases i <;>
    norm_num [simpleRootLattice, outerRootDifference, simpleRoot, sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem outerRootReflection_simpleRoot_two :
    outerRootReflectionAddEquiv (simpleRootLattice 2) = simpleRootLattice 0 := by
  apply Subtype.ext
  change reflectedAmbient (simpleRootLattice 2) = simpleRoot 0
  have hp : dot (simpleRoot 2) outerRootDifference = -2 := by
    norm_num [outerRootDifference, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh := halfOuterPairing_spec (simpleRootLattice 2)
  change dot (simpleRoot 2) outerRootDifference = _ at hh
  rw [hp] at hh
  have hhalf : halfOuterPairing (simpleRootLattice 2) = -1 := by omega
  rw [reflectedAmbient, hhalf]
  apply funext
  intro i
  fin_cases i <;>
    norm_num [simpleRootLattice, outerRootDifference, simpleRoot, sub_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem outerRootReflection_simpleRoot_one :
    outerRootReflectionAddEquiv (simpleRootLattice 1) = simpleRootLattice 1 := by
  apply Subtype.ext
  change reflectedAmbient (simpleRootLattice 1) = simpleRoot 1
  have hp : dot (simpleRoot 1) outerRootDifference = 0 := by
    norm_num [outerRootDifference, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh := halfOuterPairing_spec (simpleRootLattice 1)
  change dot (simpleRoot 1) outerRootDifference = _ at hh
  rw [hp] at hh
  have hhalf : halfOuterPairing (simpleRootLattice 1) = 0 := by omega
  rw [reflectedAmbient, hhalf]
  simp [simpleRootLattice, simpleRoot]

theorem outerRootReflection_simpleRoot_three :
    outerRootReflectionAddEquiv (simpleRootLattice 3) = simpleRootLattice 3 := by
  apply Subtype.ext
  change reflectedAmbient (simpleRootLattice 3) = simpleRoot 3
  have hp : dot (simpleRoot 3) outerRootDifference = 0 := by
    norm_num [outerRootDifference, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh := halfOuterPairing_spec (simpleRootLattice 3)
  change dot (simpleRoot 3) outerRootDifference = _ at hh
  rw [hp] at hh
  have hhalf : halfOuterPairing (simpleRootLattice 3) = 0 := by omega
  rw [reflectedAmbient, hhalf]
  simp [simpleRootLattice, simpleRoot]

/-! ## The second outer transposition -/

/-- Changing the sign of the fourth ambient coordinate preserves the
even-sum lattice and exchanges the two simple roots α₂ and α₃. -/
def signFourthAmbient (x : Ambient) : Ambient :=
  fun i => if i = 3 then -x i else x i

theorem signFourthAmbient_coordinateSum (x : Ambient) :
    coordinateSum (signFourthAmbient x) = coordinateSum x - 2 * x 3 := by
  norm_num [coordinateSum, signFourthAmbient, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> ring

theorem signFourthAmbient_mem (x : Lattice) :
    IsD4 (signFourthAmbient x.1) := by
  change coordinateSum (signFourthAmbient x.1) % 2 = 0
  rw [signFourthAmbient_coordinateSum]
  have hx : coordinateSum x.1 % 2 = 0 := x.2
  omega

def signFourth (x : Lattice) : Lattice :=
  ⟨signFourthAmbient x.1, signFourthAmbient_mem x⟩

theorem signFourth_involutive (x : Lattice) : signFourth (signFourth x) = x := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 3 <;> simp [signFourth, signFourthAmbient, hi]

theorem signFourth_map_add (x y : Lattice) :
    signFourth (x + y) = signFourth x + signFourth y := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 3 <;> simp [signFourth, signFourthAmbient, hi] <;> ring

/-- Additive lattice automorphism for the outer-root transposition
α₂ ↔ α₃. -/
def signFourthAddEquiv : Lattice ≃+ Lattice where
  toFun := signFourth
  invFun := signFourth
  left_inv := signFourth_involutive
  right_inv := signFourth_involutive
  map_add' := signFourth_map_add

theorem signFourth_simpleRoot_zero :
    signFourthAddEquiv (simpleRootLattice 0) = simpleRootLattice 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem signFourth_simpleRoot_one :
    signFourthAddEquiv (simpleRootLattice 1) = simpleRootLattice 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem signFourth_simpleRoot_two :
    signFourthAddEquiv (simpleRootLattice 2) = simpleRootLattice 3 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem signFourth_simpleRoot_three :
    signFourthAddEquiv (simpleRootLattice 3) = simpleRootLattice 2 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem signFourth_preserves_dot_self (x : Lattice) :
    dot (signFourth x).1 (signFourth x).1 = dot x.1 x.1 := by
  norm_num [signFourth, signFourthAmbient, dot, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem signFourth_preserves_root {x : Lattice} (hx : IsD4Root x) :
    IsD4Root (signFourth x) := by
  change dot (signFourth x).1 (signFourth x).1 = 2
  rw [signFourth_preserves_dot_self]
  exact hx

theorem dot_reflected_self (x : Lattice) :
    dot (reflectedAmbient x) (reflectedAmbient x) = dot x.1 x.1 := by
  rw [reflectedAmbient]
  simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right,
    outerRootDifference_norm, halfOuterPairing_spec]
  have hcross : dot x.1 outerRootDifference =
      dot outerRootDifference x.1 := by
    simp [dot, mul_comm]
  rw [← hcross]
  rw [halfOuterPairing_spec]
  ring

theorem outerRootReflection_preserves_root {x : Lattice}
    (hx : IsD4Root x) : IsD4Root (outerRootReflection x) := by
  change dot (reflectedAmbient x) (reflectedAmbient x) = 2
  rw [dot_reflected_self]
  exact hx

/-! ## Basis data needed to extend the two generators to all of S₃ -/

def halfCoordinateSum (x : Lattice) : ℤ :=
  Classical.choose (Int.even_iff.mpr x.2)

theorem halfCoordinateSum_spec (x : Lattice) :
    coordinateSum x.1 = halfCoordinateSum x + halfCoordinateSum x :=
  Classical.choose_spec (Int.even_iff.mpr x.2)

theorem halfCoordinateSum_add (x y : Lattice) :
    halfCoordinateSum (x + y) = halfCoordinateSum x + halfCoordinateSum y := by
  have hsum : coordinateSum (x.1 + y.1) =
      coordinateSum x.1 + coordinateSum y.1 := by
    simp [coordinateSum, Finset.sum_add_distrib]
  have hx := halfCoordinateSum_spec x
  have hy := halfCoordinateSum_spec y
  have hxy := halfCoordinateSum_spec (x + y)
  change coordinateSum (x.1 + y.1) = _ at hxy
  rw [hsum, hx, hy] at hxy
  omega

/-- The four integer coordinates of a lattice element in its simple-root
basis: α₀, α₁, α₂, α₃. -/
def simpleRootCoefficients (x : Lattice) : Fin 4 → ℤ
  | 0 => x.1 0
  | 1 => x.1 0 + x.1 1
  | 2 => halfCoordinateSum x - x.1 3
  | 3 => halfCoordinateSum x

def simpleRootExpansion (x : Lattice) : Lattice :=
  simpleRootCoefficients x 0 • simpleRootLattice 0 +
  simpleRootCoefficients x 1 • simpleRootLattice 1 +
  simpleRootCoefficients x 2 • simpleRootLattice 2 +
  simpleRootCoefficients x 3 • simpleRootLattice 3

theorem simpleRootExpansion_eq (x : Lattice) : simpleRootExpansion x = x := by
  apply Subtype.ext
  funext i
  have hs := halfCoordinateSum_spec x
  have hs' : x.1 0 + x.1 1 + x.1 2 + x.1 3 =
      2 * halfCoordinateSum x := by
    calc
      _ = halfCoordinateSum x + halfCoordinateSum x := by
        simpa [coordinateSum, Fin.sum_univ_four, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] using hs
      _ = 2 * halfCoordinateSum x := by ring
  fin_cases i <;>
    simp [simpleRootExpansion, simpleRootCoefficients, simpleRootLattice,
      simpleRoot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    nlinarith [hs']

def outerSimpleRootIndex : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 3

def outerSimpleRootCoefficient (x : Lattice) (i : Fin 3) : ℤ :=
  simpleRootCoefficients x (outerSimpleRootIndex i)

theorem halfCoordinateSum_simpleRoot (i : Fin 4) :
    halfCoordinateSum (simpleRootLattice i) = if i = 3 then 1 else 0 := by
  fin_cases i
  · have h := halfCoordinateSum_spec (simpleRootLattice 0)
    change coordinateSum (simpleRoot 0) = _ at h
    norm_num [simpleRoot, coordinateSum,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢
    omega
  · have h := halfCoordinateSum_spec (simpleRootLattice 1)
    change coordinateSum (simpleRoot 1) = _ at h
    norm_num [simpleRoot, coordinateSum,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢
    omega
  · have h := halfCoordinateSum_spec (simpleRootLattice 2)
    change coordinateSum (simpleRoot 2) = _ at h
    norm_num [simpleRoot, coordinateSum,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢
    omega
  · have h := halfCoordinateSum_spec (simpleRootLattice 3)
    change coordinateSum (simpleRoot 3) = _ at h
    norm_num [simpleRoot, coordinateSum,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at h ⊢
    omega

theorem simpleRootCoefficients_zero :
    simpleRootCoefficients (simpleRootLattice 0) = ![1, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp only [simpleRootCoefficients, halfCoordinateSum_simpleRoot] <;>
    simp [simpleRootLattice, simpleRoot]

theorem simpleRootCoefficients_one :
    simpleRootCoefficients (simpleRootLattice 1) = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp only [simpleRootCoefficients, halfCoordinateSum_simpleRoot] <;>
    simp [simpleRootLattice, simpleRoot]

theorem simpleRootCoefficients_two :
    simpleRootCoefficients (simpleRootLattice 2) = ![0, 0, 1, 0] := by
  funext i
  fin_cases i <;>
    simp only [simpleRootCoefficients, halfCoordinateSum_simpleRoot] <;>
    simp [simpleRootLattice, simpleRoot]

theorem simpleRootCoefficients_three :
    simpleRootCoefficients (simpleRootLattice 3) = ![0, 0, 0, 1] := by
  funext i
  fin_cases i <;>
    simp only [simpleRootCoefficients, halfCoordinateSum_simpleRoot] <;>
    simp [simpleRootLattice, simpleRoot]

/-- The lattice map specified on the simple-root basis by an arbitrary
permutation of the three outer vertices and the identity on the central
vertex. -/
def outerDiagramMap (σ : Equiv.Perm (Fin 3)) (x : Lattice) : Lattice :=
  simpleRootCoefficients x 1 • simpleRootLattice 1 +
    ∑ i : Fin 3,
      outerSimpleRootCoefficient x i •
        simpleRootLattice (outerSimpleRootIndex (σ i))

theorem outerDiagramMap_central_root (σ : Equiv.Perm (Fin 3)) :
    outerDiagramMap σ (simpleRootLattice 1) = simpleRootLattice 1 := by
  unfold outerDiagramMap outerSimpleRootCoefficient
  rw [simpleRootCoefficients_one]
  simp [outerSimpleRootIndex, Fin.sum_univ_three]

theorem outerDiagramMap_outer_root (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    outerDiagramMap σ (simpleRootLattice (outerSimpleRootIndex i)) =
      simpleRootLattice (outerSimpleRootIndex (σ i)) := by
  fin_cases i
  · change outerDiagramMap σ (simpleRootLattice 0) =
      simpleRootLattice (outerSimpleRootIndex (σ 0))
    unfold outerDiagramMap outerSimpleRootCoefficient
    rw [simpleRootCoefficients_zero]
    simp [outerSimpleRootIndex, Fin.sum_univ_three]
  · change outerDiagramMap σ (simpleRootLattice 2) =
      simpleRootLattice (outerSimpleRootIndex (σ 1))
    unfold outerDiagramMap outerSimpleRootCoefficient
    rw [simpleRootCoefficients_two]
    simp [outerSimpleRootIndex, Fin.sum_univ_three]
  · change outerDiagramMap σ (simpleRootLattice 3) =
      simpleRootLattice (outerSimpleRootIndex (σ 2))
    unfold outerDiagramMap outerSimpleRootCoefficient
    rw [simpleRootCoefficients_three]
    simp [outerSimpleRootIndex, Fin.sum_univ_three]

theorem simpleRootCoefficients_add (x y : Lattice) :
    simpleRootCoefficients (x + y) =
      simpleRootCoefficients x + simpleRootCoefficients y := by
  funext i
  fin_cases i <;>
    simp [simpleRootCoefficients, halfCoordinateSum_add] <;> ring

theorem outerDiagramMap_add (σ : Equiv.Perm (Fin 3)) (x y : Lattice) :
    outerDiagramMap σ (x + y) = outerDiagramMap σ x + outerDiagramMap σ y := by
  apply Subtype.ext
  simp only [outerDiagramMap, simpleRootCoefficients_add,
    outerSimpleRootCoefficient, Pi.add_apply, add_zsmul,
    Finset.sum_add_distrib]
  abel_nf

def outerDiagramHom (σ : Equiv.Perm (Fin 3)) : Lattice →+ Lattice where
  toFun := outerDiagramMap σ
  map_zero' := by
    apply Subtype.ext
    have hz : halfCoordinateSum (0 : Lattice) = 0 := by
      have h := halfCoordinateSum_spec (0 : Lattice)
      simp [coordinateSum] at h
      omega
    have hc : simpleRootCoefficients (0 : Lattice) = 0 := by
      funext i
      fin_cases i <;> simp [simpleRootCoefficients, hz]
    simp [outerDiagramMap, outerSimpleRootCoefficient, hc]
  map_add' := outerDiagramMap_add σ

@[simp] theorem outerDiagramHom_central_root (σ : Equiv.Perm (Fin 3)) :
    outerDiagramHom σ (simpleRootLattice 1) = simpleRootLattice 1 :=
  outerDiagramMap_central_root σ

@[simp] theorem outerDiagramHom_outer_root (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) :
    outerDiagramHom σ (simpleRootLattice (outerSimpleRootIndex i)) =
      simpleRootLattice (outerSimpleRootIndex (σ i)) :=
  outerDiagramMap_outer_root σ i

theorem outerDiagramHom_comp (σ τ : Equiv.Perm (Fin 3)) :
    (outerDiagramHom σ).comp (outerDiagramHom τ) =
      outerDiagramHom (σ * τ) := by
  have hroot (j : Fin 4) :
      outerDiagramHom σ (outerDiagramHom τ (simpleRootLattice j)) =
        outerDiagramHom (σ * τ) (simpleRootLattice j) := by
    fin_cases j
    · change outerDiagramHom σ
        (outerDiagramHom τ (simpleRootLattice (outerSimpleRootIndex 0))) = _
      rw [outerDiagramHom_outer_root τ 0,
        outerDiagramHom_outer_root σ (τ 0)]
      change simpleRootLattice (outerSimpleRootIndex (σ (τ 0))) =
        outerDiagramHom (σ * τ)
          (simpleRootLattice (outerSimpleRootIndex 0))
      rw [outerDiagramHom_outer_root (σ * τ) 0]
      simp only [Equiv.Perm.mul_apply]
    · change outerDiagramHom σ
        (outerDiagramHom τ (simpleRootLattice 1)) =
          outerDiagramHom (σ * τ) (simpleRootLattice 1)
      simp only [outerDiagramHom_central_root]
    · change outerDiagramHom σ
        (outerDiagramHom τ (simpleRootLattice (outerSimpleRootIndex 1))) =
          outerDiagramHom (σ * τ)
            (simpleRootLattice (outerSimpleRootIndex 1))
      rw [outerDiagramHom_outer_root τ 1,
        outerDiagramHom_outer_root σ (τ 1)]
      change simpleRootLattice (outerSimpleRootIndex (σ (τ 1))) =
        outerDiagramHom (σ * τ)
          (simpleRootLattice (outerSimpleRootIndex 1))
      rw [outerDiagramHom_outer_root (σ * τ) 1]
      simp only [Equiv.Perm.mul_apply]
    · change outerDiagramHom σ
        (outerDiagramHom τ (simpleRootLattice (outerSimpleRootIndex 2))) =
          outerDiagramHom (σ * τ)
            (simpleRootLattice (outerSimpleRootIndex 2))
      rw [outerDiagramHom_outer_root τ 2,
        outerDiagramHom_outer_root σ (τ 2)]
      change simpleRootLattice (outerSimpleRootIndex (σ (τ 2))) =
        outerDiagramHom (σ * τ)
          (simpleRootLattice (outerSimpleRootIndex 2))
      rw [outerDiagramHom_outer_root (σ * τ) 2]
      simp only [Equiv.Perm.mul_apply]
  apply AddMonoidHom.ext
  intro x
  rw [← simpleRootExpansion_eq x]
  simp only [AddMonoidHom.comp_apply, map_add, map_zsmul,
    simpleRootExpansion]
  rw [hroot 0, hroot 1, hroot 2, hroot 3]

theorem outerDiagramHom_one (x : Lattice) : outerDiagramHom 1 x = x := by
  have hroot (j : Fin 4) :
      outerDiagramHom 1 (simpleRootLattice j) = simpleRootLattice j := by
    fin_cases j
    · change outerDiagramHom 1
        (simpleRootLattice (outerSimpleRootIndex 0)) = _
      rw [outerDiagramHom_outer_root 1 0]
      simp [outerSimpleRootIndex]
    · exact outerDiagramHom_central_root 1
    · change outerDiagramHom 1
        (simpleRootLattice (outerSimpleRootIndex 1)) = _
      rw [outerDiagramHom_outer_root 1 1]
      simp [outerSimpleRootIndex]
    · change outerDiagramHom 1
        (simpleRootLattice (outerSimpleRootIndex 2)) = _
      rw [outerDiagramHom_outer_root 1 2]
      simp [outerSimpleRootIndex]
  rw [← simpleRootExpansion_eq x]
  simp only [simpleRootExpansion, map_add, map_zsmul]
  rw [hroot 0, hroot 1, hroot 2, hroot 3]

theorem outerDiagramHom_one_eq :
    outerDiagramHom 1 = AddMonoidHom.id Lattice := by
  apply AddMonoidHom.ext
  intro x
  exact outerDiagramHom_one x

def outerDiagramEquiv (σ : Equiv.Perm (Fin 3)) : Lattice ≃+ Lattice where
  toFun := outerDiagramHom σ
  invFun := outerDiagramHom σ⁻¹
  left_inv := by
    intro x
    have h := outerDiagramHom_comp σ⁻¹ σ
    have hp : σ⁻¹ * σ = 1 := by group
    rw [hp, outerDiagramHom_one_eq] at h
    have hx := congrArg (fun f : Lattice →+ Lattice => f x) h
    simpa [AddMonoidHom.comp_apply] using hx
  right_inv := by
    intro x
    have h := outerDiagramHom_comp σ σ⁻¹
    have hp : σ * σ⁻¹ = 1 := by group
    rw [hp, outerDiagramHom_one_eq] at h
    have hx := congrArg (fun f : Lattice →+ Lattice => f x) h
    simpa [AddMonoidHom.comp_apply] using hx
  map_add' := (outerDiagramHom σ).map_add

/-- Homomorphism candidate from outer-node permutations to additive
automorphisms of the concrete lattice. Injectivity and root-system isometry
are separate properties and are not asserted here. -/
def outerDiagramAction :
    Equiv.Perm (Fin 3) →* Multiplicative (AddAut Lattice) where
  toFun σ := Multiplicative.ofAdd (outerDiagramEquiv σ)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply AddEquiv.ext
    intro x
    change outerDiagramHom 1 x = x
    exact outerDiagramHom_one x
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro x
    change outerDiagramHom (σ * τ) x = outerDiagramHom σ (outerDiagramHom τ x)
    have h := congrArg (fun f : Lattice →+ Lattice => f x)
      (outerDiagramHom_comp σ τ)
    simpa [AddMonoidHom.comp_apply] using h.symm

@[simp] theorem outerDiagramAction_apply (σ : Equiv.Perm (Fin 3))
    (x : Lattice) :
    ((outerDiagramAction σ : Multiplicative (AddAut Lattice)).toAdd) x =
      outerDiagramHom σ x := rfl

theorem outerDiagramAction_simpleRoot_central (σ : Equiv.Perm (Fin 3)) :
    ((outerDiagramAction σ : Multiplicative (AddAut Lattice)).toAdd)
      (simpleRootLattice 1) = simpleRootLattice 1 :=
  outerDiagramHom_central_root σ

theorem outerDiagramAction_simpleRoot_outer (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) :
    ((outerDiagramAction σ : Multiplicative (AddAut Lattice)).toAdd)
      (simpleRootLattice (outerSimpleRootIndex i)) =
        simpleRootLattice (outerSimpleRootIndex (σ i)) :=
  outerDiagramHom_outer_root σ i

end InfoGeometry.RootSystem.D4DynkinOuterReflectionCandidate

end noncomputable section

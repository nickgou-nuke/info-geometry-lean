import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-!
# Native para-Kaehler algebra on the active `(3 + 3)` carrier

The active carrier is the pair of real vector triples already used by the
Cartesian/Zorn coordinate owner.  This file records the neutral pairing, its
skew companion, the product structure, and the exact Lagrangian graph
criterion.  It does not introduce a manifold, a connection, or an analytic
Hessian theorem.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionActiveParaKahler

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev Vec3 := Fin 3 → ℝ
abbrev Active := Vec3 × Vec3

def vecDot (x y : Vec3) : ℝ := ∑ i, x i * y i

theorem vecDot_swap (x y : Vec3) : vecDot x y = vecDot y x := by
  unfold vecDot
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

theorem vecDot_add_left (x y z : Vec3) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  unfold vecDot
  simp [add_mul, Finset.sum_add_distrib]

theorem vecDot_add_right (x y z : Vec3) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  unfold vecDot
  simp [mul_add, Finset.sum_add_distrib]

theorem vecDot_smul_left (r : ℝ) (x y : Vec3) :
    vecDot (r • x) y = r * vecDot x y := by
  unfold vecDot
  simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

theorem vecDot_smul_right (r : ℝ) (x y : Vec3) :
    vecDot x (r • y) = r * vecDot x y := by
  unfold vecDot
  simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

def neutralPair (x y : Active) : ℝ := vecDot x.1 y.2 + vecDot x.2 y.1

def symplecticPair (x y : Active) : ℝ := vecDot x.1 y.2 - vecDot x.2 y.1

/-- The constant mixed potential whose raw polarization is the neutral
pairing.  This is the finite linear para-Hessian model; no differentiable
manifold structure is assumed here. -/
def mixedPotential (x : Active) : ℝ := vecDot x.1 x.2

theorem mixedPotential_rawPolarization (x y : Active) :
    mixedPotential (x + y) - mixedPotential x - mixedPotential y =
      neutralPair x y := by
  change vecDot (x.1 + y.1) (x.2 + y.2) - vecDot x.1 x.2 - vecDot y.1 y.2 =
    vecDot x.1 y.2 + vecDot x.2 y.1
  rw [vecDot_add_right (x.1 + y.1) x.2 y.2]
  rw [vecDot_add_left x.1 y.1 x.2, vecDot_add_left x.1 y.1 y.2]
  rw [vecDot_swap y.1 x.2]
  abel

def paraProduct : Active →ₗ[ℝ] Active where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      simp [neg_add, add_comm]
  map_smul' r x := by ext <;> simp

@[simp] theorem paraProduct_apply (x : Active) :
    paraProduct x = (x.1, -x.2) := rfl

theorem paraProduct_sq : paraProduct * paraProduct = 1 := by
  apply LinearMap.ext
  intro x
  change paraProduct (paraProduct x) = x
  simp [paraProduct]

theorem neutralPair_swap (x y : Active) :
    neutralPair x y = neutralPair y x := by
  unfold neutralPair
  rw [vecDot_swap x.2 y.1, vecDot_swap y.2 x.1]
  abel

theorem symplecticPair_swap (x y : Active) :
    symplecticPair y x = -symplecticPair x y := by
  unfold symplecticPair vecDot
  simp [mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem neutralPair_plus_isotropic (x y : Vec3) :
    neutralPair (x, 0) (y, 0) = 0 := by
  simp [neutralPair, vecDot]

theorem neutralPair_minus_isotropic (x y : Vec3) :
    neutralPair (0, x) (0, y) = 0 := by
  simp [neutralPair, vecDot]

theorem neutralPair_paraProduct (x y : Active) :
    neutralPair (paraProduct x) (paraProduct y) = -neutralPair x y := by
  unfold neutralPair paraProduct vecDot
  simp [sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc]

theorem symplecticPair_paraProduct_compat (x y : Active) :
    symplecticPair (paraProduct x) (paraProduct y) =
      -symplecticPair x y := by
  unfold symplecticPair paraProduct vecDot
  simp [sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc]

theorem symplecticPair_paraProduct (x y : Active) :
    symplecticPair (paraProduct x) (paraProduct y) = -symplecticPair x y := by
  unfold symplecticPair paraProduct vecDot
  simp [sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc]

def graph (A : Vec3 →ₗ[ℝ] Vec3) (x : Vec3) : Active := (x, A x)

theorem neutralPair_graph (A : Vec3 →ₗ[ℝ] Vec3) (x y : Vec3) :
    neutralPair (graph A x) (graph A y) =
      vecDot x (A y) + vecDot (A x) y := by
  rfl

theorem symplecticPair_graph_eq_zero
    (A : Vec3 →ₗ[ℝ] Vec3)
    (hA : ∀ x y : Vec3, vecDot x (A y) = vecDot (A x) y)
    (x y : Vec3) :
    symplecticPair (graph A x) (graph A y) = 0 := by
  unfold symplecticPair graph
  rw [hA]
  ring

def identityGraph (x : Vec3) : Active := (x, x)

theorem identityGraph_isotropic (x y : Vec3) :
    symplecticPair (identityGraph x) (identityGraph y) = 0 := by
  exact symplecticPair_graph_eq_zero LinearMap.id (by
    intro x y
    simp [vecDot, mul_comm]) x y

theorem neutralPair_identityGraph (x y : Vec3) :
    neutralPair (identityGraph x) (identityGraph y) =
      2 * vecDot x y := by
  unfold neutralPair identityGraph
  ring

def circularChange : Active ≃ₗ[ℝ] Active where
  toFun x := (x.1 + x.2, x.2 - x.1)
  invFun x := ((x.1 - x.2) / 2, (x.1 + x.2) / 2)
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp [sub_eq_add_neg] <;> ring
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [sub_eq_add_neg] <;> ring
  map_add' x y := by
    apply Prod.ext <;> funext i <;> simp [sub_eq_add_neg] <;> ring
  map_smul' r x := by
    apply Prod.ext <;> funext i <;> simp [sub_eq_add_neg] <;> ring

@[simp] theorem circularChange_apply (x : Active) :
    circularChange x = (x.1 + x.2, x.2 - x.1) := rfl

def activeExchange : Active →ₗ[ℝ] Active where
  toFun x := (x.2, x.1)
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> rfl

@[simp] theorem activeExchange_apply (x : Active) :
    activeExchange x = (x.2, x.1) := rfl

theorem circularChange_intertwines_exchange (x : Active) :
    circularChange (activeExchange x) = paraProduct (circularChange x) := by
  apply Prod.ext <;> funext i <;>
    simp [circularChange, activeExchange, paraProduct, sub_eq_add_neg, add_comm]

def activeCartesian (x : Active) : CartesianCoordinates :=
  ((0, x.1), (0, x.2))

theorem detZ_activeCartesian (x : Active) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (cartesianZornLinearEquiv (activeCartesian x)) =
      vecDot x.1 x.1 - vecDot x.2 x.2 := by
  rw [detZ_cartesianZornLinearEquiv]
  simp [activeCartesian, quaternionNorm, vecDot,
    InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]

theorem neutralPair_circular_self (x : Active) :
    neutralPair (circularChange x) (circularChange x) =
      -2 * (vecDot x.1 x.1 - vecDot x.2 x.2) := by
  unfold neutralPair circularChange vecDot
  simp [sub_eq_add_neg, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem detZ_activeCartesian_eq_neg_half_neutralPair (x : Active) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (cartesianZornLinearEquiv (activeCartesian x)) =
      -(1 / 2 : ℝ) *
        neutralPair (circularChange x) (circularChange x) := by
  rw [detZ_activeCartesian, neutralPair_circular_self]
  ring

/-! ## Algebraic mixed-potential readout

This is the finite algebraic shadow of a mixed Hessian potential.  It is
stated only with the existing dot product and neutral pairing; no analytic
derivative or manifold structure is introduced here.
-/

def activePotential (x : Active) : ℝ :=
  vecDot x.1 x.2

def activeMixedHessian (x y : Active) : ℝ :=
  neutralPair x y

noncomputable def activeMixedHessianBilin : LinearMap.BilinForm ℝ Active :=
  LinearMap.mk₂ ℝ
    (fun x y => neutralPair x y)
    (fun x₁ x₂ y => by
      simp [neutralPair, vecDot, Finset.sum_add_distrib, mul_add, add_mul,
        mul_comm, add_comm, add_left_comm, add_assoc])
    (fun r x y => by
      simp [neutralPair, vecDot_smul_left, vecDot_smul_right, mul_comm]
      ring)
    (fun x y₁ y₂ => by
      simp [neutralPair, vecDot, Finset.sum_add_distrib, mul_add, add_mul,
        mul_comm, add_comm, add_left_comm, add_assoc])
    (fun r x y => by
      simp [neutralPair, vecDot_smul_left, vecDot_smul_right, mul_comm]
      ring)

@[simp] theorem activeMixedHessianBilin_apply (x y : Active) :
    activeMixedHessianBilin x y = activeMixedHessian x y := rfl

def activePlus (x : Vec3) : Active := (x, 0)

def activeMinus (y : Vec3) : Active := (0, y)

theorem active_decompose (x : Active) :
    activePlus x.1 + activeMinus x.2 = x := by
  ext i <;> simp [activePlus, activeMinus]

theorem activeExchange_plus (x : Vec3) :
    activeExchange (activePlus x) = activeMinus x := by
  rfl

theorem activeExchange_minus (x : Vec3) :
    activeExchange (activeMinus x) = activePlus x := by
  rfl

theorem activeMixedHessianBilin_plus_plus (x y : Vec3) :
    activeMixedHessianBilin (activePlus x) (activePlus y) = 0 := by
  simp [activeMixedHessianBilin, activePlus, neutralPair, vecDot]

theorem activeMixedHessianBilin_minus_minus (x y : Vec3) :
    activeMixedHessianBilin (activeMinus x) (activeMinus y) = 0 := by
  simp [activeMixedHessianBilin, activeMinus, neutralPair, vecDot]

theorem activeMixedHessianBilin_plus_minus (x y : Vec3) :
    activeMixedHessianBilin (activePlus x) (activeMinus y) = vecDot x y := by
  simp [activeMixedHessianBilin, activePlus, activeMinus, neutralPair, vecDot]

theorem activeMixedHessianBilin_minus_plus (x y : Vec3) :
    activeMixedHessianBilin (activeMinus x) (activePlus y) = vecDot y x := by
  simp [activeMixedHessianBilin, activePlus, activeMinus, neutralPair, vecDot,
    mul_comm]

theorem activePotential_swap (x : Active) :
    activePotential (x.2, x.1) = activePotential x := by
  simp [activePotential, vecDot, mul_comm]

theorem activeMixedHessian_swap (x y : Active) :
    activeMixedHessian x y = activeMixedHessian y x := by
  exact neutralPair_swap x y

theorem activeMixedHessian_self (x : Active) :
    activeMixedHessian x x = 2 * activePotential x := by
  change vecDot x.1 x.2 + vecDot x.2 x.1 = 2 * vecDot x.1 x.2
  rw [vecDot_swap x.2 x.1]
  ring

theorem activePotential_paraProduct (x : Active) :
    activePotential (paraProduct x) = -activePotential x := by
  simp [activePotential, paraProduct, vecDot]

theorem activeMixedHessian_graph (A : Vec3 →ₗ[ℝ] Vec3)
    (x y : Vec3) :
    activeMixedHessian (graph A x) (graph A y) =
      vecDot x (A y) + vecDot (A x) y := by
  rfl

theorem activeMixedHessian_identityGraph (x y : Vec3) :
    activeMixedHessian (identityGraph x) (identityGraph y) =
      2 * vecDot x y := by
  exact neutralPair_identityGraph x y

theorem activePotential_identityGraph (x : Vec3) :
    activePotential (identityGraph x) = vecDot x x := by
  rfl

theorem activeMixedHessian_circular_self (x : Active) :
    activeMixedHessian (circularChange x) (circularChange x) =
      -2 * (vecDot x.1 x.1 - vecDot x.2 x.2) := by
  exact neutralPair_circular_self x

end InfoGeometry.Lie.SplitOctonionActiveParaKahler

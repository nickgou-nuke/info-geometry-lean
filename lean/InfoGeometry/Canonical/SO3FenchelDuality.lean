import Mathlib
import InfoGeometry.Canonical.LieGeometricDuality

/-!
# InfoGeometry.Canonical.SO3FenchelDuality

Concrete `SO(3)` primal/dual witness for the Lie/Fenchel dictionary.

Highlights:
* `so3Action` is the coadjoint-adjoint action by matrix multiplication,
* dot-product and quadratic Casimir are `SO(3)` invariants,
* kinetic potential and Legendre-pairing setup for the isotropic inertia case,
* KKS form written with the 3D cross product.
-/

noncomputable section

namespace InfoGeometry.Canonical.SO3FenchelDuality

open InfoGeometry.Canonical.LieGeometricDuality

open scoped Matrix

abbrev V3 : Type := Fin 3 → ℝ
abbrev SO3 : Type := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- `SO(3)` action on vectors and hence on momentum coordinates. -/
def so3Action (R : SO3) (x : V3) : V3 := (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x

/-- Dot-product is `SO(3)`-invariant. -/
theorem so3_dotProduct_invariant (R : SO3) (x y : V3) :
    so3Action R x ⬝ᵥ so3Action R y = x ⬝ᵥ y := by
  have hR : (R : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  have hmul : (R : Matrix (Fin 3) (Fin 3) ℝ).transpose * (R : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin 3) (R := ℝ)).1 hR
  change (R : Matrix (Fin 3) (Fin 3) ℝ).mulVec x ⬝ᵥ (R : Matrix (Fin 3) (Fin 3) ℝ).mulVec y = x ⬝ᵥ y
  calc
    (R : Matrix (Fin 3) (Fin 3) ℝ).mulVec x ⬝ᵥ (R : Matrix (Fin 3) (Fin 3) ℝ).mulVec y
        = Matrix.vecMul ((R : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) (R : Matrix (Fin 3) (Fin 3) ℝ) ⬝ᵥ y := by
          simpa using
            (Matrix.dotProduct_mulVec ((R : Matrix (Fin 3) (Fin 3) ℝ).mulVec x)
              (R : Matrix (Fin 3) (Fin 3) ℝ) y)
    _ = Matrix.vecMul x ((R : Matrix (Fin 3) (Fin 3) ℝ).transpose * (R : Matrix (Fin 3) (Fin 3) ℝ) )
          ⬝ᵥ y := by
          simpa using
            congrArg (fun z => z ⬝ᵥ y)
              (Matrix.vecMul_mulVec (A := (R : Matrix (Fin 3) (Fin 3) ℝ))
                (B := (R : Matrix (Fin 3) (Fin 3) ℝ)) x)
    _ = Matrix.vecMul x 1 ⬝ᵥ y := by rw [hmul]
    _ = x ⬝ᵥ y := by simp [Matrix.vecMul_one]

/-- Quadratic Casimir / squared spin magnitude. -/
def casimir (L : V3) : ℝ := L ⬝ᵥ L

/-- The Casimir is constant on coadjoint-orbit trajectories. -/
theorem casimir_invariant_on_orbit (L0 : V3) (R : SO3) :
    casimir (so3Action R L0) = casimir L0 := by
  simp [casimir, so3_dotProduct_invariant]

/-- Coadjoint orbit as the `so3Action`-orbit in `V3`. -/
def coadjointOrbit (L0 : V3) : Set V3 := Set.range (fun R : SO3 => so3Action R L0)

/-- Every point in the `SO(3)` coadjoint orbit stays on the same Casimir sphere. -/
theorem coadjoint_orbit_subset_casimir_sphere (L0 : V3) :
    ∀ {x}, x ∈ coadjointOrbit L0 → casimir x = casimir L0 := by
  intro x hx
  rcases hx with ⟨R, rfl⟩
  exact casimir_invariant_on_orbit L0 R

/-- Isotropic kinetic potential on `so(3)` vectors (angular velocity coordinates). -/
def kinetic (I : ℝ) (ω : V3) : ℝ := (I / 2) * (ω ⬝ᵥ ω)

/-- Dual quadratic potential (angular momentum coordinates, same inertia `I`). -/
def dualQuadratic (I : ℝ) (L : V3) : ℝ := (1 / (2 * I)) * (L ⬝ᵥ L)

/-- The coadjoint/primal pairing in this basis is the Euclidean pairing. -/
def so3Pairing (L ω : V3) : ℝ := L ⬝ᵥ ω

/-- Linear moment map `L = I ω` for isotropic inertia. -/
def angularMomentum (I : ℝ) (ω : V3) : V3 := I • ω

theorem angularMomentum_injective (I : ℝ) (hI : I ≠ 0) : Function.LeftInverse (fun L : V3 => (1 / I) • L) (angularMomentum I) := by
  intro ω
  simp [angularMomentum, hI, smul_smul]

theorem momentum_from_velocity_pairing (I : ℝ) (ω : V3) :
    angularMomentum I ω ⬝ᵥ ω = (2 : ℝ) * kinetic I ω := by
  simp [angularMomentum, kinetic, dotProduct, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  ring_nf

/-- `SO(3)` invariance of quadratic momentum/velocity potentials (no dependence on axis choice). -/
theorem kinetic_invariant (I : ℝ) (R : SO3) (ω : V3) :
    kinetic I (so3Action R ω) = kinetic I ω := by
  simp [kinetic, so3_dotProduct_invariant]

theorem dual_invariant (I : ℝ) (R : SO3) (L : V3) :
    dualQuadratic I (so3Action R L) = dualQuadratic I L := by
  simp [dualQuadratic, so3_dotProduct_invariant]

/-- KKS 2-form on a dual orbit (in coordinates): `ωₗ(X,Y)=⟨L,[X,Y]⟩ = L·(X×Y)`. -/
def kksForm (L : V3) : V3 → V3 → ℝ :=
  fun X Y => L ⬝ᵥ (X ⨯₃ Y)

/-- KKS form is skew-symmetric in the two arguments. -/
theorem kksForm_skew (L : V3) (X Y : V3) : kksForm L X Y = -kksForm L Y X := by
  unfold kksForm
  have hneg : (L ⬝ᵥ (Y ⨯₃ X)) = -(L ⬝ᵥ (X ⨯₃ Y)) := by
    simpa using (dotProduct_neg L (X ⨯₃ Y))
  linarith

/-- Unit-sphere Bregman picture (spherical slice at fixed Casimir level):
The following identity expresses the standard tangent-space metric of the quadratic
potential as the ambient weighted Euclidean form restricted to the orbit.
-/
def dualBregman (I : ℝ) (L1 L2 : V3) : ℝ :=
  dualQuadratic I L1 - dualQuadratic I L2 - ((L2) ⬝ᵥ (L1 - L2)) / I

/-- Base-point check for the dual Bregman gap. -/
theorem dualBregman_zero_diag (I : ℝ) (L : V3) : dualBregman I L L = 0 := by
  simp [dualBregman]

/-- Closed-form dual Bregman divergence: quadratic norm-square in the gap. -/
theorem dualBregman_eq_norm_sq (I : ℝ) (L1 L2 : V3) :
    dualBregman I L1 L2 = (1 / (2 * I)) * ((L1 - L2) ⬝ᵥ (L1 - L2)) := by
  unfold dualBregman dualQuadratic
  have hR : (L2 ⬝ᵥ (L1 - L2)) = L2 ⬝ᵥ L1 - L2 ⬝ᵥ L2 := by
    simp [dotProduct_sub]
  have hN1 : (L1 - L2) ⬝ᵥ (L1 - L2) =
      (L1 ⬝ᵥ L1 - L1 ⬝ᵥ L2) - (L2 ⬝ᵥ L1 - L2 ⬝ᵥ L2) := by
    rw [sub_dotProduct]
    simp [dotProduct_sub]
  have hN : (L1 - L2) ⬝ᵥ (L1 - L2) = L1 ⬝ᵥ L1 + L2 ⬝ᵥ L2 - 2 * (L1 ⬝ᵥ L2) := by
    rw [hN1]
    rw [dotProduct_comm L2 L1]
    ring
  rw [hR, hN]
  rw [dotProduct_comm L2 L1]
  ring_nf

/-- Conjugate coadjoint orbit converse (finite-dimensional witness): equal Casimir implies same `SO(3)` orbit. -/
theorem so3_converse_equal_casimir (x y : V3) (h : casimir x = casimir y) :
    ∃ Q : SO3, so3Action Q x = y := by
  let xE : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm x
  let yE : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm y
  let b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := EuclideanSpace.basisFun (Fin 3) ℝ

  have hnorm_sq : ‖xE‖ ^ 2 = ‖yE‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simpa [pow_two] using h
  have hnorm : ‖xE‖ = ‖yE‖ := by
    nlinarith [hnorm_sq, norm_nonneg xE, norm_nonneg yE]

  by_cases hxy : xE = yE
  · refine ⟨1, ?_⟩
    have hxy' : x = y := by
      have := congrArg (EuclideanSpace.equiv (Fin 3) ℝ) hxy
      simpa [xE, yE] using this
    simpa [so3Action, hxy']

  · have hdiff_ne : xE - yE ≠ 0 := sub_ne_zero.mpr hxy
    let K0 : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := ℝ ∙ (xE - yE)
    let R1 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      K0ᗮ.reflection

    have hR1xy : R1 xE = yE := by
      simpa [R1, K0] using (Submodule.reflection_sub (v := xE) (w := yE) hnorm)

    have hy_nonzero : yE ≠ 0 := by
      intro hy
      have hx0 : xE = 0 := by
        apply norm_eq_zero.mp
        have : ‖xE‖ = 0 := by simpa [hy] using hnorm
        simpa using this
      exact hxy (by simpa [hy] using hx0)

    let u : EuclideanSpace ℝ (Fin 3) :=
      if h0 : yE 0 = 0 then EuclideanSpace.single 0 1
      else if h1 : yE 1 = 0 then EuclideanSpace.single 1 1
      else EuclideanSpace.single 2 1

    have hu_notin : u ∉ (ℝ ∙ yE) := by
      classical
      by_cases h0 : yE 0 = 0
      · intro hu
        rw [Submodule.mem_span_singleton] at hu
        rcases hu with ⟨a, ha⟩
        have hcoord : a * yE 0 = (1 : ℝ) := by
          simpa [u, h0] using congrArg (fun z => z 0) ha
        have : (0 : ℝ) = (1 : ℝ) := by simpa [h0] using hcoord
        norm_num at this
      · by_cases h1 : yE 1 = 0
        · intro hu
          rw [Submodule.mem_span_singleton] at hu
          rcases hu with ⟨a, ha⟩
          have hcoord : a * yE 1 = (1 : ℝ) := by
            simpa [u, h0, h1] using congrArg (fun z => z 1) ha
          have : (0 : ℝ) = (1 : ℝ) := by simpa [h1] using hcoord
          norm_num at this
        · intro hu
          rw [Submodule.mem_span_singleton] at hu
          rcases hu with ⟨a, ha⟩
          have hcoord0 : a * yE 0 = 0 := by
            simpa [u, h0, h1] using congrArg (fun z => z 0) ha
          have ha0 : a = 0 := by
            exact (mul_eq_zero.mp hcoord0).resolve_right h0
          have hcoord2 : a * yE 2 = (1 : ℝ) := by
            simpa [u, h0, h1] using congrArg (fun z => z 2) ha
          have : (0 : ℝ) = (1 : ℝ) := by simpa [ha0] using hcoord2
          norm_num at this

    have hu_ne : u ≠ 0 := by
      classical
      by_cases h0 : yE 0 = 0
      · simp [u, h0]
      · by_cases h1 : yE 1 = 0
        · simp [u, h0, h1]
        · simp [u, h0, h1]

    let K2 : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
      Submodule.span ℝ (Set.range (![yE, u]))

    have hpair : LinearIndependent ℝ (![yE, u] : Fin 2 → EuclideanSpace ℝ (Fin 3)) := by
      exact (LinearIndependent.pair_iff' (x := yE) (y := u) hy_nonzero).2 (by
        intro a hmul
        exact hu_notin (by
          rw [Submodule.mem_span_singleton]
          exact ⟨a, hmul⟩))

    have hK2dim : Module.finrank ℝ ↥K2 = 2 := by
      simpa [K2] using (finrank_span_eq_card hpair)

    let R2 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) := K2.reflection

    have hyfix : R2 yE = yE := by
      have hy_mem : yE ∈ K2 := by
        exact Submodule.subset_span (show yE ∈ Set.range (![yE, u]) from ⟨0, by simp⟩)
      simpa [R2, K2] using (Submodule.reflection_mem_subspace_eq_self (K := K2) hy_mem)

    have hdetR1' :
        LinearMap.det (R1.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
          = (-1) ^ Module.finrank ℝ ↥K0ᗮᗮ := by
      haveI : FiniteDimensional ℝ ↥K0ᗮ := inferInstance
      simpa [R1, K0] using (Submodule.det_reflection (K := K0ᗮ))

    have hK0dim : Module.finrank ℝ ↥K0 = 1 := by
      simpa [K0] using (finrank_span_singleton hdiff_ne)
    have hK0orth : K0ᗮᗮ = K0 := by
      simpa [K0] using (Submodule.orthogonal_orthogonal (K := K0))

    have hdetR1 :
        LinearMap.det (R1.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = -1 := by
      rw [hdetR1']
      rw [hK0orth]
      rw [hK0dim]
      norm_num

    have hdetR2' :
        LinearMap.det (R2.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
          = (-1) ^ Module.finrank ℝ ↥K2ᗮ := by
      haveI : FiniteDimensional ℝ ↥K2 := inferInstance
      simpa [R2, K2] using (Submodule.det_reflection (K := K2))

    have hK2orth : Module.finrank ℝ ↥K2ᗮ = 1 := by
      have hsum : Module.finrank ℝ ↥K2 + Module.finrank ℝ ↥K2ᗮ = 3 := by
        simpa using (K2.finrank_add_finrank_orthogonal)
      nlinarith [hsum, hK2dim]

    have hdetR2 :
        LinearMap.det (R2.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = -1 := by
      rw [hdetR2']
      rw [hK2orth]
      norm_num

    let R : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (R2.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).comp
        (R1.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))

    have hRxy : R xE = yE := by
      change (R2.toLinearEquiv (R1.toLinearEquiv xE)) = yE
      have hR1xy' : R1.toLinearEquiv xE = yE := by
        simpa using (show R1 xE = yE from hR1xy)
      rw [hR1xy']
      simpa using hyfix

    have hdetR : LinearMap.det R = 1 := by
      unfold R
      rw [LinearMap.det_comp, hdetR2, hdetR1]
      norm_num

    have hinner : ∀ v w : EuclideanSpace ℝ (Fin 3), inner ℝ (R v) (R w) = inner ℝ v w := by
      intro v w
      calc
        inner ℝ (R v) (R w) = inner ℝ (R2 (R1 v)) (R2 (R1 w)) := by
          rfl
        _ = inner ℝ (R1 v) (R1 w) := by
          simpa using (R2.inner_map_map (R1 v) (R1 w))
        _ = inner ℝ v w := by
          simpa using (R1.inner_map_map v w)

    let A : Matrix (Fin 3) (Fin 3) ℝ :=
      LinearMap.toMatrix b.toBasis b.toBasis R

    have hb : ∀ i j : Fin 3, inner ℝ (b i) (b j) = if i = j then (1 : ℝ) else 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp [b]
      · simpa [hij] using (b.orthonormal.2 hij)

    have hA_orth : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff']
      ext i j
      calc
        (Aᵀ * A) i j = ∑ x : Fin 3, A x i * A x j := by
          simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ = ∑ x : Fin 3,
            (b.repr (R (b i))).ofLp x * (b.repr (R (b j))).ofLp x := by
          simp [A, LinearMap.toMatrix_apply]
        _ = inner ℝ (R (b i)) (R (b j)) := by
          calc
            (∑ x : Fin 3, (b.repr (R (b i))).ofLp x * (b.repr (R (b j))).ofLp x)
                = ∑ x : Fin 3,
                    inner ℝ (b x) (R (b i)) * inner ℝ (b x) (R (b j)) := by
                  simp [OrthonormalBasis.repr_apply_apply]
            _ = inner ℝ (R (b i)) (R (b j)) := by
                  simpa [real_inner_comm] using (b.sum_inner_mul_inner (R (b i)) (R (b j)))
        _ = inner ℝ (b i) (b j) := by
          simpa using (hinner (b i) (b j))
        _ = (if i = j then (1 : ℝ) else 0) := by
          simpa using hb i j
        _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
          simp [Matrix.one_apply]

    have hdetA : A.det = 1 := by
      have hdetA' :
          A.det =
            LinearMap.det R := by
        simpa [A] using (LinearMap.det_toMatrix b.toBasis b.toBasis R)
      rw [hdetA', hdetR]

    have hmul' : A *ᵥ (b.toBasis.repr xE) = b.toBasis.repr (R xE) := by
      simpa [A] using
        (LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis R xE)

    have hmul : A *ᵥ (b.toBasis.repr xE) = b.toBasis.repr yE := by
      simpa [hRxy] using hmul'

    have hxrepr : (b.toBasis.repr xE) = x := by
      ext i
      simp [b, xE]
    have hyrepr : (b.toBasis.repr yE) = y := by
      ext i
      simp [b, yE]

    refine ⟨⟨A, (Matrix.mem_specialOrthogonalGroup_iff).2 ⟨hA_orth, hdetA⟩⟩, ?_⟩
    change (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = y
    simpa [so3Action, hxrepr, hyrepr] using hmul

/-- Tangent identification by cross-product: a coadjoint-orbit tangent at `L` is `L × ξ`. -/
def tangentVectorFromGenerator (L ξ : V3) : V3 := L ⨯₃ ξ


section LieBridge

local instance : LieRing V3 := Cross.lieRing

local instance : LieAlgebra ℝ V3 := by
  refine { lie_smul := ?_ }
  intro a x y
  change x ⨯₃ (a • y) = a • (x ⨯₃ y)
  simpa using (crossProduct x).map_smul a y

/-- Bundle SO(3) vectors into the abstract dual via Euclidean pairing. -/
def so3ToDual (L : V3) : LieDual V3 :=
  { toFun := fun Z => L ⬝ᵥ Z
    map_add' := by
      intro Z₁ Z₂
      simp [dotProduct_add]
    map_smul' := by
      intro a Z
      simpa using (dotProduct_smul a L Z) }

/-- Abstract coadjoint pairing is function application. -/
theorem so3_coadjointPairing_eq_apply (ξ : LieDual V3) (X : V3) :
    coadjointPairing ξ X = ξ.toFun X := by
  rfl

/-- Abstract KKS form matches the explicit `\u27C3₃` bracket form for this `LieRing` instance. -/
theorem so3_kksForm_eq_lieKks (ξ : LieDual V3) (X Y : V3) :
    LieGeometricDuality.kksForm ξ X Y = ξ.toFun (X ⨯₃ Y) := by
  rfl

/-- Concrete SO(3) KKS form is the abstract KKS form under this embedding. -/
theorem so3_kksForm_as_lieKks (L X Y : V3) :
    kksForm L X Y = LieGeometricDuality.kksForm (so3ToDual L) X Y := by
  rfl

end LieBridge

end InfoGeometry.Canonical.SO3FenchelDuality

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Jean-Marie Souriau, MDPAS 1974: finite spin-particle algebra

Source digest: `MDPAS-JMSouriau.pdf`, *Modèle de particule à spin dans le
champ électromagnétique et gravitationnel*.

The paper contains global relativistic, distributional, symplectic and
prequantization claims.  This file formalizes only a kernel-checkable finite
algebraic spine over `ℚ`:

* antisymmetric spin/electromagnetic tensors;
* a simple decomposable spin bivector `I ∧ J`;
* transversality/contraction identities used in spin supplementary conditions;
* Lorentz-force power conservation for antisymmetric fields;
* exact rational mass-shell and gyromagnetic finite readouts.

No smooth spacetime, distribution theory, global symplectic form, or Dirac
quantization theorem is claimed here.
-/

namespace InfoGeometry
namespace Physics
namespace MDPASJMSouriau

abbrev Vec4 := InfoGeometry.Algebra.FiniteSpin.Vec4Q
abbrev Tensor2 := Matrix (Fin 4) (Fin 4) ℚ

def dot (u v : Vec4) : ℚ := ∑ i : Fin 4, u i * v i

def minkowskiDot (u v : Vec4) : ℚ :=
  u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- The Minkowski pairing is symmetric on the fixed `(+---)` four-vector carrier. -/
theorem minkowskiDot_symm (u v : Vec4) : minkowskiDot u v = minkowskiDot v u := by
  unfold minkowskiDot
  ring

/-- Additivity of the Minkowski pairing in its first argument. -/
theorem minkowskiDot_add_left (u v w : Vec4) :
    minkowskiDot (u + v) w = minkowskiDot u w + minkowskiDot v w := by
  simp only [minkowskiDot, Pi.add_apply]
  ring

/-- Additivity of the Minkowski pairing in its second argument. -/
theorem minkowskiDot_add_right (u v w : Vec4) :
    minkowskiDot u (v + w) = minkowskiDot u v + minkowskiDot u w := by
  simp only [minkowskiDot, Pi.add_apply]
  ring

/-- Scalar linearity of the Minkowski pairing in its first argument. -/
theorem minkowskiDot_smul_left (a : ℚ) (u v : Vec4) :
    minkowskiDot (a • u) v = a * minkowskiDot u v := by
  simp only [minkowskiDot, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scalar linearity of the Minkowski pairing in its second argument. -/
theorem minkowskiDot_smul_right (a : ℚ) (u v : Vec4) :
    minkowskiDot u (a • v) = a * minkowskiDot u v := by
  simp only [minkowskiDot, Pi.smul_apply, smul_eq_mul]
  ring

/-- A linear field action is skew with respect to the Minkowski pairing. -/
def MinkowskiSkew (F : Vec4 →ₗ[ℚ] Vec4) : Prop :=
  ∀ u v, minkowskiDot u (F v) = -minkowskiDot (F u) v

/-- The self-contraction of a Minkowski-skew field action vanishes. -/
theorem minkowskiDot_field_self_zero (F : Vec4 →ₗ[ℚ] Vec4)
    (hF : MinkowskiSkew F) (v : Vec4) : minkowskiDot v (F v) = 0 := by
  have h := hF v v
  rw [minkowskiDot_symm (F v) v] at h
  linarith

/-- Lorentz acceleration for a field action `F` and scalar coupling `k`. -/
def lorentzAcceleration (F : Vec4 →ₗ[ℚ] Vec4) (k : ℚ) (u : Vec4) : Vec4 :=
  k • F u

/-- The algebraic BMT spin derivative in units where the normalized velocity
satisfies `minkowskiDot u u = 1`. Its second term is parallel to `u`; it is the
covariant correction needed to preserve the Frenkel constraint. -/
def bmtSpinDerivative (F : Vec4 →ₗ[ℚ] Vec4) (k g : ℚ) (u s : Vec4) : Vec4 :=
  (k * (g / 2)) • F s +
    (k * ((g - 2) / 2) * minkowskiDot s (F u)) • u

/-- The BMT spin derivative is tangent to the fixed-spin quadratic level when
the Frenkel condition `u ⟂ s` holds. This is a pointwise algebraic identity, not
an ODE existence or global-flow theorem. -/
theorem bmt_spin_norm_tangent (F : Vec4 →ₗ[ℚ] Vec4)
    (hF : MinkowskiSkew F) (k g : ℚ) (u s : Vec4)
    (hFrenkel : minkowskiDot u s = 0) :
    minkowskiDot s (bmtSpinDerivative F k g u s) = 0 := by
  rw [bmtSpinDerivative, minkowskiDot_add_right,
    minkowskiDot_smul_right, minkowskiDot_smul_right]
  have hsu : minkowskiDot s u = 0 := by
    rw [minkowskiDot_symm, hFrenkel]
  rw [minkowskiDot_field_self_zero F hF s, hsu]
  ring

/-- The derivative of the Frenkel pairing vanishes algebraically along the
coupled Lorentz/BMT tangent vectors, for every gyromagnetic ratio `g`. -/
theorem bmt_frenkel_tangent (F : Vec4 →ₗ[ℚ] Vec4)
    (hF : MinkowskiSkew F) (k g : ℚ) (u s : Vec4)
    (hUnit : minkowskiDot u u = 1) :
    minkowskiDot (lorentzAcceleration F k u) s +
      minkowskiDot u (bmtSpinDerivative F k g u s) = 0 := by
  rw [lorentzAcceleration, bmtSpinDerivative,
    minkowskiDot_smul_left, minkowskiDot_add_right,
    minkowskiDot_smul_right, minkowskiDot_smul_right]
  have hQ : minkowskiDot (F u) s = minkowskiDot s (F u) :=
    minkowskiDot_symm _ _
  have hUS : minkowskiDot u (F s) = -minkowskiDot s (F u) := by
    calc
      minkowskiDot u (F s) = -minkowskiDot (F u) s := hF u s
      _ = -minkowskiDot s (F u) := by rw [minkowskiDot_symm]
  rw [hQ, hUS, hUnit]
  ring

/-- At `g = 2`, the BMT correction vanishes and the spin tangent is `k F(s)`. -/
theorem bmt_g_two (F : Vec4 →ₗ[ℚ] Vec4) (k : ℚ) (u s : Vec4) :
    bmtSpinDerivative F k 2 u s = k • F s := by
  simp [bmtSpinDerivative]

/-- The full change in the BMT tangent relative to `g = 2` has both a field
rotation component and the velocity-parallel correction. In particular, it is
not in general purely parallel to `u`. -/
theorem bmt_anomaly_difference (F : Vec4 →ₗ[ℚ] Vec4) (k g : ℚ)
    (u s : Vec4) :
    bmtSpinDerivative F k g u s - bmtSpinDerivative F k 2 u s =
      (k * ((g - 2) / 2)) •
        (F s + minkowskiDot s (F u) • u) := by
  unfold bmtSpinDerivative
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def wedge (u v : Vec4) : Tensor2 := fun i j => u i * v j - u j * v i

def IsAntisymmetric (A : Tensor2) : Prop := ∀ i j, A i j = - A j i

def contractRight (A : Tensor2) (p : Vec4) : Vec4 := fun i => ∑ j : Fin 4, A i j * p j

def lorentzForce (F : Tensor2) (p : Vec4) : Vec4 := contractRight F p

def massShell (p : Vec4) (m : ℚ) : Prop := minkowskiDot p p = m ^ 2

def gyromagneticReadout (charge mass g spinB : ℚ) : ℚ :=
  g * charge * spinB / (2 * mass)

/-- Four-dimensional Pfaffian polynomial for a `4×4` skew tensor. -/
def pfaffian4 (A : Tensor2) : ℚ :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- Finite electromagnetic tensor from electric/magnetic triples.
The sign convention is only a finite certificate convention. -/
def emTensor (E B : Fin 3 → ℚ) : Tensor2 :=
  !![(0 : ℚ), E 0, E 1, E 2;
     -E 0, 0, -B 2, B 1;
     -E 1, B 2, 0, -B 0;
     -E 2, -B 1, B 0, 0]

/-- Prequantization integrality socket made dependent: the integer `k` must
actually clear `2s/h`, i.e. `2s = k h`. -/
def SpinPrequantized (s h : ℚ) : Prop := ∃ k : ℤ, 2 * s = k * h

@[simp] theorem dot_zero_left (v : Vec4) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (v : Vec4) : dot v 0 = 0 := by
  simp [dot]

theorem wedge_apply (u v : Vec4) (i j : Fin 4) :
    wedge u v i j = u i * v j - u j * v i :=
  rfl

/-- A decomposable Souriau spin bivector is antisymmetric. -/
theorem wedge_antisymmetric (u v : Vec4) : IsAntisymmetric (wedge u v) := by
  intro i j
  simp [wedge]

theorem wedge_self_zero (u v : Vec4) (i : Fin 4) : wedge u v i i = 0 := by
  simp [wedge]

theorem wedge_swap (u v : Vec4) : wedge u v = - wedge v u := by
  ext i j
  simp [wedge]
  ring

/-- Decomposable spin bivectors obey the Plücker/Pfaffian relation. -/
theorem pfaffian4_wedge_zero (u v : Vec4) : pfaffian4 (wedge u v) = 0 := by
  simp [pfaffian4, wedge]
  ring

/-- The finite electromagnetic tensor is antisymmetric. -/
theorem emTensor_antisymmetric (E B : Fin 3 → ℚ) : IsAntisymmetric (emTensor E B) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [emTensor]

/-- In this sign convention, the Pfaffian of the electromagnetic tensor is `-E·B`. -/
theorem pfaffian4_emTensor (E B : Fin 3 → ℚ) :
    pfaffian4 (emTensor E B) = -(E 0 * B 0 + E 1 * B 1 + E 2 * B 2) := by
  simp [pfaffian4, emTensor]
  ring

/-- The normal spin-half prequantization readout `2s = h` is integral with `k=1`. -/
theorem spin_half_prequantized (h : ℚ) : SpinPrequantized (h / 2) h := by
  refine ⟨1, ?_⟩
  ring

/-- Contraction of a decomposable bivector with a transverse vector. -/
theorem contract_wedge_eq (u v p : Vec4) :
    contractRight (wedge u v) p = fun i => u i * dot v p - v i * dot u p := by
  ext i
  simp [contractRight, wedge, dot, Fin.sum_univ_four]
  ring

/-- If both blade vectors are transverse to `p`, then `(u∧v)·p=0`. -/
theorem contract_wedge_eq_zero_of_dot_eq_zero
    (u v p : Vec4) (hu : dot u p = 0) (hv : dot v p = 0) :
    contractRight (wedge u v) p = 0 := by
  rw [contract_wedge_eq]
  ext i
  simp [hu, hv]

/-- Antisymmetric electromagnetic tensors do no instantaneous power in this finite model. -/
theorem antisymmetric_power_zero (F : Tensor2) (p : Vec4) (hF : IsAntisymmetric F) :
    dot p (lorentzForce F p) = 0 := by
  simp [dot, lorentzForce, contractRight, Fin.sum_univ_four]
  have h00 : F 0 0 = 0 := by
    have h := hF 0 0
    linarith
  have h11 : F 1 1 = 0 := by
    have h := hF 1 1
    linarith
  have h22 : F 2 2 = 0 := by
    have h := hF 2 2
    linarith
  have h33 : F 3 3 = 0 := by
    have h := hF 3 3
    linarith
  have h01 := hF 0 1
  have h02 := hF 0 2
  have h03 := hF 0 3
  have h12 := hF 1 2
  have h13 := hF 1 3
  have h23 := hF 2 3
  rw [h00, h11, h22, h33, h01, h02, h03, h12, h13, h23]
  ring

/-- Mass shell for the unit rest momentum used as a finite sanity certificate. -/
theorem rest_momentum_mass_shell (m : ℚ) :
    massShell (fun i => if i = 0 then m else 0) m := by
  simp [massShell, minkowskiDot]
  ring

/-- Souriau/BMT normal magnetic moment readout at `g=2`: `μ = q S / m`. -/
theorem gyromagneticReadout_g_two (q m sB : ℚ) (hm : m ≠ 0) :
    gyromagneticReadout q m 2 sB = q * sB / m := by
  unfold gyromagneticReadout
  field_simp [hm]

end InfoGeometry.Physics.MDPASJMSouriau

import Mathlib.Tactic

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

abbrev Vec4 := Fin 4 → ℚ
abbrev Tensor2 := Matrix (Fin 4) (Fin 4) ℚ

def dot (u v : Vec4) : ℚ := ∑ i : Fin 4, u i * v i

def minkowskiDot (u v : Vec4) : ℚ :=
  u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

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
The sign convention is only a finite property convention. -/
def emTensor (E B : Fin 3 → ℚ) : Tensor2 :=
  !![(0 : ℚ), E 0, E 1, E 2;
     -E 0, 0, -B 2, B 1;
     -E 1, B 2, 0, -B 0;
     -E 2, -B 1, B 0, 0]

/-- Prequantization integrality condition: the integer `k` must
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

/-- Mass shell for the unit rest momentum used as a finite sanity property. -/
theorem rest_momentum_mass_shell (m : ℚ) :
    massShell (fun i => if i = 0 then m else 0) m := by
  simp [massShell, minkowskiDot]
  ring

/-- Souriau/BMT normal magnetic moment readout at `g=2`: `μ = q S / m`. -/
theorem gyromagneticReadout_g_two (q m sB : ℚ) (hm : m ≠ 0) :
    gyromagneticReadout q m 2 sB = q * sB / m := by
  unfold gyromagneticReadout
  field_simp [hm]

abbrev FiniteSpinParticleCertificate : Type _ :=
  Σ' p : Vec4,
    Σ' u : Vec4,
      Σ' v : Vec4,
        Σ' field : Tensor2,
          IsAntisymmetric field

namespace FiniteSpinParticleCertificate

abbrev p (C : FiniteSpinParticleCertificate) : Vec4 := C.1
abbrev u (C : FiniteSpinParticleCertificate) : Vec4 := C.2.1
abbrev v (C : FiniteSpinParticleCertificate) : Vec4 := C.2.2.1
abbrev field (C : FiniteSpinParticleCertificate) : Tensor2 := C.2.2.2.1
abbrev field_antisym (C : FiniteSpinParticleCertificate) := C.2.2.2.2

end FiniteSpinParticleCertificate

namespace FiniteSpinParticleCertificate

variable (C : FiniteSpinParticleCertificate)

/-- The property's decomposable spin bivector is antisymmetric. -/
theorem spin_antisym : IsAntisymmetric (wedge C.u C.v) :=
  wedge_antisymmetric C.u C.v

/-- The property's decomposable spin bivector has zero Pfaffian. -/
theorem spin_plucker : pfaffian4 (wedge C.u C.v) = 0 :=
  pfaffian4_wedge_zero C.u C.v

/-- Orthogonality of both generating vectors implies spin transversality. -/
theorem spin_transverse
    (hu : dot C.u C.p = 0) (hv : dot C.v C.p = 0) :
    contractRight (wedge C.u C.v) C.p = 0 :=
  contract_wedge_eq_zero_of_dot_eq_zero C.u C.v C.p hu hv

/-- Antisymmetry of the supplied field forces zero Lorentz-force power. -/
theorem lorentz_power_zero :
    dot C.p (lorentzForce C.field C.p) = 0 :=
  antisymmetric_power_zero C.field C.p C.field_antisym

/-- The normal `g = 2` magnetic-moment readout. -/
theorem normal_moment_readout
    (_C : FiniteSpinParticleCertificate)
    (q m sB : ℚ) (hm : m ≠ 0) :
    gyromagneticReadout q m 2 sB = q * sB / m :=
  gyromagneticReadout_g_two q m sB hm

/-- Half-spin prequantization is the integral identity `2(h/2)/h = 1`. -/
theorem spin_half_prequantization
    (_C : FiniteSpinParticleCertificate) (h : ℚ) :
    SpinPrequantized (h / 2) h :=
  spin_half_prequantized h

end FiniteSpinParticleCertificate

end MDPASJMSouriau
end Physics
end InfoGeometry

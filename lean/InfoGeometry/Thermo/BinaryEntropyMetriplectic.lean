import InfoGeometry.Thermo.GenericMetriplecticFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Probability.BinaryAitchisonMoments

/-!
# A concrete metriplectic extension of the binary entropy field

State coordinates are `(q, r, p)`, with oscillator energy `(q^2+r^2)/2`
and binary Shannon entropy `S(p)`. The canonical skew operator acts on `(q,r)`;
the positive mobility `p*(1-p)` acts only on the probability coordinate.
All GENERIC law fields are proved for explicit linear maps. The construction
does not assert a nondegenerate Poisson bracket on the one-simplex alone.
-/

noncomputable section
namespace InfoGeometry.Thermo.BinaryEntropyMetriplectic

open InfoGeometry.Thermo.GenericMetriplecticFlow
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Probability.BinaryAitchisonMoments

abbrev V := InfoGeometry.Algebra.FiniteSpin.Vec3R

def e (i : Fin 3) : V := Pi.single i 1

def poisson : Covector V →ₗ[ℝ] V where
  toFun α := α (e 1) • e 0 - α (e 0) • e 1
  map_add' α β := by simp [add_smul]; abel
  map_smul' c α := by simp [smul_sub, smul_smul]

def mobility (p : ℝ) : Covector V →ₗ[ℝ] V where
  toFun α := (p * (1 - p) * α (e 2)) • e 2
  map_add' α β := by simp [mul_add, add_smul]
  map_smul' c α := by simp [smul_smul]; congr 1; ring

def energyDifferential (q r : ℝ) : Covector V :=
  q • LinearMap.proj 0 + r • LinearMap.proj 1

def entropyDifferential (p : ℝ) : Covector V :=
  -logit p • LinearMap.proj 2

/-- Actual differentials of energy and entropy along any differentiable curve. -/
theorem energy_curve_derivative (q r : ℝ → ℝ) (u v t : ℝ)
    (hq : HasDerivAt q u t) (hr : HasDerivAt r v t) :
    HasDerivAt (fun s => (q s ^ 2 + r s ^ 2) / 2)
      (energyDifferential (q t) (r t) ![u, v, 0]) t := by
  convert ((hq.pow 2).add (hr.pow 2)).div_const 2 using 1
  simp [energyDifferential]
  ring

theorem entropy_curve_derivative (p : ℝ → ℝ) (u t : ℝ)
    (hd : HasDerivAt p u t) (hp : p t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => -negativeEntropy (p s))
      (entropyDifferential (p t) ![0, 0, u]) t := by
  exact ((hasDerivAt_negativeEntropy hp).neg).comp t hd

/-- A constructed inhabitant of the existing GENERIC owner. Neither energy
conservation nor entropy production is assumed as a field without proof. -/
def system (q r : ℝ) (p : Set.Ioo (0 : ℝ) 1) : System V where
  dH := energyDifferential q r
  dS := entropyDifferential p.val
  L := poisson
  M := mobility p.val
  L_skew α β := by simp [poisson, map_sub, map_smul]; ring
  L_entropy_casimir := by simp [poisson, entropyDifferential, e]
  M_symmetric α β := by simp [mobility, map_smul]; ring
  M_hamiltonian_casimir := by simp [mobility, energyDifferential, e]
  M_nonneg α := by
    change 0 ≤ α ((p.val * (1 - p.val) * α (e 2)) • e 2)
    rw [map_smul]
    change 0 ≤ p.val * (1 - p.val) * α (e 2) * α (e 2)
    have h := mul_nonneg (mul_pos p.property.1 (sub_pos.mpr p.property.2)).le
      (sq_nonneg (α (e 2)))
    nlinarith

/-- The reversible oscillator and the binary entropy-gradient field are both
present in the constructed flow. -/
theorem system_flow (q r : ℝ) (p : Set.Ioo (0 : ℝ) 1) :
    (system q r p).flow = ![r, -q, entropyGradientField p.val] := by
  ext i
  fin_cases i <;>
    simp [System.flow, system, poisson, mobility, energyDifferential,
      entropyDifferential, e, entropyGradientField]

/-- The reversible field is tangent to the constant-energy circle. -/
theorem oscillator_tangent_energy (q r : ℝ) :
    energyDifferential q r ![r, -q, 0] = 0 := by
  simp [energyDifferential]
  ring

/-- The entropy rate is the actual nonnegative production of the binary field. -/
theorem system_entropy_rate (q r : ℝ) (p : Set.Ioo (0 : ℝ) 1) :
    (system q r p).dS (system q r p).flow = p.val * (1 - p.val) * logit p.val ^ 2 := by
  rw [system_flow]
  simp [system, entropyDifferential, entropyGradientField]
  ring

end InfoGeometry.Thermo.BinaryEntropyMetriplectic

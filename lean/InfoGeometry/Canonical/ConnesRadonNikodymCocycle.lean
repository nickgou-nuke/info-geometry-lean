import InfoGeometry.Clifford.ChiralGrandCanonicalModularGenerator
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Canonical.TomitaTakesakiRealification
import InfoGeometry.Arithmetic.MoebiusSignature
import InfoGeometry.Analysis.MellinZetaScaling

open InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.ChiralLorentzFockQuadratic
open InfoGeometry.Clifford.Cl44Witt

/-!
# Connes Radon-Nikodym Cocycle — Concrete Cl(4,4) Realization

We define the true algebraic Connes Radon-Nikodym cocycle derivative
D_X ω = H₂ - H₁ directly on the concrete Cl(4,4) operator carrier,
using the specific grand-canonical modular generators.

There are no conditional wrappers.
-/

namespace ConnesCocycle

/-- The concrete algebraic Connes Radon-Nikodym cocycle derivative. -/
noncomputable def connesRadonNikodymDerivative (H1 H2 : Operator) (beta1 μ1 μχ1 beta2 μ2 μχ2 : ℝ) : Operator :=
  grandCanonicalModularGenerator H2 beta2 μ2 μχ2 - grandCanonicalModularGenerator H1 beta1 μ1 μχ1

/-- Zero derivative when the states (modular generators) coincide. -/
theorem connesRadonNikodymDerivative_zero_of_eq (H : Operator) (beta μ μχ : ℝ) :
    connesRadonNikodymDerivative H H beta μ μχ beta μ μχ = 0 := by
  simp [connesRadonNikodymDerivative]

/-- The cocycle derivative conserves the total number operator. -/
theorem connesRadonNikodymDerivative_commutator_totalNumber_conserved
    (H1 H2 : Operator) (beta1 μ1 μχ1 beta2 μ2 μχ2 : ℝ)
    (hH1 : algebraCommutator H1 totalNumber = 0)
    (hH2 : algebraCommutator H2 totalNumber = 0) :
    algebraCommutator (connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2) totalNumber = 0 := by
  unfold connesRadonNikodymDerivative algebraCommutator
  rw [sub_mul, mul_sub]
  have h1 := grandCanonicalGenerator_commutator_totalNumber_conserved H1 beta1 μ1 μχ1 hH1
  have h2 := grandCanonicalGenerator_commutator_totalNumber_conserved H2 beta2 μ2 μχ2 hH2
  unfold algebraCommutator at h1 h2
  have h1_eq : grandCanonicalModularGenerator H1 beta1 μ1 μχ1 * totalNumber = totalNumber * grandCanonicalModularGenerator H1 beta1 μ1 μχ1 := sub_eq_zero.mp h1
  have h2_eq : grandCanonicalModularGenerator H2 beta2 μ2 μχ2 * totalNumber = totalNumber * grandCanonicalModularGenerator H2 beta2 μ2 μχ2 := sub_eq_zero.mp h2
  rw [h1_eq, h2_eq]
  exact sub_self _

/-- The cocycle derivative conserves the chiral charge. -/
theorem connesRadonNikodymDerivative_commutator_chiralCharge_conserved
    (H1 H2 : Operator) (beta1 μ1 μχ1 beta2 μ2 μχ2 : ℝ)
    (hH1 : algebraCommutator H1 chiralCharge = 0)
    (hH2 : algebraCommutator H2 chiralCharge = 0) :
    algebraCommutator (connesRadonNikodymDerivative H1 H2 beta1 μ1 μχ1 beta2 μ2 μχ2) chiralCharge = 0 := by
  unfold connesRadonNikodymDerivative algebraCommutator
  rw [sub_mul, mul_sub]
  have h1 := grandCanonicalModularGenerator_commutator_chiralCharge H1 beta1 μ1 μχ1 hH1
  have h2 := grandCanonicalModularGenerator_commutator_chiralCharge H2 beta2 μ2 μχ2 hH2
  unfold algebraCommutator at h1 h2
  have h1_eq : grandCanonicalModularGenerator H1 beta1 μ1 μχ1 * chiralCharge = chiralCharge * grandCanonicalModularGenerator H1 beta1 μ1 μχ1 := sub_eq_zero.mp h1
  have h2_eq : grandCanonicalModularGenerator H2 beta2 μ2 μχ2 * chiralCharge = chiralCharge * grandCanonicalModularGenerator H2 beta2 μ2 μχ2 := sub_eq_zero.mp h2
  rw [h1_eq, h2_eq]
  exact sub_self _


end ConnesCocycle

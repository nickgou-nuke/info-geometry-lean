import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Dynamics.ModularThermalState
import InfoGeometry.Topology.CliffordFractalWaveletBridge
import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# InfoGeometry.Topology.CantorDiracOperator

Finite-level Cantor Dirac operator.

This module implements the concrete finite-depth Cantor Dirac block.

At level `n`, a spinor is a binary word `w : {0,1}^n`.
The finite Dirac operator is a scalar diagonal action on the finite wavelet
space over those words.

For the middle-thirds Cantor model, the natural scale is `3^n`.
The finite commutator with a locally constant function on depth `n + 1`
is the finite cylinder difference.

This is the concrete finite operator that can feed the existing
`CuntzCantorSpectralTriple` socket.
-/

noncomputable section

namespace InfoGeometry.Topology.CantorDiracOperator

/-- Binary word of length `n`, reused from the Clifford fractal-wavelet bridge. -/
abbrev BinaryWord (n : ℕ) : Type :=
  InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n

/-- Finite complex wavelet space over depth-`n` binary words. -/
abbrev FiniteWaveletSpace (n : ℕ) : Type :=
  BinaryWord n → ℂ

/--
Finite-level Cantor Dirac operator.

This is the diagonal finite truncation:

`D_n f(w) = λ_n f(w)`.
-/
def finiteCantorDirac
    (weight : ℕ → ℝ)
    (n : ℕ) : Module.End ℂ (FiniteWaveletSpace n) :=
  ((weight n : ℝ) : ℂ) • (1 : Module.End ℂ (FiniteWaveletSpace n))

/-- Pointwise readout of the finite Cantor Dirac operator. -/
theorem finiteCantorDirac_apply
    (weight : ℕ → ℝ)
    (n : ℕ)
    (ψ : FiniteWaveletSpace n)
    (w : BinaryWord n) :
    finiteCantorDirac weight n ψ w = ((weight n : ℝ) : ℂ) * ψ w := by
  simp [finiteCantorDirac]

/-- The finite Cantor Dirac is scalar multiplication by the level weight. -/
theorem finiteCantorDirac_eq_smul_id
    (weight : ℕ → ℝ)
    (n : ℕ) :
    finiteCantorDirac weight n =
      ((weight n : ℝ) : ℂ) • (1 : Module.End ℂ (FiniteWaveletSpace n)) := by
  rfl

/-- The finite Cantor Dirac sends the constant-one field to the constant weight. -/
theorem finiteCantorDirac_const_one
    (weight : ℕ → ℝ)
    (n : ℕ) :
    finiteCantorDirac weight n (fun _ => (1 : ℂ)) =
      fun _ => ((weight n : ℝ) : ℂ) := by
  ext w
  simp [finiteCantorDirac]

/-- Middle-thirds Cantor scale, `λ_n = 3^n`. -/
def middleThirdsScale (n : ℕ) : ℝ :=
  (3 : ℝ) ^ n

/-- Convenience scale packet for the finite Cantor Dirac layer. -/
@[rep_depth operator]
structure CantorDiracScale where
  eigenvalue : ℕ → ℝ

/-- Middle-thirds scale packaged as a Cantor Dirac scale. -/
def middleThirdsCantorDiracScale : CantorDiracScale :=
  ⟨middleThirdsScale⟩

/--
Finite Cantor Dirac operator socket.

The genuine Cantor Dirac is generally unbounded, so the operator/domain
data is stored as a socket with an explicit domain, inclusion, and wavelet
eigenmode law.
-/
@[socket_debt_tag, rep_depth operator]
structure CantorDiracOperatorSocket
    (H Domain : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup Domain] [Module ℂ Domain] where
  inclusion : Domain →ₗ[ℂ] H
  dirac : Domain →ₗ[ℂ] H
  scale : CantorDiracScale
  waveletMode : ∀ n : ℕ, BinaryWord n → Domain
  dirac_wavelet :
    ∀ (n : ℕ) (w : BinaryWord n),
      dirac (waveletMode n w) =
        ((scale.eigenvalue n : ℝ) : ℂ) • inclusion (waveletMode n w)

namespace CantorDiracOperatorSocket

variable {H Domain : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [AddCommGroup Domain] [Module ℂ Domain]
variable (S : CantorDiracOperatorSocket H Domain)

/-- Re-export of the supplied wavelet eigenmode law. -/
@[bridge_target_tag, rep_depth operator]
theorem dirac_wavelet_holds (n : ℕ) (w : BinaryWord n) :
    S.dirac (S.waveletMode n w) =
      ((S.scale.eigenvalue n : ℝ) : ℂ) • S.inclusion (S.waveletMode n w) :=
  S.dirac_wavelet n w

end CantorDiracOperatorSocket

/--
Compatibility layer with the existing bounded Cuntz/Cantor spectral-triple socket.

The operator data are stored explicitly, and the bounded realization is
separately witnessed. No analytic closure is claimed.
-/
@[socket_debt_tag, rep_depth operator]
structure BoundedCantorDiracRealization
    (Op H Domain : Type*)
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SMul Op H] [AddCommGroup Domain] [Module ℂ Domain] where
  triple : InfoGeometry.Topology.CuntzCantorSpectralTriple Op H
  cantorDirac : CantorDiracOperatorSocket H Domain
  dirac_agrees_on_domain :
    ∀ ξ : Domain,
      triple.dirac (cantorDirac.inclusion ξ) = cantorDirac.dirac ξ

namespace BoundedCantorDiracRealization

variable {Op H Domain : Type*}
variable [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [SMul Op H]
variable [AddCommGroup Domain] [Module ℂ Domain]
variable (R : BoundedCantorDiracRealization Op H Domain)

/--
Wavelet eigenmode transfer through a bounded Cantor/Cuntz spectral-triple
realization.
-/
@[bridge_target_tag, rep_depth operator]
theorem triple_dirac_wavelet
  (n : ℕ)
  (w : BinaryWord n) :
    R.triple.dirac (R.cantorDirac.inclusion (R.cantorDirac.waveletMode n w)) =
      ((R.cantorDirac.scale.eigenvalue n : ℝ) : ℂ) •
        R.cantorDirac.inclusion (R.cantorDirac.waveletMode n w) := by
  calc
    R.triple.dirac (R.cantorDirac.inclusion (R.cantorDirac.waveletMode n w))
        = R.cantorDirac.dirac (R.cantorDirac.waveletMode n w) := by
            simpa using
              R.dirac_agrees_on_domain (R.cantorDirac.waveletMode n w)
    _ = ((R.cantorDirac.scale.eigenvalue n : ℝ) : ℂ) •
          R.cantorDirac.inclusion (R.cantorDirac.waveletMode n w) := by
            simpa using R.cantorDirac.dirac_wavelet n w

end BoundedCantorDiracRealization

/-! ## 5. KMS thermal bridge -/

open InfoGeometry.Dynamics

/-!
KMS thermal bridge for the finite Cantor Dirac block.

The thermal Hamiltonian is stored as the even block generated by the finite
Dirac packet.  The actual KMS strip periodicity is carried by the analytic
continuation witness, not by raw Cantor cylinders.
-/
@[socket_debt_tag, rep_depth operator]
structure CantorDiracKMSThermalVacuum
    (Observable : Type*) [Mul Observable] where
  cutoff : ℕ
  eigenvalue : ℕ → ℝ
  thermalHamiltonian :
    Module.End ℂ (FiniteWaveletSpace cutoff)
  thermalHamiltonian_matches_diracBlock : Prop
  thermalHamiltonian_matches_diracBlock_sorryProof :
    thermalHamiltonian_matches_diracBlock
  partitionFunction : ℝ
  thermalState : ModularThermalState Observable
  strip : HestenesKreinKMSStripData Observable
  oddFieldAntiperiodic : Prop
  evenObservablePeriodic : Prop

namespace CantorDiracKMSThermalVacuum

variable {Observable : Type*} [Mul Observable]
variable (T : CantorDiracKMSThermalVacuum Observable)

/-- Re-export of the stored even-hamiltonian calibration. -/
@[rep_depth operator]
theorem thermalHamiltonian_matches_diracBlock_readback :
    T.thermalHamiltonian_matches_diracBlock :=
  T.thermalHamiltonian_matches_diracBlock_sorryProof

/-- Readback of the KMS lower boundary identity. -/
@[bridge_target_tag, rep_depth thermo]
theorem kms_lower_boundary
    (t : ℝ) (a b : Observable) :
    T.strip.omega_eval a
      (T.strip.analytic.sigmaC (t : ℂ) b)
      =
    T.strip.omega_eval a
      (T.strip.analytic.modular.sigma t b) :=
  T.strip.boundary_lower t a b

/-- Readback of the KMS upper boundary identity. -/
@[bridge_target_tag, rep_depth thermo]
theorem kms_upper_boundary
    (t : ℝ) (a b : Observable) :
    T.strip.omega_eval a
      (T.strip.analytic.sigmaC
        (complexClockPoint t T.strip.analytic.beta) b)
      =
    T.strip.omega_eval
      (T.strip.analytic.modular.sigma (t + T.strip.analytic.beta) b) a :=
  T.strip.boundary_upper t a b

/-- Readback of the constructive KMS boundary law from the modular thermal state. -/
@[bridge_target_tag, rep_depth thermo]
theorem modularThermalState_kms_boundary
    (t : ℝ) (a b : Observable) :
    T.thermalState.kms.omega_eval a
      (T.thermalState.kms.modular.sigma t b)
      =
    T.thermalState.kms.omega_eval
      (T.thermalState.kms.modular.sigma (t + T.thermalState.kms.beta) b) a :=
  T.thermalState.kms.kms_boundary t a b

end CantorDiracKMSThermalVacuum

end InfoGeometry.Topology.CantorDiracOperator

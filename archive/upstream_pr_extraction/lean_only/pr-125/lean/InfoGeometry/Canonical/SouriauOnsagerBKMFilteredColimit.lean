import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

noncomputable section

/-!
# Filtered direct/inverse-colimit transport of Kubo--Mori kernels

The continuum mechanism in this owner is categorical:

* finite stages are full noncommutative bounded-operator algebras;
* observables move covariantly through a filtered direct inductive system;
* Kubo--Mori kernel functionals move contravariantly through the dual inverse
  system owned by `FilteredDirectInverseColimit`;
* a functional on a colimit cocone makes the finite-stage Kubo--Mori readout
  independent of the chosen stage representative.

No infinite-dimensional carrier, epsilon limit, coordinate chart, or
measure-theoretic continuum construction is introduced here.  The real
parameter `s` is the Cartan/modular-flow parameter already present in the
operator kernel `ρ^s A* ρ^(1-s)`.
-/

namespace InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit

open SouriauOnsagerBKM
open FilteredColimit
open FilteredColimit.InductiveCocone

variable {I : Type*} [Preorder I]

/-- Full finite operator algebra at a filtered stage. -/
abbrev OperatorStage (dim : I → ℕ) (i : I) :=
  FiniteOperatorAlgebra (dim i)

variable (dim : I → ℕ)
variable
  (sys : DirectInductiveSystem ℂ I (OperatorStage dim))
  (D : ∀ i, FaithfulDensityOperator (dim i))
  (A : ∀ i, FiniteOperatorAlgebra (dim i))
  (s : ℝ)

/-- The stagewise Kubo--Mori dual functional at Cartan parameter `s`. -/
def stageKernel (i : I) :
    OperatorStage dim i →ₗ[ℂ] ℂ :=
  (D i).kuboMoriKernelFunctional (A i) s

omit [Preorder I] in
@[simp] theorem stageKernel_apply
    (i : I) (B : OperatorStage dim i) :
    stageKernel dim D A s i B =
      (D i).kuboMoriIntegrand (A i) B s :=
  rfl

/-- Pointwise compatibility of Kubo--Mori kernels with a direct transition is
exactly equality after the owner-provided dual inverse transition. -/
theorem stageKernel_dualInverseTransition
    {i j : I} (hij : i ≤ j)
    (hcompat :
      ∀ B : OperatorStage dim i,
        stageKernel dim D A s j (sys.f hij B) =
          stageKernel dim D A s i B) :
    dualInverseTransition sys hij (stageKernel dim D A s j) =
      stageKernel dim D A s i := by
  ext B
  exact hcompat B

/-- Kubo--Mori stage kernels inherit the inverse-system composition law from
the filtered direct system. -/
theorem stageKernel_dual_inverse_comp
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    dualInverseTransition sys hij
        (dualInverseTransition sys hjk
          (stageKernel dim D A s k)) =
      dualInverseTransition sys (le_trans hij hjk)
        (stageKernel dim D A s k) :=
  dual_inverse_comp sys hij hjk (stageKernel dim D A s k)

variable {Ainf : Type*} [AddCommGroup Ainf] [Module ℂ Ainf]
variable
  (cocone : InductiveCocone ℂ sys Ainf)
  (Phi : Ainf →ₗ[ℂ] ℂ)

/-- If a colimit functional restricts to the stagewise Kubo--Mori kernels,
then their dual inverse compatibility is derived rather than separately
postulated. -/
theorem stageKernel_compatible_of_colimit_descent
    (hdesc :
      ∀ i, Phi.comp (cocone.psi i) =
        stageKernel dim D A s i)
    {i j : I} (hij : i ≤ j) :
    dualInverseTransition sys hij (stageKernel dim D A s j) =
      stageKernel dim D A s i := by
  apply stageKernel_dualInverseTransition dim sys D A s hij
  intro B
  rw [← LinearMap.congr_fun (hdesc j) (sys.f hij B)]
  rw [← LinearMap.congr_fun (hdesc i) B]
  exact cocone.colimit_functional_trace_comm Phi hij B

/-- The Kubo--Mori scalar readout of a direct-stage observable is independent
of whether it is evaluated before or after a filtered transition. -/
theorem stageKernel_colimit_readout_independent
    (hdesc :
      ∀ i, Phi.comp (cocone.psi i) =
        stageKernel dim D A s i)
    {i j : I} (hij : i ≤ j)
    (B : OperatorStage dim i) :
    Phi (cocone.psi j (sys.f hij B)) =
      stageKernel dim D A s i B := by
  rw [cocone.colimit_functional_trace_comm Phi hij B]
  exact LinearMap.congr_fun (hdesc i) B

end InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit

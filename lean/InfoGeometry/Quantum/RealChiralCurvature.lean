/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace
import InfoGeometry.Quantum.Realification
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# Real internal-phase readout of projector curvature

For finite real matrices the readout is `phaseTrace J T = (1/2) Tr(J T)`.
Its restriction to the native subalgebra centralizing `J` is a cyclic
additive functional, derived from matrix trace cyclicity. This restriction
is essential: no cyclicity on all real matrices is asserted.

The existing projector-curvature trace identities give the gauge-generator
contraction, complementary-projector sign, and triple-tangent cancellation
on this real algebra. These are finite algebraic identities, not a
construction of a differential form, an integration measure, or a positive
normalized state.

The comparison uses the existing faithful matrix realification. Its
normalization is `phaseTrace internalJ (realify T) = -(Tr T).im`. For the
skew-adjoint curvature of self-adjoint projectors and directions this is
exactly the real scalar represented by `i Tr(P [X,Y])` in Craig,
*A gauge-invariant measure for lattice chiral fermions*, arXiv:2610.09093v1,
equation (4.19). The real operator definitions require no external
imaginary scalar; the complex expressions occur only in this comparison.
-/

noncomputable section

namespace InfoGeometry.Quantum.RealChiralCurvature

open InfoGeometry.Clifford.ChiralProjectorBerryCurvature
open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
open InfoGeometry.Quantum.Realification

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real internal-phase trace readout. The factor `1/2` compensates
for the doubled real trace in the existing realification. -/
def phaseTrace (J T : Matrix n n ℝ) : ℝ := (1 / 2 : ℝ) * Matrix.trace (J * T)

/-- Commutation with the phase axis supplies the required cyclic rotation.
No square law or adjoint assumption on the phase axis is needed here. -/
theorem phaseTrace_mul_comm_of_commute_right (J a b : Matrix n n ℝ)
    (hb : Commute J b) : phaseTrace J (a * b) = phaseTrace J (b * a) := by
  unfold phaseTrace
  congr 1
  calc
    Matrix.trace (J * (a * b)) = Matrix.trace ((J * a) * b) := by rw [mul_assoc]
    _ = Matrix.trace (b * (J * a)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((b * J) * a) := by rw [mul_assoc]
    _ = Matrix.trace ((J * b) * a) := by rw [← hb.eq]
    _ = Matrix.trace (J * (b * a)) := by rw [mul_assoc]

/-- The readout as an actual additive functional on the native phase centralizer. -/
def centralizerTrace (J : Matrix n n ℝ) :
    Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ)) →+ ℝ where
  toFun T := phaseTrace J T
  map_zero' := by
    change phaseTrace J (0 : Matrix n n ℝ) = 0
    simp only [phaseTrace, mul_zero, Matrix.trace_zero]
  map_add' a b := by
    change phaseTrace J ((a : Matrix n n ℝ) + (b : Matrix n n ℝ)) =
      phaseTrace J a + phaseTrace J b
    simp only [phaseTrace, mul_add, Matrix.trace_add]

/-- Cyclicity is proved from centralizer membership, not stored as an assumption. -/
theorem centralizerTrace_cyclic (J : Matrix n n ℝ)
    (a b : Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ))) :
    centralizerTrace J (a * b) = centralizerTrace J (b * a) := by
  change phaseTrace J ((a : Matrix n n ℝ) * (b : Matrix n n ℝ)) =
    phaseTrace J ((b : Matrix n n ℝ) * (a : Matrix n n ℝ))
  apply phaseTrace_mul_comm_of_commute_right
  change J * (b : Matrix n n ℝ) = (b : Matrix n n ℝ) * J
  exact (Subalgebra.mem_centralizer_iff.mp b.property) J (by simp)

section CentralizerCurvature

variable (J : Matrix n n ℝ)
variable {p x y z : Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ))}

/-- A phase-linear projector tangent has zero internal-phase trace. -/
theorem phaseTrace_tangent_zero (hp : p * p = p) (hx : p * x + x * p = x) :
    phaseTrace J (x : Matrix n n ℝ) = 0 := by
  change centralizerTrace J x = 0
  exact InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_tangent_zero
    (centralizerTrace J) (centralizerTrace_cyclic J) hp hx

/-- The ordered product of three phase-linear tangents has zero readout. -/
theorem phaseTrace_tangent_triple_zero (hp : p * p = p)
    (hx : p * x + x * p = x) (hy : p * y + y * p = y)
    (hz : p * z + z * p = z) :
    phaseTrace J ((x : Matrix n n ℝ) * (y : Matrix n n ℝ) * (z : Matrix n n ℝ)) = 0 := by
  change centralizerTrace J (x * y * z) = 0
  exact InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_tangent_triple_zero
    (centralizerTrace J) (centralizerTrace_cyclic J) hp hx hy hz

/-- The existing sandwiched curvature and single-projector formula have
the same internal-phase readout. -/
theorem phaseTrace_projectorCurvature (hp : p * p = p)
    (x y : Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ))) :
    phaseTrace J (projectorCurvature (p : Matrix n n ℝ) x y) =
      phaseTrace J ((p : Matrix n n ℝ) * commutator x y) := by
  change centralizerTrace J (projectorCurvature p x y) =
    centralizerTrace J (p * commutator x y)
  exact InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_projectorCurvature
    (centralizerTrace J) (centralizerTrace_cyclic J) hp x y

/-- Contracting curvature with an inner gauge variation gives the actual
phase-weighted generator-tangent pairing. -/
theorem phaseTrace_projectorCurvature_gauge (hp : p * p = p)
    (hx : p * x + x * p = x)
    (g : Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ))) :
    phaseTrace J (projectorCurvature (p : Matrix n n ℝ) x (commutator g p)) =
      phaseTrace J ((g : Matrix n n ℝ) * (x : Matrix n n ℝ)) := by
  change centralizerTrace J (projectorCurvature p x (commutator g p)) =
    centralizerTrace J (g * x)
  exact InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_projectorCurvature_gauge
    (centralizerTrace J) (centralizerTrace_cyclic J) hp hx g

/-- Complementing the phase-linear projector reverses the curvature readout. -/
theorem phaseTrace_projectorCurvature_complement (hp : p * p = p)
    (x y : Subalgebra.centralizer ℝ ({J} : Set (Matrix n n ℝ))) :
    phaseTrace J (projectorCurvature (1 - (p : Matrix n n ℝ))
      (-(x : Matrix n n ℝ)) (-(y : Matrix n n ℝ))) =
      -phaseTrace J (projectorCurvature (p : Matrix n n ℝ) x y) := by
  change centralizerTrace J (projectorCurvature (1 - p) (-x) (-y)) =
    -centralizerTrace J (projectorCurvature p x y)
  exact InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_projectorCurvature_complement
    (centralizerTrace J) (centralizerTrace_cyclic J) hp x y

end CentralizerCurvature

section ExistingRealificationComparison

/-- Exact normalization against the repository's faithful realification,
for an arbitrary complex matrix, without an adjoint assumption. -/
theorem phaseTrace_realify (T : Matrix n n ℂ) :
    phaseTrace (internalJ (n := n)) (realify T) = -(Matrix.trace T).im := by
  unfold phaseTrace
  rw [internalJ_eq_realify, ← realify_mul, smul_mul_assoc, one_mul,
    trace_realify, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.I_mul_re]
  rw [← mul_assoc, div_mul_cancel₀ 1 (two_ne_zero : (2 : ℝ) ≠ 0), one_mul]

/-- The existing reconstruction theorem identifies the readout on every
real matrix in the internal-axis centralizer, not just a chosen image. -/
theorem phaseTrace_internalJ_centralizer
    (T : Subalgebra.centralizer ℝ
      ({internalJ (n := n)} : Set (Matrix (n ⊕ n) (n ⊕ n) ℝ))) :
    phaseTrace internalJ (T : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      -(Matrix.trace (unrealify (T : Matrix (n ⊕ n) (n ⊕ n) ℝ))).im := by
  have hT : Commute (T : Matrix (n ⊕ n) (n ⊕ n) ℝ) internalJ := by
    change (T : Matrix (n ⊕ n) (n ⊕ n) ℝ) * internalJ =
      internalJ * (T : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    exact ((Subalgebra.mem_centralizer_iff.mp T.property) internalJ (by simp)).symm
  calc
    phaseTrace internalJ (T : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        phaseTrace internalJ (realify (unrealify (T : Matrix (n ⊕ n) (n ⊕ n) ℝ))) :=
      congrArg (phaseTrace internalJ) (realify_unrealify_of_commute _ hT).symm
    _ = -(Matrix.trace (unrealify (T : Matrix (n ⊕ n) (n ⊕ n) ℝ))).im :=
      phaseTrace_realify _

/-- For a purely imaginary trace the real readout is exactly the scalar
represented by `i Tr(T)`, including its sign. -/
theorem phaseTrace_realify_eq_paper_of_re_eq_zero (T : Matrix n n ℂ)
    (hT : (Matrix.trace T).re = 0) :
    (phaseTrace (internalJ (n := n)) (realify T) : ℂ) = Complex.I * Matrix.trace T := by
  rw [phaseTrace_realify]
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.I_mul_re]
  · simp only [Complex.ofReal_im, Complex.I_mul_im, hT]

/-- Faithful realification preserves the actual ordered curvature, and
self-adjoint input operators discharge the pure-imaginary trace condition.
The resulting scalar equals the paper's single-projector expression. -/
theorem phaseTrace_realified_curvature_eq_paper (p x y : Matrix n n ℂ)
    (hp : p * p = p) (hps : star p = p) (hxs : star x = x) (hys : star y = y) :
    (phaseTrace (internalJ (n := n))
      (projectorCurvature (realify p) (realify x) (realify y)) : ℂ) =
      Complex.I * Matrix.trace (p * commutator x y) := by
  let F := projectorCurvature p x y
  have hFstar : star F = -F := star_projectorCurvature_of_selfAdjoint hps hxs hys
  have htrace : star (Matrix.trace F) = -Matrix.trace F := by
    have h := congrArg Matrix.trace hFstar
    simpa only [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
      Matrix.trace_neg] using h
  have hre : (Matrix.trace F).re = -(Matrix.trace F).re := by
    simpa only [Complex.star_def, Complex.conj_re, Complex.neg_re] using
      congrArg Complex.re htrace
  have hzero : (Matrix.trace F).re = 0 := by
    have htwo : (2 : ℝ) * (Matrix.trace F).re = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hre
    exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
  have hmap := map_projectorCurvature (realifyRingHom (n := n)) p x y
  change realify F = projectorCurvature (realify p) (realify x) (realify y) at hmap
  rw [← hmap]
  calc
    (phaseTrace internalJ (realify F) : ℂ) = Complex.I * Matrix.trace F :=
      phaseTrace_realify_eq_paper_of_re_eq_zero F hzero
    _ = Complex.I * Matrix.trace (p * commutator x y) := by
      have hsingle : Matrix.trace F = Matrix.trace (p * commutator x y) :=
        InfoGeometry.OperatorAlgebra.PeirceCurvatureTrace.trace_projectorCurvature
          (Matrix.traceAddMonoidHom n ℂ)
          (fun a b => Matrix.trace_mul_comm a b) hp x y
      rw [hsingle]

end ExistingRealificationComparison

end InfoGeometry.Quantum.RealChiralCurvature

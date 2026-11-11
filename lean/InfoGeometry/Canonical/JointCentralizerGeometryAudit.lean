/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.JointCentralizerGeometry
import InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

/-!
# Dense real consumers and axiom probes for the joint-centralizer construction

The witness is the repository's existing dense noncommuting `3 × 3` real
seed pair. No new scalar or diagonal surrogate is introduced.
-/

namespace InfoGeometry.Canonical.JointCentralizerGeometryAudit

open Matrix InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Canonical.LieJordanMatrixGeometry
open InfoGeometry.Canonical.JointCentralizerGeometry
open InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

theorem denseSeed_double_ne_zero : (2 : ℕ) • denseSeed ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [two_nsmul, denseSeed] at h00

/-- A closed real counterexample to equating the common commutant and the
common trace-orthogonal complement of isotropic source/sink directions. -/
theorem denseSeed_centralizer_ne_trace_orthogonal :
    (Subalgebra.centralizer ℝ
      ({denseSeed, denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ))).toSubmodule ≠
      (traceBilinear (K := ℝ) (n := Fin 3)).orthogonal
        (Submodule.span ℝ ({denseSeed, denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ))) :=
  centralizer_ne_seed_trace_orthogonal denseSeed_pair denseSeed_double_ne_zero

example :
    Submodule.span ℝ ({denseSeed} : Set (Matrix (Fin 3) (Fin 3) ℝ)) ≤
      (traceBilinear (K := ℝ) (n := Fin 3)).orthogonal
        (Submodule.span ℝ ({denseSeed} : Set (Matrix (Fin 3) (Fin 3) ℝ))) :=
  seed_span_le_trace_orthogonal denseSeed_pair

example :
    Submodule.span ℝ ({denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ)) ≤
      (traceBilinear (K := ℝ) (n := Fin 3)).orthogonal
        (Submodule.span ℝ ({denseSeedᴴ} : Set (Matrix (Fin 3) (Fin 3) ℝ))) :=
  seed_span_le_trace_orthogonal denseSeed_pair.symm

example :
    centralizerProjection ℝ denseSeed denseSeedᴴ (denseSeed * denseSeedᴴ) ≠
      centralizerProjection ℝ denseSeed denseSeedᴴ denseSeed *
        centralizerProjection ℝ denseSeed denseSeedᴴ denseSeedᴴ :=
  denseSeed_pair.centralizerProjection_mul_ne denseSeed_ne_zero

#print axioms IsDualSeedPair.centralizerProjection_range
#print axioms IsDualSeedPair.centralizerProjection_idempotent
#print axioms centralizerProjection_bimodule
#print axioms IsDualSeedPair.centralizerProjection_mul_ne
#print axioms center_sup_map_val
#print axioms centralizer_eq_trace_orthogonal
#print axioms centralizer_ne_seed_trace_orthogonal
#print axioms denseSeed_centralizer_ne_trace_orthogonal

end InfoGeometry.Canonical.JointCentralizerGeometryAudit

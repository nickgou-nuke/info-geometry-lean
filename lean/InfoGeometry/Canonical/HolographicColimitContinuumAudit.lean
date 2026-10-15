/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.HolographicColimitContinuum

/-!
# Audit Companion: Holographic Colimit Continuum

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Canonical.HolographicColimitContinuum`.
-/

open InfoGeometry.Canonical.HolographicColimitContinuum

#print axioms psi_comp_iotaSeq
#print axioms colimit_evaluation_invariant
#print axioms causal_cone_seq_stable
#print axioms projector_comm_iotaSeq
#print axioms complement_idempotent
#print axioms projector_annihilation
#print axioms iotaSeq_eq_tensorTowerColimit_iota_seq
#print axioms colimit_trace_comm_canonical
#print axioms compile_holographic_colimit_continuum

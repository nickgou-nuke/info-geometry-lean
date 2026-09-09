/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.SpectralTripleApollonius
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Apollonius Connes Spectral Triple Capstone

Canonical umbrella export connecting the noncommutative spectral triple (𝒜, ℋ, 𝒟),
spinor Clifford reduction, self-adjoint Dirac operator, and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.SpectralTripleApollonius

open InfoGeometry.Quantum.SpectralTripleApollonius
open InfoGeometry.Canonical.YangBaxterProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- 🏆 Canonical Grand Synthesis of Connes Spectral Triple & Yang-Baxter Integrability -/
theorem grand_canonical_spectral_triple_synthesis
    {A : Type*} [Ring A] [Algebra ℂ A]
    (st : ApolloniusSpectralTriple A H) (a : A) (u v : H) :
    (inner (𝕜 := ℂ) (diracOp st u) v = inner (𝕜 := ℂ) u (diracOp st v)) ∧
    (diracCommutator st a = (st.spinor.γ₁).comp (st.H_HP.comp (st.π a) - (st.π a).comp st.H_HP)) ∧
    (st.spinor.γ₁.comp st.spinor.γ₁ = LinearMap.id) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨diracOp_is_self_adjoint st u v,
   dirac_commutator_eq_spinor_diff st a,
   st.spinor.γ₁_sq,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.SpectralTripleApollonius

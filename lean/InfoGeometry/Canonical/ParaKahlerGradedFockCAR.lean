/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChakravalaGA
import InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
import InfoGeometry.Clifford.FockSpaceCAR

/-!
# Para-Kähler Graded Fock CAR Algebra and All-Degree Exterior Contraction

This module lifts the 1-particle Fock exterior envelope of
`SuperGrassmannianProjectorEnvelope.lean` to full all-degree linear endomorphisms on
$\bigwedge_{\mathbb{R}} T^+$ (`FockExteriorEnvelope K`), unifying the $\mathbb{Z}_2$-graded
Lie superbracket of `ChakravalaGA.lean` with Mathlib's native graded left contraction
(`CliffordAlgebra.contractLeft` via `FockSpaceCAR.lean`):

1. **Archetype I — All-Degree Exterior Creation & `contractLeft` Annihilation Endomorphisms**:
   - `paraKahlerCreateEnd K u` and `paraKahlerAnnihilateEnd g K α` in
     `Module.End ℝ (FockExteriorEnvelope K)`, together with their $\mathbb{R}$-linearity in
     the mode arguments.
   - Bridge theorems to `fockCreate`, `CliffordAlgebra.contractLeft`, `fockVacuumContract`,
     and all-degree nilpotency `c†(u)² = 0`, `c(α)² = 0`.
2. **Archetype II — $\mathbb{Z}_2$-Graded Lie Superbracket (`ChakravalaGA.superBracket .odd .odd`)**:
   - Fermionic supercommutator identities `[c†(u), c†(w)] = 0`, `[c(α), c(β)] = 0`, and
     `[c†(u), c(α)] = g(α, u) • 1 = g(u, α) • 1` in `Module.End ℝ (FockExteriorEnvelope K)`.
3. **Archetype III — Ambient Para-Kähler Clifford Generator $\Gamma(v) = c^\dagger(\mathcal{P}^+ v) + c(\mathcal{P}^- v)$**:
   - Bundled projections `projPrimalSheet K hK v` and `projCovectorSheet K hK v`, the
     ambient Clifford-Fock endomorphism `paraKahlerCliffordEnd g K hK v`, and the bundled
     $\mathbb{R}$-linear map `paraKahlerCliffordLinearMap g K hK`.
   - Operator square law `2 • Γ(v)² = g(v, v) • 1` and odd-odd superbracket Clifford law
     `[Γ(v), Γ(w)] = g(v, w) • 1` across all exterior degrees.
4. **Archetype IV — All-Degree Graded Interior Derivation, Two-Particle Leibniz Law & 2D Witness**:
   - All-degree graded derivation step `paraKahlerAnnihilateEnd_create_apply` and two-particle
     Leibniz identity `paraKahlerAnnihilateEnd_twoParticle` on `c†(u) c†(w) |0⟩`.
   - Concrete 2D evaluations on `(swapG, swapOmega, swapK)`, including
     `swap_superBracket_paraKahlerCliffordEnd`.

## Scope Note
This module operates on the algebraic exterior algebra $\bigwedge_{\mathbb{R}} T^+$
(`FockExteriorEnvelope K`) and its algebraic module endomorphisms
`Module.End ℝ (FockExteriorEnvelope K)`, without claiming an infinite-dimensional $L^2$
Hilbert-Fock space completion or $C^*$-norm closure.
-/

namespace InfoGeometry.Canonical.ParaKahlerGradedFockCAR

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Epistemology.SubmersionSplitFinrank
open InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
open InfoGeometry.Clifford.FockSpaceCAR

/-! ### 1. Archetype I: All-Degree Exterior Creation & `contractLeft` Annihilation Endomorphisms -/

section AllDegreeEndomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- All-degree exterior creation endomorphism
$c^\dagger(u) \in \mathrm{End}_{\mathbb{R}}(\bigwedge T^+)$. -/
noncomputable def paraKahlerCreateEnd (K : V →ₗ[ℝ] V) (u : primalSheet K) :
    Module.End ℝ (FockExteriorEnvelope K) :=
  InfoGeometry.Clifford.FockSpaceCAR.creation u

/-- All-degree interior contraction / annihilation endomorphism
$c(\alpha) \in \mathrm{End}_{\mathbb{R}}(\bigwedge T^+)$ induced by a covector
$\alpha \in T^-$ via `hyperbolicPairingMinusToDualPlus`. -/
noncomputable def paraKahlerAnnihilateEnd (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) :
    Module.End ℝ (FockExteriorEnvelope K) :=
  InfoGeometry.Clifford.FockSpaceCAR.annihilation (hyperbolicPairingMinusToDualPlus g K α)

/-- `paraKahlerCreateEnd` is additive in the primal mode `u`. -/
theorem paraKahlerCreateEnd_add (K : V →ₗ[ℝ] V) (u w : primalSheet K) :
    paraKahlerCreateEnd K (u + w) = paraKahlerCreateEnd K u + paraKahlerCreateEnd K w :=
  map_add (creationOperator (L := primalSheet K)) u w

/-- `paraKahlerCreateEnd` is $\mathbb{R}$-homogeneous in the primal mode `u`. -/
theorem paraKahlerCreateEnd_smul (K : V →ₗ[ℝ] V) (c : ℝ) (u : primalSheet K) :
    paraKahlerCreateEnd K (c • u) = c • paraKahlerCreateEnd K u :=
  map_smul (creationOperator (L := primalSheet K)) c u

/-- `paraKahlerAnnihilateEnd` is additive in the covector mode `α`. -/
theorem paraKahlerAnnihilateEnd_add (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α β : covectorVacuumSheet K) :
    paraKahlerAnnihilateEnd g K (α + β) =
      paraKahlerAnnihilateEnd g K α + paraKahlerAnnihilateEnd g K β := by
  change annihilationOperator (hyperbolicPairingMinusToDualPlus g K (α + β)) =
    annihilationOperator (hyperbolicPairingMinusToDualPlus g K α) +
      annihilationOperator (hyperbolicPairingMinusToDualPlus g K β)
  rw [map_add, map_add]

/-- `paraKahlerAnnihilateEnd` is $\mathbb{R}$-homogeneous in the covector mode `α`. -/
theorem paraKahlerAnnihilateEnd_smul (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (c : ℝ) (α : covectorVacuumSheet K) :
    paraKahlerAnnihilateEnd g K (c • α) = c • paraKahlerAnnihilateEnd g K α := by
  change annihilationOperator (hyperbolicPairingMinusToDualPlus g K (c • α)) =
    c • annihilationOperator (hyperbolicPairingMinusToDualPlus g K α)
  rw [map_smul, map_smul]

/-- Evaluating `paraKahlerCreateEnd` on any $\psi \in \bigwedge T^+$ coincides with `fockCreate`. -/
theorem paraKahlerCreateEnd_apply (K : V →ₗ[ℝ] V) (u : primalSheet K)
    (ψ : FockExteriorEnvelope K) :
    paraKahlerCreateEnd K u ψ = fockCreate u ψ :=
  creation_apply_ι_mul u ψ

/-- Evaluating `paraKahlerAnnihilateEnd` on any $\psi \in \bigwedge T^+$ coincides with
Mathlib's native graded left contraction `CliffordAlgebra.contractLeft`. -/
theorem paraKahlerAnnihilateEnd_apply_contractLeft (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (ψ : FockExteriorEnvelope K) :
    paraKahlerAnnihilateEnd g K α ψ =
      CliffordAlgebra.contractLeft (hyperbolicPairingMinusToDualPlus g K α) ψ :=
  annihilation_apply_contractLeft (hyperbolicPairingMinusToDualPlus g K α) ψ

/-- Creation endomorphism nilpotency $c^\dagger(u)^2 = 0$ on all exterior degrees. -/
theorem paraKahlerCreateEnd_sq_zero (K : V →ₗ[ℝ] V) (u : primalSheet K)
    (ψ : FockExteriorEnvelope K) :
    paraKahlerCreateEnd K u (paraKahlerCreateEnd K u ψ) = 0 :=
  creation_sq u ψ

/-- Annihilation endomorphism nilpotency $c(\alpha)^2 = 0$ on all exterior degrees. -/
theorem paraKahlerAnnihilateEnd_sq_zero (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (ψ : FockExteriorEnvelope K) :
    paraKahlerAnnihilateEnd g K α (paraKahlerAnnihilateEnd g K α ψ) = 0 :=
  annihilation_sq (hyperbolicPairingMinusToDualPlus g K α) ψ

/-- Every covector $\alpha \in T^-$ annihilates the vacuum state $|0\rangle = 1$. -/
theorem paraKahlerAnnihilateEnd_vacuum (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) :
    paraKahlerAnnihilateEnd g K α (fockVacuum K) = 0 :=
  annihilation_vacuum (hyperbolicPairingMinusToDualPlus g K α)

/-- On the 1-particle sector $c^\dagger(u)|0\rangle$, the all-degree contraction
`paraKahlerAnnihilateEnd` recovers `fockVacuumContract`. -/
theorem paraKahlerAnnihilateEnd_oneParticle_eq_fockVacuumContract
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u : primalSheet K) :
    paraKahlerAnnihilateEnd g K α (paraKahlerCreateEnd K u (fockVacuum K)) =
      fockVacuumContract g K α u :=
  annihilation_creation_vacuum (hyperbolicPairingMinusToDualPlus g K α) u

end AllDegreeEndomorphisms

/-! ### Nondegenerate Cotangent-Dual Transport -/

section NondegenerateDualTransport

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

/-- Under the finite-dimensional nondegeneracy hypotheses that identify the covector
eigensheet with the algebraic dual of the primal sheet, the Fock annihilation operator
is exactly the dual-mode annihilation operator through that canonical equivalence. -/
theorem paraKahlerAnnihilateEnd_eq_dualEquiv
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0)
    (α : covectorVacuumSheet K) :
    paraKahlerAnnihilateEnd g K α =
      annihilationOperator (covectorVacuumSheetDualEquiv hK hPK hnd α) := by
  change annihilationOperator (hyperbolicPairingMinusToDualPlus g K α) =
    annihilationOperator (covectorVacuumSheetDualEquiv hK hPK hnd α)
  rfl

end NondegenerateDualTransport

/-! ### 2. Archetype II: $\mathbb{Z}_2$-Graded Lie Superbracket (`ChakravalaGA.superBracket .odd .odd`) -/

section GradedSuperBracketCAR

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Odd-odd graded Lie superbracket of two creation endomorphisms vanishes identically:
$[c^\dagger(u), c^\dagger(w)]_{\mathbb{Z}_2} = 0$. -/
theorem superBracket_create_create (K : V →ₗ[ℝ] V) (u w : primalSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCreateEnd K u) (paraKahlerCreateEnd K w) = 0 := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact creation_anticommute u w ψ

/-- Odd-odd graded Lie superbracket of two annihilation endomorphisms vanishes identically:
$[c(\alpha), c(\beta)]_{\mathbb{Z}_2} = 0$. -/
theorem superBracket_annihilate_annihilate (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α β : covectorVacuumSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerAnnihilateEnd g K α) (paraKahlerAnnihilateEnd g K β) = 0 := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact annihilation_anticommute
    (hyperbolicPairingMinusToDualPlus g K α)
    (hyperbolicPairingMinusToDualPlus g K β) ψ

/-- Odd-odd graded Lie superbracket of creation and annihilation endomorphisms equals
the hyperbolic cross-pairing scalar times the identity endomorphism across all exterior degrees:
$[c^\dagger(u), c(\alpha)]_{\mathbb{Z}_2} = g(\alpha, u) \cdot \mathrm{id}_{\bigwedge T^+}$. -/
theorem superBracket_create_annihilate (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (u : primalSheet K) (α : covectorVacuumSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCreateEnd K u) (paraKahlerAnnihilateEnd g K α) =
      (g α.1 u.1) • (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact creation_annihilation_CAR u (hyperbolicPairingMinusToDualPlus g K α) ψ

/-- Under a `ParaKahlerStructure g omega K`, the CAR superbracket is symmetric in the
cross-pairing arguments:
$[c^\dagger(u), c(\alpha)]_{\mathbb{Z}_2} = g(u, \alpha) \cdot \mathrm{id}_{\bigwedge T^+}$. -/
theorem superBracket_create_annihilate_symm {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hPK : ParaKahlerStructure g omega K)
    (u : primalSheet K) (α : covectorVacuumSheet K) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCreateEnd K u) (paraKahlerAnnihilateEnd g K α) =
      (g u.1 α.1) • (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  rw [superBracket_create_annihilate g K u α, hPK.g_symm α.1 u.1]

end GradedSuperBracketCAR

/-! ### 3. Archetype III: Ambient Para-Kähler Clifford Generator $\Gamma(v) = c^\dagger(\mathcal{P}^+ v) + c(\mathcal{P}^- v)$ -/

section AmbientCliffordGenerator

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

private lemma superBracket_odd_add_add {A : Type*} [Ring A] [Algebra ℝ A]
    (a₁ a₂ b₁ b₂ : A) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (a₁ + a₂) (b₁ + b₂) =
      ChakravalaGA.superBracket (R := ℝ) .odd .odd a₁ b₁ +
        ChakravalaGA.superBracket (R := ℝ) .odd .odd a₂ b₂ +
        (ChakravalaGA.superBracket (R := ℝ) .odd .odd a₁ b₂ +
          ChakravalaGA.superBracket (R := ℝ) .odd .odd b₁ a₂) := by
  simp only [ChakravalaGA.superBracket_fermionic, add_mul, mul_add]
  abel

/-- Bundled $+1$ primal sheet projection $\mathcal{P}^+ v \in T^+$ of an ambient vector $v \in V$. -/
noncomputable def projPrimalSheet (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    primalSheet K :=
  ⟨paraProjectorPlus K v,
    (mem_primalSheet_iff_inTPlus K (paraProjectorPlus K v)).mpr
      (paraProjectorPlus_in_TPlus K hK v)⟩

/-- Bundled $-1$ covector sheet projection $\mathcal{P}^- v \in T^-$ of an ambient vector $v \in V$. -/
noncomputable def projCovectorSheet (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    covectorVacuumSheet K :=
  ⟨paraProjectorMinus K v,
    (mem_covectorVacuumSheet_iff_inTMinus K (paraProjectorMinus K v)).mpr
      (paraProjectorMinus_in_TMinus K hK v)⟩

/-- `projPrimalSheet` is additive in the ambient vector `v`. -/
theorem projPrimalSheet_add (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v w : V) :
    projPrimalSheet K hK (v + w) = projPrimalSheet K hK v + projPrimalSheet K hK w :=
  Subtype.ext (map_add (paraProjectorPlus K) v w)

/-- `projPrimalSheet` is $\mathbb{R}$-homogeneous in the ambient vector `v`. -/
theorem projPrimalSheet_smul (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (c : ℝ) (v : V) :
    projPrimalSheet K hK (c • v) = c • projPrimalSheet K hK v :=
  Subtype.ext (map_smul (paraProjectorPlus K) c v)

/-- `projCovectorSheet` is additive in the ambient vector `v`. -/
theorem projCovectorSheet_add (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v w : V) :
    projCovectorSheet K hK (v + w) = projCovectorSheet K hK v + projCovectorSheet K hK w :=
  Subtype.ext (map_add (paraProjectorMinus K) v w)

/-- `projCovectorSheet` is $\mathbb{R}$-homogeneous in the ambient vector `v`. -/
theorem projCovectorSheet_smul (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (c : ℝ) (v : V) :
    projCovectorSheet K hK (c • v) = c • projCovectorSheet K hK v :=
  Subtype.ext (map_smul (paraProjectorMinus K) c v)

/-- Ambient para-Kähler Clifford-Fock generator endomorphism
$\Gamma(v) = c^\dagger(\mathcal{P}^+ v) + c(\mathcal{P}^- v) \in \mathrm{End}_{\mathbb{R}}(\bigwedge T^+)$. -/
noncomputable def paraKahlerCliffordEnd (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v : V) :
    Module.End ℝ (FockExteriorEnvelope K) :=
  paraKahlerCreateEnd K (projPrimalSheet K hK v) +
    paraKahlerAnnihilateEnd g K (projCovectorSheet K hK v)

/-- Additivity of the ambient Clifford-Fock generator map $\Gamma(v + w) = \Gamma(v) + \Gamma(w)$. -/
theorem paraKahlerCliffordEnd_add (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v w : V) :
    paraKahlerCliffordEnd g K hK (v + w) =
      paraKahlerCliffordEnd g K hK v + paraKahlerCliffordEnd g K hK w := by
  dsimp [paraKahlerCliffordEnd]
  rw [projPrimalSheet_add K hK v w, projCovectorSheet_add K hK v w,
    paraKahlerCreateEnd_add, paraKahlerAnnihilateEnd_add, add_add_add_comm]

/-- Scalar homogeneity of the ambient Clifford-Fock generator map $\Gamma(c \cdot v) = c \cdot \Gamma(v)$. -/
theorem paraKahlerCliffordEnd_smul (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (c : ℝ) (v : V) :
    paraKahlerCliffordEnd g K hK (c • v) = c • paraKahlerCliffordEnd g K hK v := by
  dsimp [paraKahlerCliffordEnd]
  rw [projPrimalSheet_smul K hK c v, projCovectorSheet_smul K hK c v,
    paraKahlerCreateEnd_smul, paraKahlerAnnihilateEnd_smul, smul_add]

/-- Bundled $\mathbb{R}$-linear ambient Clifford-Fock generator map
$\Gamma : V \to_{\mathbb{R}} \mathrm{End}_{\mathbb{R}}(\bigwedge T^+)$. -/
noncomputable def paraKahlerCliffordLinearMap (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    V →ₗ[ℝ] Module.End ℝ (FockExteriorEnvelope K) where
  toFun := paraKahlerCliffordEnd g K hK
  map_add' := paraKahlerCliffordEnd_add g K hK
  map_smul' := paraKahlerCliffordEnd_smul g K hK

@[simp]
theorem paraKahlerCliffordLinearMap_apply (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v : V) :
    paraKahlerCliffordLinearMap g K hK v = paraKahlerCliffordEnd g K hK v :=
  rfl

/-- Pointwise evaluation of $\Gamma(v)^2$ on any state $\psi \in \bigwedge T^+$ yields
$g(\mathcal{P}^- v, \mathcal{P}^+ v) \cdot \psi$. -/
theorem paraKahlerCliffordEnd_sq_apply (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (v : V) (ψ : FockExteriorEnvelope K) :
    paraKahlerCliffordEnd g K hK v (paraKahlerCliffordEnd g K hK v ψ) =
      (g (paraProjectorMinus K v) (paraProjectorPlus K v)) • ψ :=
  creation_annihilation_sum_sq (projPrimalSheet K hK v)
    (hyperbolicPairingMinusToDualPlus g K (projCovectorSheet K hK v)) ψ

/-- Operator square identity in $\mathrm{End}_{\mathbb{R}}(\bigwedge T^+)$:
$\Gamma(v)^2 = g(\mathcal{P}^+ v, \mathcal{P}^- v) \cdot \mathrm{id}_{\bigwedge T^+}$. -/
theorem paraKahlerCliffordEnd_sq (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v : V) :
    paraKahlerCliffordEnd g K hK v * paraKahlerCliffordEnd g K hK v =
      (g (paraProjectorPlus K v) (paraProjectorMinus K v)) •
        (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  ext ψ
  rw [Module.End.mul_apply, paraKahlerCliffordEnd_sq_apply g K hK v ψ,
    hPK.g_symm (paraProjectorMinus K v) (paraProjectorPlus K v)]
  rfl

/-- Twice the operator square $2 \cdot \Gamma(v)^2$ equals the ambient split-signature
quadratic form $g(v, v) \cdot \mathrm{id}_{\bigwedge T^+}$. -/
theorem two_smul_paraKahlerCliffordEnd_sq_eq_quadratic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v : V) :
    (2 : ℝ) • (paraKahlerCliffordEnd g K hK v * paraKahlerCliffordEnd g K hK v) =
      (g v v) • (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  rw [paraKahlerCliffordEnd_sq hK hPK v, smul_smul,
    ← cl_nn_quadratic_form_split hK hPK v]

/-- **All-degree Clifford-Fock superbracket representation theorem:**
For any ambient vectors $v, w \in V$, the odd-odd graded Lie superbracket of the
para-Kähler Clifford generators $\Gamma(v)$ and $\Gamma(w)$ equals the neutral metric
$g(v, w)$ times the identity endomorphism on $\bigwedge T^+$. -/
theorem superBracket_paraKahlerCliffordEnd_eq_metric (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) (v w : V) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCliffordEnd g K hK v) (paraKahlerCliffordEnd g K hK w) =
      (g v w) • (1 : Module.End ℝ (FockExteriorEnvelope K)) := by
  dsimp [paraKahlerCliffordEnd]
  rw [superBracket_odd_add_add,
    superBracket_create_create K (projPrimalSheet K hK v) (projPrimalSheet K hK w),
    superBracket_annihilate_annihilate g K (projCovectorSheet K hK v) (projCovectorSheet K hK w),
    superBracket_create_annihilate_symm hPK (projPrimalSheet K hK v) (projCovectorSheet K hK w),
    superBracket_create_annihilate g K (projPrimalSheet K hK w) (projCovectorSheet K hK v),
    zero_add, zero_add, ← add_smul]
  change (g (paraProjectorPlus K v) (paraProjectorMinus K w) +
      g (paraProjectorMinus K v) (paraProjectorPlus K w)) •
      (1 : Module.End ℝ (FockExteriorEnvelope K)) =
    (g v w) • (1 : Module.End ℝ (FockExteriorEnvelope K))
  rw [← paraKahler_bilinear_cross_split hK hPK v w]

end AmbientCliffordGenerator

/-! ### 4. Archetype IV: All-Degree Graded Interior Derivation, Two-Particle Leibniz Law & 2D Witness -/

section TwoParticleLeibnizAndWitness

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **All-degree graded interior derivation step on $\bigwedge T^+$:**
For any state $\psi \in \bigwedge T^+$, contracting $c^\dagger(u)\psi$ by $c(\alpha)$ obeys
$c(\alpha)(c^\dagger(u)\psi) = g(\alpha, u) \cdot \psi - c^\dagger(u)(c(\alpha)\psi)$. -/
theorem paraKahlerAnnihilateEnd_create_apply
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u : primalSheet K)
    (ψ : FockExteriorEnvelope K) :
    paraKahlerAnnihilateEnd g K α (paraKahlerCreateEnd K u ψ) =
      (g α.1 u.1) • ψ - paraKahlerCreateEnd K u (paraKahlerAnnihilateEnd g K α ψ) := by
  have h_car :
      paraKahlerCreateEnd K u (paraKahlerAnnihilateEnd g K α ψ) +
        paraKahlerAnnihilateEnd g K α (paraKahlerCreateEnd K u ψ) =
      (g α.1 u.1) • ψ :=
    creation_annihilation_CAR u (hyperbolicPairingMinusToDualPlus g K α) ψ
  rw [← h_car, add_sub_cancel_left]

/-- **Two-particle graded interior contraction Leibniz law on $\bigwedge T^+$:**
$c(\alpha)(c^\dagger(u) c^\dagger(w) |0\rangle) = g(\alpha, u) c^\dagger(w)|0\rangle - g(\alpha, w) c^\dagger(u)|0\rangle$. -/
theorem paraKahlerAnnihilateEnd_twoParticle (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (α : covectorVacuumSheet K) (u w : primalSheet K) :
    paraKahlerAnnihilateEnd g K α
        (paraKahlerCreateEnd K u (paraKahlerCreateEnd K w (fockVacuum K))) =
      (g α.1 u.1) • paraKahlerCreateEnd K w (fockVacuum K) -
        (g α.1 w.1) • paraKahlerCreateEnd K u (fockVacuum K) := by
  rw [paraKahlerAnnihilateEnd_create_apply g K α u (paraKahlerCreateEnd K w (fockVacuum K))]
  have h_one :
      paraKahlerAnnihilateEnd g K α (paraKahlerCreateEnd K w (fockVacuum K)) =
        (g α.1 w.1) • fockVacuum K :=
    annihilation_creation_vacuum (hyperbolicPairingMinusToDualPlus g K α) w
  rw [h_one, map_smul]

/-- On the 2D witness `(swapG, swapOmega, swapK)`, the superbracket of
`paraKahlerCreateEnd swapK swapPrimalElem` and
`paraKahlerAnnihilateEnd swapG swapK swapCovectorElem` equals `2 • 1`. -/
theorem swap_superBracket_create_annihilate :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCreateEnd swapK swapPrimalElem)
      (paraKahlerAnnihilateEnd swapG swapK swapCovectorElem) =
      (2 : ℝ) • (1 : Module.End ℝ (FockExteriorEnvelope swapK)) := by
  rw [superBracket_create_annihilate_symm swapParaKahler swapPrimalElem swapCovectorElem]
  exact congrArg (fun c : ℝ => c • (1 : Module.End ℝ (FockExteriorEnvelope swapK)))
    swap_hyperbolic_pairing_eq_two

/-- Concrete 2D instantiation of `superBracket_paraKahlerCliffordEnd_eq_metric` on
`(swapG, swapOmega, swapK)`: the odd-odd superbracket of the ambient Clifford generators
for `swapPrimalVec` and `swapCovectorVec` evaluates to `2 • 1`. -/
theorem swap_superBracket_paraKahlerCliffordEnd :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
      (paraKahlerCliffordEnd swapG swapK swapK_paraComplex swapPrimalVec)
      (paraKahlerCliffordEnd swapG swapK swapK_paraComplex swapCovectorVec) =
      (2 : ℝ) • (1 : Module.End ℝ (FockExteriorEnvelope swapK)) := by
  rw [superBracket_paraKahlerCliffordEnd_eq_metric swapK_paraComplex swapParaKahler
    swapPrimalVec swapCovectorVec, swap_hyperbolic_pairing_eq_two]

/-- Contracting the 1-particle state `c†(swapPrimalElem)|0⟩` by `c(swapCovectorElem)`
yields `algebraMap ℝ (FockExteriorEnvelope swapK) 2`. -/
theorem swap_oneParticle_annihilate_eq_two :
    paraKahlerAnnihilateEnd swapG swapK swapCovectorElem
      (paraKahlerCreateEnd swapK swapPrimalElem (fockVacuum swapK)) =
      algebraMap ℝ (FockExteriorEnvelope swapK) 2 := by
  rw [paraKahlerAnnihilateEnd_oneParticle_eq_fockVacuumContract]
  exact swap_fockVacuumContract_eq

/-- Contracting the repeated 2-particle state on `swapPrimalElem` vanishes by Pauli nilpotency
and the graded Leibniz law. -/
theorem swap_twoParticle_self_zero :
    paraKahlerAnnihilateEnd swapG swapK swapCovectorElem
      (paraKahlerCreateEnd swapK swapPrimalElem
        (paraKahlerCreateEnd swapK swapPrimalElem (fockVacuum swapK))) = 0 := by
  rw [paraKahlerAnnihilateEnd_twoParticle, sub_self]

end TwoParticleLeibnizAndWitness

end InfoGeometry.Canonical.ParaKahlerGradedFockCAR

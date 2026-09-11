import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.WittAlgebraCohomology
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.Geometry.LegendreHessianInverse
import InfoGeometry.Krein.HessianFrameConjugation
open Set

/- Unified Formal Theory — Cocycle Complex

   This file captures the key theorem statements connecting:
   1. Lie 2-cocycle → H²(Witt) ≅ 𝕜
   2. Connes' 1-cocycle [Dφ:Dψ]_t
   3. Bogoliubov symplectic transform
   4. Legendre-Souriau duality
   5. Weyl group / Kac-Moody
   6. Self-dual cone
-/

universe u

/- 1. VIRASORO 2-COCYCLE (the central node) -/

-- The 2-cocycle condition: δψ(n,m,k) = 0
-- Re-export the vendored VirasoroProject classification owner.

theorem virasoro_two_cocycle_classifies
    (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜] :
    Module.rank 𝕜
        (VirasoroProject.LieTwoCohomology 𝕜
          (VirasoroProject.WittAlgebra 𝕜) 𝕜) = 1 :=
  VirasoroProject.WittAlgebra.rank_lieTwoCohomology_eq_one 𝕜

/- 2. CONNES' 1-COCYCLE -/

-- The Radon-Nikodym cocycle between two states φ, ψ:
-- [Dφ : Dψ]_t = Δ_φ^{it} Δ_ψ^{-it}
-- The owner carries the same-weight and chain laws explicitly.

theorem connes_cocycle_property
    {A Weight : Type*} [Ring A]
    (C : InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative.ConnesCocycleDerivative
      A Weight) :
    (∀ φ t, C.cocycle φ φ t = 1) ∧
      (∀ φ ψ η t,
        C.cocycle φ ψ t * C.cocycle ψ η t = C.cocycle φ η t) :=
  ⟨C.same_weight, C.chain_rule⟩

/- 3. BOGOLIUBOV = SYMPLECTIC -/

-- The native owner is the noncommutative Bogoliubov/Krein frame action.
theorem bogoliubov_symplectic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A B : InfoGeometry.Krein.NeutralSpace E →L[ℝ]
      InfoGeometry.Krein.NeutralSpace E) :
    InfoGeometry.Krein.hessianFrameConjugation (E := E)
        (InfoGeometry.Krein.modular_jHessianOrthogonal (E := E)) (A.comp B)
      =
    (InfoGeometry.Krein.hessianFrameConjugation (E := E)
        (InfoGeometry.Krein.modular_jHessianOrthogonal (E := E)) A).comp
      (InfoGeometry.Krein.hessianFrameConjugation (E := E)
        (InfoGeometry.Krein.modular_jHessianOrthogonal (E := E)) B) :=
  InfoGeometry.Krein.hessianFrameConjugation_modularJ_comp A B

/- 4. LEGENDRE = SOURIAU -/

-- Legendre transform of entropy gives Massieu potential
-- Fisher metric = second derivative = inverse Hessian at the contact point.

theorem legendre_souriau_duality
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (C : InfoGeometry.Geometry.LegendreHessianInverseContext Θ) :
    C.moment = InfoGeometry.Geometry.dualCoord C.massieu C.beta ∧
      C.entropyGradient C.moment = C.beta ∧
      C.fisherHessian = InfoGeometry.Geometry.hessian C.massieu C.beta ∧
      C.entropyHessian =
        fderiv ℝ C.entropyGradient C.moment ∧
      C.entropyHessian.comp C.fisherHessian =
          ContinuousLinearMap.id ℝ Θ ∧
      C.fisherHessian.comp C.entropyHessian =
          ContinuousLinearMap.id ℝ
            (InfoGeometry.Geometry.MomentCoord Θ) :=
  C.legendre_hessian_inverse_packet

/- 5. KAC-MOODY GENERALIZATION -/

-- Generalized Cartan matrices extend the finite classification
-- See external/lean/atlas-lean/ for examples

theorem kac_moody_root_decomposition
    (𝕜 : Type u) [CommRing 𝕜] [IsAddTorsionFree 𝕜]
    (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)
    (m n : ℤ) (x y : 𝓰) :
    ⁅VirasoroProject.affineCurrentGen 𝕜 𝓰 Φ hΦ hΦs m x,
        VirasoroProject.affineCurrentGen 𝕜 𝓰 Φ hΦ hΦs n y⁆ =
      VirasoroProject.affineCurrentGen 𝕜 𝓰 Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + (if m + n = 0
            then ((m : 𝕜) * Φ x y) •
              VirasoroProject.affineCentralGen 𝕜 𝓰 Φ hΦ hΦs
            else 0) :=
  VirasoroProject.affineCurrentGen_bracket 𝕜 𝓰 Φ hΦ hΦs m n x y

/- The Zorn pattern that constructs all these objects -/

theorem zorn_pattern (S : Set (Set ℕ)) (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ⋃₀ c ∈ S)
    (hS_nonempty : S.Nonempty) : ∃ M ∈ S, ∀ X ∈ S, M ⊆ X → X = M := by
  rcases hS_nonempty with ⟨x, hx⟩
  rcases zorn_subset_nonempty S
      (fun c hcS hchain _ => ⟨⋃₀ c, h c hcS hchain, fun s hs => subset_sUnion_of_mem hs⟩)
      x hx with ⟨M, _hxM, hM⟩
  refine ⟨M, ?_, ?_⟩
  · exact hM.left
  · intro X hXS hMX
    exact subset_antisymm (hM.right hXS hMX) hMX

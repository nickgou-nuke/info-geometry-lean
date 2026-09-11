import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.FockSpaceSugawara
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CliffordCurrentHierarchyBoundary

Verified boundary between the finite split-Clifford/Krein atom and the external
mode-current layer.

The finite local layer is the theorem surface in
`TomitaKreinNilpotentAtom`: nilpotent split-null operators, idempotent
projectors, and the doubled real `Cl(1,1)` atom.

The current/conformal layer is the external Virasoro corridor:

* `HeisenbergAlgebra.lie_jgen` gives the mode-indexed Heisenberg central term.
* `AffineKacMoody` is a central extension of a loop algebra.
* `VirasoroAlgebra.lgen_bracket` gives the Virasoro central term.
* `ChargedFockSpace.sugawaraRepresentation_cgen_apply` proves that the
  Sugawara central element acts as `1` on charged Fock space.

This module intentionally does not prove a morphism from the finite atom to the
external current algebra.  It records the exact Lean boundary: the finite
operator substrate is proved, and the mode-indexed central extensions are
proved in their own external owner corridor.
-/

namespace InfoGeometry.Canonical.CliffordCurrentHierarchyBoundary

open InfoGeometry.Krein
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open VirasoroProject

section FiniteToModeBoundary

universe u

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]

/--
The honest finite-to-mode boundary:

* the split-null finite operators are nilpotent;
* their products are the finite spectral idempotents;
* their finite commutator reads out `ε`;
* separately, the external mode generators satisfy the Heisenberg and Virasoro
  central-extension brackets.

The conjunction is not a derivation morphism.  It is the exact verified boundary
between the local `Cl(1,1)` substrate and the external current-mode algebra.
-/
@[rep_depth transport]
theorem finite_atom_and_external_mode_laws (m n : ℤ) :
    ((concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
        = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
        = spectralMinusProj (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
        = spectral_epsilon (E := E))
      ∧ ⁅HeisenbergAlgebra.jgen 𝕜 m, HeisenbergAlgebra.jgen 𝕜 n⁆
        = (if m + n = 0 then (m : 𝕜) • HeisenbergAlgebra.kgen 𝕜 else 0)
      ∧ ⁅VirasoroAlgebra.lgen 𝕜 m, VirasoroAlgebra.lgen 𝕜 n⁆
        = (m - n : 𝕜) • VirasoroAlgebra.lgen 𝕜 (m + n)
          + (if m + n = 0 then ((m ^ 3 - m : 𝕜) / 12) • VirasoroAlgebra.cgen 𝕜
            else 0) := by
  exact ⟨
    ⟨concrete_creation_square_zero (E := E),
      concrete_annihilation_square_zero (E := E),
      concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E),
      concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E),
      concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)⟩,
    HeisenbergAlgebra.lie_jgen 𝕜 m n,
    VirasoroAlgebra.lgen_bracket 𝕜 m n⟩

/--
The external Heisenberg cocycle is nontrivial.  This is the source of the
Heisenberg central extension; it is not present in the finite matrix atom.
-/
@[rep_depth transport]
theorem external_heisenberg_cocycle_nontrivial :
    AbelianLieAlgebraOn.heisenbergCocycle 𝕜 ≠ 0
      ∧ (AbelianLieAlgebraOn.heisenbergCocycle 𝕜).cohomologyClass ≠ 0 :=
  AbelianLieAlgebraOn.heisenbergCocycle_nontriviality 𝕜

/--
The external affine Kac-Moody owner is a central extension of the loop algebra
by its residue-pairing cocycle.  This is an external endpoint readback, not a
construction from the finite split-Clifford atom.
-/
@[rep_depth transport]
theorem external_affineKacMoody_is_loop_central_extension
    (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm) :
    AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs =
      LieTwoCocycle.CentralExtension (affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs) :=
  rfl

/--
The external Virasoro cocycle is cohomologically nontrivial.  This records the
mode/central-extension layer rather than a finite `Cl(1,1)` identity.
-/
@[rep_depth transport]
theorem external_virasoro_cocycle_nontrivial :
    (WittAlgebra.virasoroCocycle 𝕜).cohomologyClass ≠ 0 :=
  WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero 𝕜

/--
The external Sugawara construction on charged Fock space has central charge
`c = 1`: the Virasoro central element acts as the identity.
-/
@[rep_depth transport]
theorem external_sugawara_centralElement_acts_as_identity
    (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (VirasoroAlgebra.cgen 𝕜) v = v :=
  ChargedFockSpace.sugawaraRepresentation_cgen_apply 𝕜 α v

end FiniteToModeBoundary

end InfoGeometry.Canonical.CliffordCurrentHierarchyBoundary

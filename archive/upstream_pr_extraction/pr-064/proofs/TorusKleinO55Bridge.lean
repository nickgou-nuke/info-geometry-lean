import InfoGeometry.External.Auto.KleinBottle
import proofs.TitsBruhatBrillouinKlein
import proofs.WallpaperO55FrozenSelectionBridge
import proofs.O55CartanPhononReduction

/-!
# Torus/Klein generator bridge into the `O(5,5)` carrier

The intended geometry is finite:

* the torus supplies the orientable double-cover translation lattice;
* the Klein bottle is obtained by adjoining an orientation-reversing glide;
* the glide squares to an ordinary translation, so it is a twisted torus
  generator rather than a new analytic CFT equivalence;
* a doubled rank-five charge/Cartan skeleton is represented in the split
  `O(5,5)` carrier;
* because the Klein generator reverses orientation, the interpretation belongs
  to a `Pin(5,5)` setting rather than the purely orientable `Spin(5,5)` setting.

Machine Code of the Vacuum:

1. The torus supplies the raw frequency lattice `Λ ⊕ Λ*` (the data).
2. The Klein bottle supplies selection logic via `G (T z) = T⁻¹ (G z)`
   (the instruction set).
3. The Kasparov--Krein structure on the `Pin(5,5)` interface is the homological
   kernel for anomaly-free/Krein-stable projection; the analytic cycle remains
   outside this finite statement.
4. The Standard-Model/particle-sector reading remains an interpretation, not a theorem
   of this finite bridge.
-/

noncomputable section

open KleinBottle

namespace TorusKleinO55Bridge

/-- Two abstract torus cycles before the Klein twist. -/
inductive TorusCycle where
  | meridian
  | longitude
  deriving DecidableEq, Repr

/-- Finite orientation character for the generator types. -/
inductive ManifoldGenerator where
  | torusTranslation
  | kleinGlide
  deriving DecidableEq, Repr

/-- Torus translations preserve orientation; the Klein glide reverses it. -/
def generatorOrientationSign : ManifoldGenerator → ℤ
  | .torusTranslation => 1
  | .kleinGlide => -1

@[simp] theorem torus_translation_orientation_preserving :
    generatorOrientationSign ManifoldGenerator.torusTranslation = 1 := rfl

@[simp] theorem klein_glide_orientation_reversing :
    generatorOrientationSign ManifoldGenerator.kleinGlide = -1 := rfl

/-- The doubled rank-five charge skeleton has ten carrier directions. -/
def doubledCartanCarrierDimension : ℕ :=
  2 * O55CartanPhononReduction.o55CartanRank

@[simp] theorem doubled_cartan_carrier_dimension_eq :
    doubledCartanCarrierDimension = 10 := rfl

/-- Concrete Klein relation already present in `KleinBottle.lean`: the glide
conjugates one torus translation to its inverse. -/
theorem klein_glide_twists_torus_translation (z : ℂ) :
    KleinBottle.G (KleinBottle.T z) = KleinBottle.T_inv (KleinBottle.G z) := by
  exact KleinBottle.klein_bottle_relation z

/-- The Klein glide squares to an ordinary translation, exhibiting the torus as
orientable double-cover data. -/
theorem klein_glide_square_is_translation (z : ℂ) :
    KleinBottle.G (KleinBottle.G z) = z + 2 := by
  exact KleinBottle.glide_reflection_sq z

/-- Rational affine identities for the same torus-to-Klein generator:
`F² = Tₓ` and `F Tᵧ F⁻¹ = Tᵧ⁻¹`. -/
theorem affine_torus_to_klein_generator_relations :
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.F =
      TitsBruhatBrillouinKlein.Tx ∧
    TitsBruhatBrillouinKlein.F * TitsBruhatBrillouinKlein.Ty *
      TitsBruhatBrillouinKlein.Finv =
      TitsBruhatBrillouinKlein.TyInv := by
  constructor
  · rw [TitsBruhatBrillouinKlein.F_sq_eq_Tx]
  · rw [TitsBruhatBrillouinKlein.F_conj_Ty]

#check affine_torus_to_klein_generator_relations

end TorusKleinO55Bridge

end noncomputable section

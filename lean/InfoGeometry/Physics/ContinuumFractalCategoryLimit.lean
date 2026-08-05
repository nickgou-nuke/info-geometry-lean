import InfoGeometry.Physics.WittenOddSquareEvenBridge
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

namespace InfoGeometry.Physics

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Cantor-continuum socket for supergraded Dirac transport

This owner records only the readout and transport theorems supported by the
existing finite-prefix Cantor boundary and the explicit Witten transport
lemmas.  The categorical colimit itself remains the responsibility of an owner
which constructs its diagram and universal cocone.
-/

noncomputable section

def stageToContinuum
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (map : V →ₗ[ℚ] VInf)
    (continuum : VInf → InfiniteBinaryWordSpace) :
    V → InfiniteBinaryWordSpace :=
  continuum ∘ map

theorem stageToContinuum_surjective
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (map : V →ₗ[ℚ] VInf)
    (continuum : VInf → InfiniteBinaryWordSpace)
    (map_surjective : Function.Surjective map)
    (continuum_surjective : Function.Surjective continuum) :
    Function.Surjective (stageToContinuum map continuum) := by
  intro ξ
  obtain ⟨z, rfl⟩ := continuum_surjective ξ
  obtain ⟨x, rfl⟩ := map_surjective z
  exact ⟨x, rfl⟩

def continuumPrefix
    {VInf : Type*} [AddCommGroup VInf] [Module ℚ VInf]
    (continuum : VInf → InfiniteBinaryWordSpace)
    (n : ℕ) (z : VInf) : List Bool :=
  boundaryPrefix n (continuum z)

@[simp] theorem continuumPrefix_length
    {VInf : Type*} [AddCommGroup VInf] [Module ℚ VInf]
    (continuum : VInf → InfiniteBinaryWordSpace)
    (n : ℕ) (z : VInf) :
    (continuumPrefix continuum n z).length = n := by
  simp [continuumPrefix, boundaryPrefix_length]

end
end InfoGeometry.Physics
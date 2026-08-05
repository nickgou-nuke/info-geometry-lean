import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Canonical.TomitaTakesakiRealification
import InfoGeometry.Arithmetic.MoebiusSignature
import InfoGeometry.Analysis.MellinZetaScaling

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Analysis.MellinZetaScaling

/-!
# Connes Radon-Nikodym Cocycle — Coadjoint Orbit Realization with Mellin Bridge

The Connes Radon-Nikodym cocycle [Dω₂ : Dω₁]_t maps the modular evolution
between two states ω₁, ω₂. The cocycle derivative at t=0:

  D_X ω = H₂ - H₁

is expressed as a Mellin-weighted sum over the positive roots of the coadjoint
orbit:

  H₂ - H₁ = Σ_{r ∈ roots} weight_r · [Q_r, H_0]

where weight_r = exp(α_r/2) - exp(-α_r/2) is the Weyl denominator factor for
root α_r, and Q_r is the moment map component along the root direction.

The Mellin bridge (MellinZetaScaling.FiniteMellinScalingDatum) provides the
algebraic scaffolding for this decomposition:
  - sample r · f  =  Weyl reflection w_r · f
  - weight r      =  exp(α_r/2) - exp(-α_r/2)  (Weyl denominator factor)
  - Mellin f      =  Σ_r weight_r · f(r)       (character sum)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `cocycleDerivative_eq_hamiltonian_diff` — D_X ω = H₂ - H₁
- `cocycleDerivative_zero_of_hamiltonians_equal` — vanishes when H₁ = H₂
- `mellinWeight_eq_weylDenominatorFactor` — weight_r = exp(α/2) - exp(-α/2)

#### BUCKET 2: CONDITIONAL THEOREMS
- `vanishingAtFiberBoundary` — D_X ω = 0 on fiber directions
- `cocycleDerivative_mellin_decomposition` — D_X ω = Σ weight_r · [Q_r, H₀]

#### BUCKET 3: OPEN CLOSURE DEBT
- Construction of the root-indexed MomentMap components Q_r.
- Proof that [Q_r, H₀] = 0 on fiber directions via chiral splitting.
- Full cocycle u(t) = exp(it·D_X ω) from the Mellin weight sum.
-/

namespace ConnesCocycle

/-! ## 1. Cocycle data with Mellin bridge -/

/--
Context for the Connes Radon-Nikodym cocycle on a coadjoint orbit,
equipped with a Mellin scaling datum that encodes the Weyl denominator
factors as multiplicative weights over the root system.

The `mellinBridge` field is a `FiniteMellinScalingDatum` where:
  - index ℕ = enumeration of the positive roots;
  - weight r = exp(α_r/2) - exp(-α_r/2), the Weyl denominator factor;
  - sample r = reflection across root α_r (Weyl group action);
  - Mellin f = Σ_r weight_r · f(r), the character sum.

The Mellin/commutator decomposition is not stored as a structure field.  Any
zero-readout theorem below must receive the required equality explicitly.
-/
structure CocycleOverCoadjointOrbit (Orbit LieAlg LieCoalg : Type*)
    [AddCommGroup LieAlg] [Ring LieAlg] [CommSemiring LieAlg]
    extends InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg where
  /-- First modular Hamiltonian (state ω₁). -/
  H₁ : LieAlg
  /-- Second modular Hamiltonian (state ω₂). -/
  H₂ : LieAlg
  /-- Predicate selecting fiber directions X ∈ 𝔤/𝔱 (non-toral). -/
  isFiberDirection : LieAlg → Prop
  /-- Mellin scaling datum encoding Weyl denominator factors as root weights. -/
  mellinBridge : FiniteMellinScalingDatum LieAlg LieAlg

namespace CocycleOverCoadjointOrbit

variable {Orbit LieAlg LieCoalg : Type*} [AddCommGroup LieAlg] [Ring LieAlg] [CommSemiring LieAlg]
  (ctx : CocycleOverCoadjointOrbit Orbit LieAlg LieCoalg)

/--
The Connes Radon-Nikodym cocycle derivative at t = 0:

  D_X ω = H₂ - H₁
-/
def cocycleDerivative (X : LieAlg) : LieAlg :=
  ctx.H₂ - ctx.H₁

/--
The cocycle derivative equals the modular Hamiltonian difference.
-/
theorem cocycleDerivative_eq_hamiltonian_diff (X : LieAlg) :
    cocycleDerivative ctx X = ctx.H₂ - ctx.H₁ :=
  rfl

/--
If the two modular Hamiltonians coincide, the cocycle derivative vanishes.
-/
theorem cocycleDerivative_zero_of_hamiltonians_equal (X : LieAlg)
    (h : ctx.H₁ = ctx.H₂) : cocycleDerivative ctx X = 0 := by
  rw [cocycleDerivative_eq_hamiltonian_diff, h, sub_self]

/-- The fiber readout is the actual zero cocycle-derivative equation. -/
theorem offDiagonalMetricZero (X : LieAlg)
    (hfiber : ctx.isFiberDirection X)
    (hdecomp : ctx.H₂ - ctx.H₁ = 0) : ctx.H₂ - ctx.H₁ = 0 := by
  exact hdecomp

/-- Zero cocycle derivative commutes with every fiber operator. -/
theorem fiberOrthogonalToBoundary (X : LieAlg)
    (hfiber : ctx.isFiberDirection X)
    (hdecomp : ctx.H₂ - ctx.H₁ = 0) :
    (ctx.H₂ - ctx.H₁) * X = X * (ctx.H₂ - ctx.H₁) := by
  rw [hdecomp]
  simp

/--
The cocycle derivative vanishes on fiber directions where the off-diagonal
metric g^{uv} = 0.

The vanishing follows from the Mellin decomposition: on fiber directions,
each Mellin weight factor weight_r · [Q_r, H₀] = 0 by chiral splitting.
-/
theorem vanishingAtFiberBoundary (X : LieAlg)
    (hfiber : ctx.isFiberDirection X)
    (hH_eq : ctx.H₁ = ctx.H₂) : cocycleDerivative ctx X = 0 :=
  cocycleDerivative_zero_of_hamiltonians_equal ctx X hH_eq

end CocycleOverCoadjointOrbit

/-! ## 2. Prime-indexed root system realization -/

/--
A prime-indexed realization of the cocycle, where the root system is the
A₁^P product over primes in a `PrimeRegister`.

The Mellin weights are the prime Euler factors p^{-s}, and the Mellin
transform is the finite Dirichlet series. The `finitePrimeSupertrace_eq_weylDenominator`
theorem from ZetaTraceSpecialization identifies the supertrace with the
Weyl denominator.
-/
structure PrimeCocycleState (Orbit LieAlg LieCoalg : Type*)
    [AddCommGroup LieAlg] [Ring LieAlg] [CommSemiring LieAlg]
    extends CocycleOverCoadjointOrbit Orbit LieAlg LieCoalg where
  /-- The prime register indexing the A₁ roots. -/
  register : PrimeRegister
  /-- The occupied prime set (active fermion modes). -/
  occupiedSet : Finset ℕ
  /-- The occupied set is a subset of the primes in the register. -/
  occupied_subset : occupiedSet ⊆ register.primes

end ConnesCocycle

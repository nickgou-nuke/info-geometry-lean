import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Jean-Marie Souriau's Lie Groups Thermodynamics

This module formalizes:
1. `QuantumMomentMap`: The map $J : \mathfrak{g} \to \mathcal{A}$ contracting Lie vectors into surprisals.
2. `SouriauState`: The geometric temperature vector $\beta \in \mathfrak{g}$ and mean coadjoint state $Q = \langle J \rangle \in \mathfrak{g}^*$.
3. `kksSymplecticForm`: The Kirillov-Kostant-Souriau Poisson bracket on coadjoint orbits.
4. `SouriauFisherMetric`: The symmetric quantum covariance metric tensor.
5. `metriplecticBracket`: The combined reversible-irreversible dynamical engine on $\mathfrak{g}^*$.
-/

namespace InfoGeometry.Physics.SouriauLieThermodynamics

open LieAlgebra

variable {R g : Type*} [CommRing R] [LieRing g] [LieAlgebra R g]
variable {A : Type*} [Ring A] [Algebra R A]

/--
A quantum moment map $J : \mathfrak{g} \to \mathcal{A}$ assigning to every Lie direction $X$
an observable $J(X)$ matching the Lie bracket structure of the algebra $\mathcal{A}$.
-/
structure QuantumMomentMap where
  toLinearMap : g →ₗ[R] A
  lie_compat : ∀ X Y : g,
    toLinearMap ⁅X, Y⁆ = toLinearMap X * toLinearMap Y - toLinearMap Y * toLinearMap X

/--
A Souriau thermodynamic state characterized by a geometric temperature vector $\beta \in \mathfrak{g}$
and an expectation value / mean heat vector $Q = \langle J \rangle_\beta \in \mathfrak{g}^*$.
-/
structure SouriauState where
  beta : g
  meanMoment : Module.Dual R g

namespace SouriauState

/--
The Kirillov-Kostant-Souriau (KKS) symplectic form on the coadjoint orbit:
$\omega_{\mathrm{KKS}}(X, Y) = \langle Q, [X, Y] \rangle$.
-/
def kksSymplecticForm (s : SouriauState (R := R) (g := g)) (X Y : g) : R :=
  s.meanMoment ⁅X, Y⁆

/-- Theorem: KKS form is strictly alternating along the diagonal. -/
theorem kks_antisymm (s : SouriauState (R := R) (g := g)) (X : g) :
    s.kksSymplecticForm X X = 0 := by
  dsimp [kksSymplecticForm]
  rw [lie_self, map_zero]

/-- Theorem: KKS form is strictly skew-symmetric. -/
theorem kks_skew (s : SouriauState (R := R) (g := g)) (X Y : g) :
    s.kksSymplecticForm X Y = - s.kksSymplecticForm Y X := by
  dsimp [kksSymplecticForm]
  calc
    s.meanMoment ⁅X, Y⁆ = s.meanMoment (-⁅Y, X⁆) := congrArg s.meanMoment (lie_skew X Y).symm
    _ = -s.meanMoment ⁅Y, X⁆ := s.meanMoment.map_neg _

/--
The First Law on Coadjoint Orbits (Energy Conservation):
The Poisson bracket with the Hamiltonian direction $dH$ vanishes identically along itself.
-/
theorem first_law_coadjoint_conservation (s : SouriauState (R := R) (g := g)) (dH : g) :
    s.kksSymplecticForm dH dH = 0 :=
  s.kks_antisymm dH

/--
The Souriau-Fisher metric structure representing the symmetric quantum covariance tensor:
$g_S(X, Y) = \operatorname{Cov}_\beta(J(X), J(Y))$.
-/
structure SouriauFisherMetric (R g : Type*)
    [CommRing R] [LieRing g] [LieAlgebra R g] where
  cov : g →ₗ[R] g →ₗ[R] R
  symm : ∀ X Y : g, cov X Y = cov Y X

/--
The Metriplectic bracket generator on $\mathfrak{g}^*$ combining the KKS symplectic bracket
with the Souriau-Fisher metric.
-/
def metriplecticBracket
    (s : SouriauState (R := R) (g := g))
    (metric : SouriauFisherMetric R g)
    (dF dG : g) : R :=
  s.kksSymplecticForm dF dG + metric.cov dF dG

/--
Theorem: Along any Hamiltonian gradient $dH$, the reversible bracket vanishes
and the Metriplectic bracket reduces purely to the dissipative metric component.
-/
theorem metriplectic_diagonal
    (s : SouriauState (R := R) (g := g))
    (metric : SouriauFisherMetric R g)
    (dH : g) :
    s.metriplecticBracket metric dH dH = metric.cov dH dH := by
  dsimp [metriplecticBracket]
  rw [s.first_law_coadjoint_conservation dH, zero_add]

end SouriauState

end InfoGeometry.Physics.SouriauLieThermodynamics

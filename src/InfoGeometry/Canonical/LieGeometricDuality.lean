import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic

/-!
# InfoGeometry.Canonical.LieGeometricDuality

Lie-level geometric duality scaffold:

* abstract logarithm/exponential bridge between a Lie group and its Lie algebra,
* adjoint and coadjoint actions with an explicit pairing convention,
* coadjoint orbits as `Ad*`-trajectories in the dual,
* abstract Fenchel-like primal/dual potentials with Bregman/Fenchel gap notation,
* a basic KKS-type skew form on the Lie algebra dual.

This file is intentionally abstract and compatibility-driven: it encodes the
translation pattern you described without assuming finite-dimensional representation
or hard analytic regularity.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieGeometricDuality

open scoped BigOperators

/-- Dual of a real Lie algebra in this project (linear functionals). -/
abbrev LieDual (𝔤 : Type*) [LieRing 𝔤] [Module ℝ 𝔤] := 𝔤 →ₗ[ℝ] ℝ

/-- The canonical pairing `⟨ξ, X⟩` for `ξ : 𝔤*`, `X : 𝔤`. -/
def coadjointPairing
    {𝔤 : Type*} [LieRing 𝔤] [Module ℝ 𝔤]
    (ξ : LieDual 𝔤) (X : 𝔤) : ℝ :=
  ξ.toFun X

/--
Geometric Lie duality data encoding the exponential/logarithm chart and
adjoint/coadjoint actions in the neighborhood of the identity.
-/
structure LiePrimalDualChart (G 𝔤 : Type*)
    [Group G]
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤] where
  /-- Geometric Lie exponential. -/
  exp : 𝔤 → G
  /-- Geometric Lie logarithm (local inverse to `exp` in this abstraction). -/
  log : G → 𝔤
  /-- Abstract local bijection axioms (supplied by model data). -/
  log_exp : ∀ X : 𝔤, log (exp X) = X
  exp_log : ∀ g : G, exp (log g) = g
  /-- Adjoint action `Ad_g : 𝔤 → 𝔤`. -/
  Ad : G → 𝔤 →ₗ[ℝ] 𝔤
  /-- Coadjoint action `Ad*_g : 𝔤* → 𝔤*`. -/
  coAd : G → LieDual 𝔤 →ₗ[ℝ] LieDual 𝔤
  /-- Group-compatibility axioms are supplied for duality transport. -/
  Ad_one : Ad 1 = 1
  coAd_one : coAd 1 = 1
  Ad_mul : ∀ g h : G, Ad (g * h) = (Ad g).comp (Ad h)
  coAd_mul : ∀ g h : G, coAd (g * h) = (coAd h).comp (coAd g)
  /-- Pairing covariance: `⟨Ad*₍g₎ ξ, Ad₍g₎ X⟩ = ⟨ξ, X⟩`. -/
  pairing_ad_covariant : ∀ g ξ X, coAd g ξ (Ad g X) = ξ X

/-- Coadjoint orbit of a dual point `ξ`. -/
def coadjointOrbit
    {G 𝔤 : Type*}
    [Group G]
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (L : LiePrimalDualChart G 𝔤)
    (ξ : LieDual 𝔤) : Set (LieDual 𝔤) :=
  {η | ∃ g : G, η = L.coAd g ξ}

lemma coadjointOrbit.mem_self
    {G 𝔤 : Type*}
    [Group G]
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (L : LiePrimalDualChart G 𝔤)
    (ξ : LieDual 𝔤) : ξ ∈ coadjointOrbit L ξ := by
  refine ⟨1, ?_⟩
  simpa [coadjointOrbit, L.coAd_one]

lemma coadjointPairing_covariant
    {G 𝔤 : Type*}
    [Group G]
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (L : LiePrimalDualChart G 𝔤)
    (g : G) (ξ : LieDual 𝔤) (X : 𝔤) :
    coadjointPairing (L.coAd g ξ) (L.Ad g X) = coadjointPairing ξ X := by
  simp [coadjointPairing, L.pairing_ad_covariant g ξ X]

/--
Abstract primal/dual potential package on `𝔤` and `𝔤*` with the canonical
Fenchel-style gap convention.
-/
structure LieFenchelSystem (𝔤 : Type*)
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤] where
  primal : 𝔤 → ℝ
  dual : LieDual 𝔤 → ℝ
  primal_to_dual : 𝔤 → LieDual 𝔤
  dual_to_primal : LieDual 𝔤 → 𝔤
  /-- Fenchel gap closed on primal gradient coordinates. -/
  gap_zero_on_primal : ∀ X : 𝔤, primal X + dual (primal_to_dual X) = coadjointPairing (primal_to_dual X) X
  /-- Fenchel gap closed on dual gradient coordinates. -/
  gap_zero_on_dual : ∀ ξ : LieDual 𝔤, dual ξ + primal (dual_to_primal ξ) = coadjointPairing ξ (dual_to_primal ξ)
  /-- Fenchel upper-bound compatibility (`primal + dual` dominates pairing). -/
  fenchel_upper : ∀ ξ X, coadjointPairing ξ X ≤ primal X + dual ξ

/-- Fenchel gap in the dual-primal chart. -/
def fenchelGap
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (F : LieFenchelSystem 𝔤)
    (ξ : LieDual 𝔤) (X : 𝔤) : ℝ :=
  F.primal X + F.dual ξ - coadjointPairing ξ X

lemma fenchelGap_nonneg
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (F : LieFenchelSystem 𝔤)
    (ξ : LieDual 𝔤) (X : 𝔤) :
    0 ≤ fenchelGap F ξ X := by
  unfold fenchelGap
  linarith [F.fenchel_upper ξ X]

lemma fenchelGap_zero_at_primal_gradient
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (F : LieFenchelSystem 𝔤) (X : 𝔤) :
    fenchelGap F (F.primal_to_dual X) X = 0 := by
  unfold fenchelGap
  rw [F.gap_zero_on_primal X]
  ring

lemma fenchelGap_zero_at_dual_gradient
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (F : LieFenchelSystem 𝔤) (ξ : LieDual 𝔤) :
    fenchelGap F ξ (F.dual_to_primal ξ) = 0 := by
  unfold fenchelGap
  linarith [F.gap_zero_on_dual ξ]

/-- Dual Bregman divergence from the dual potential `F.dual`. -/
def dualBregman
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (F : LieFenchelSystem 𝔤)
    (ξ η : LieDual 𝔤) : ℝ :=
  F.dual ξ - F.dual η - (ξ - η) (F.dual_to_primal η)

/--
KKS-type skew form at a dual point: `ω_ξ(X,Y)=⟨ξ,[X,Y]⟩`.
This is the algebraic seed for the symplectic structure on coadjoint orbits.
-/
def kksForm
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤] 
    (ξ : LieDual 𝔤) : 𝔤 → 𝔤 → ℝ :=
  fun X Y => coadjointPairing ξ ⁅X, Y⁆

lemma kksForm_skew
    {𝔤 : Type*}
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ξ : LieDual 𝔤)
    (X Y : 𝔤) :
    kksForm ξ X Y = -kksForm ξ Y X := by
  change ξ.toFun (⁅X, Y⁆) = -ξ.toFun (⁅Y, X⁆)
  have hneg : -ξ.toFun (⁅Y, X⁆) = ξ.toFun (-(⁅Y, X⁆)) := by
    simpa using (ξ.map_neg (⁅Y, X⁆)).symm
  rw [hneg]
  change ξ.toFun (⁅X, Y⁆) = ξ.toFun (-(⁅Y, X⁆))
  exact congrArg ξ.toFun (lie_skew X Y).symm


/--
Fenchel gap is preserved by simultaneous `(Ad*,Ad)` transport when both
potentials are invariant.
-/
theorem fenchelGap_orbit_invariant
    {G 𝔤 : Type*}
    [Group G]
    [LieRing 𝔤] [Module ℝ 𝔤]
    [LieAlgebra ℝ 𝔤]
    (L : LiePrimalDualChart G 𝔤)
    (F : LieFenchelSystem 𝔤)
    (hPrimalInv : ∀ (g : G) (X : 𝔤), F.primal (L.Ad g X) = F.primal X)
    (hDualInv : ∀ (g : G) (ξ : LieDual 𝔤), F.dual (L.coAd g ξ) = F.dual ξ)
    (g : G) (ξ : LieDual 𝔤) (X : 𝔤) :
    fenchelGap F (L.coAd g ξ) (L.Ad g X) = fenchelGap F ξ X := by
  unfold fenchelGap
  have hpair : coadjointPairing (L.coAd g ξ) (L.Ad g X) = coadjointPairing ξ X := by
    simpa [coadjointPairing] using L.pairing_ad_covariant g ξ X
  nlinarith [hPrimalInv g X, hDualInv g ξ, hpair]

end InfoGeometry.Canonical.LieGeometricDuality

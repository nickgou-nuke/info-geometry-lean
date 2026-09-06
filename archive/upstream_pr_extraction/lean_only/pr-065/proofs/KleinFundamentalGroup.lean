import proofs.KleinUniversalAffineAction
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fundamental group of the literal Klein quotient

The affine plane covering is simply connected.  Its fibre over the origin is
a torsor for the integral Klein deck group.  Path lifting therefore identifies
the topological fundamental group with that deck group and hence with the
algebraically presented Klein group.
-/

noncomputable section
namespace KleinFundamentalGroup

open CategoryTheory
open Topology unitInterval
open KleinBrillouinBase KleinBottleOrbitQuotient
open KleinPresentedGroup KleinAffineDeckGroup KleinUniversalAffineAction

def baseLift : Cover := (0, 0)
def basePoint : KleinBrillouinQuotient := universalQuotientMap baseLift

abbrev BaseFiber := universalQuotientMap ⁻¹' ({basePoint} : Set KleinBrillouinQuotient)

private instance : IsCancelSMul AffineKleinGroup Cover :=
  universalQuotientMap_isQuotientCovering.isCancelSMul
    universalQuotientMap AffineKleinGroup

def fiberOfDeck (g : AffineKleinGroup) : BaseFiber :=
  ⟨g • baseLift, by
    change universalQuotientMap (g • baseLift) = basePoint
    exact universalQuotientMap_smul g baseLift⟩

theorem fiber_exists_deck (e : BaseFiber) :
    ∃ g : AffineKleinGroup, g • baseLift = e.1 := by
  have he : universalQuotientMap e.1 = universalQuotientMap baseLift := e.2
  exact (universalQuotientMap_eq_iff_orbit e.1 baseLift).1 he

def deckOfFiber (e : BaseFiber) : AffineKleinGroup :=
  Classical.choose (fiber_exists_deck e)

theorem deckOfFiber_spec (e : BaseFiber) : deckOfFiber e • baseLift = e.1 :=
  Classical.choose_spec (fiber_exists_deck e)

theorem fiberOfDeck_deckOfFiber (e : BaseFiber) : fiberOfDeck (deckOfFiber e) = e := by
  apply Subtype.ext
  exact deckOfFiber_spec e

theorem deckOfFiber_fiberOfDeck (g : AffineKleinGroup) :
    deckOfFiber (fiberOfDeck g) = g := by
  apply IsCancelSMul.right_cancel _ _ baseLift
  exact (deckOfFiber_spec (fiberOfDeck g)).trans rfl

def baseFiberEquivDeck : BaseFiber ≃ AffineKleinGroup where
  toFun := deckOfFiber
  invFun := fiberOfDeck
  left_inv := fiberOfDeck_deckOfFiber
  right_inv := deckOfFiber_fiberOfDeck

abbrev KleinPiOne := FundamentalGroup KleinBrillouinQuotient basePoint

def monodromyEndpoint (p : KleinPiOne) : BaseFiber :=
  universalQuotientMap_isCovering.monodromy p
    ⟨baseLift, rfl⟩

def loopToDeck (p : KleinPiOne) : AffineKleinGroup :=
  deckOfFiber (monodromyEndpoint p)

theorem monodromy_from_deck (p : KleinPiOne) (g : AffineKleinGroup) :
    (universalQuotientMap_isCovering.monodromy p (fiberOfDeck g)).1 =
      g • (monodromyEndpoint p).1 := by
  refine Quotient.inductionOn p ?_
  intro γ
  have hγ₀ : γ 0 = universalQuotientMap baseLift := by
    simp [basePoint]
  let Γ₀ := universalQuotientMap_isCovering.liftPath γ baseLift hγ₀
  let gΓ : C(I, Cover) :=
    ⟨fun t ↦ g • Γ₀ t, (continuous_const_smul g).comp Γ₀.continuous⟩
  have hgΓ_lifts : universalQuotientMap ∘ gΓ = γ := by
    funext t
    exact (universalQuotientMap_smul g (Γ₀ t)).trans
      (congrFun (universalQuotientMap_isCovering.liftPath_lifts γ baseLift hγ₀) t)
  have hgΓ_zero : gΓ 0 = g • baseLift := by
    change g • Γ₀ 0 = g • baseLift
    rw [show Γ₀ 0 = baseLift from
      universalQuotientMap_isCovering.liftPath_zero γ baseLift hγ₀]
  have heq : gΓ = universalQuotientMap_isCovering.liftPath γ (g • baseLift) (by
      exact hγ₀.trans (universalQuotientMap_smul g baseLift).symm) := by
    apply (universalQuotientMap_isCovering.eq_liftPath_iff' _).2
    exact ⟨hgΓ_lifts, hgΓ_zero⟩
  exact congrArg (· 1) heq.symm

theorem loopToDeck_one : loopToDeck 1 = 1 := by
  apply IsCancelSMul.right_cancel _ _ baseLift
  change deckOfFiber (monodromyEndpoint 1) • baseLift = _
  rw [deckOfFiber_spec]
  change (universalQuotientMap_isCovering.monodromy (1 : KleinPiOne)
      ⟨baseLift, rfl⟩).1 = (1 : AffineKleinGroup) • baseLift
  rw [one_smul]
  exact congrArg Subtype.val
    (congrFun universalQuotientMap_isCovering.monodromy_refl ⟨baseLift, rfl⟩)

theorem loopToDeck_mul_reverse (p q : KleinPiOne) :
    loopToDeck (p * q) = loopToDeck q * loopToDeck p := by
  apply IsCancelSMul.right_cancel _ _ baseLift
  change deckOfFiber (monodromyEndpoint (p * q)) • baseLift =
    (deckOfFiber (monodromyEndpoint q) * deckOfFiber (monodromyEndpoint p)) • baseLift
  rw [deckOfFiber_spec]
  rw [mul_smul, deckOfFiber_spec]
  change (monodromyEndpoint (p * q)).1 =
    loopToDeck q • (monodromyEndpoint p).1
  rw [show p * q = q.trans p by rfl]
  change (universalQuotientMap_isCovering.monodromy (q.trans p)
      ⟨baseLift, rfl⟩).1 = _
  rw [universalQuotientMap_isCovering.monodromy_trans_apply]
  change (universalQuotientMap_isCovering.monodromy p (monodromyEndpoint q)).1 = _
  have hq : monodromyEndpoint q = fiberOfDeck (loopToDeck q) := by
    exact (fiberOfDeck_deckOfFiber (monodromyEndpoint q)).symm
  rw [hq]
  exact monodromy_from_deck p (loopToDeck q)

def loopToDeckForward (p : KleinPiOne) : AffineKleinGroup := (loopToDeck p)⁻¹

theorem loopToDeckForward_one : loopToDeckForward 1 = 1 := by
  simp [loopToDeckForward, loopToDeck_one]

theorem loopToDeckForward_mul (p q : KleinPiOne) :
    loopToDeckForward (p * q) = loopToDeckForward p * loopToDeckForward q := by
  simp only [loopToDeckForward, loopToDeck_mul_reverse, mul_inv_rev]

def loopToDeckHom : KleinPiOne →* AffineKleinGroup where
  toFun := loopToDeckForward
  map_one' := loopToDeckForward_one
  map_mul' := loopToDeckForward_mul

theorem monodromyEndpoint_surjective : Function.Surjective monodromyEndpoint := by
  intro e
  obtain ⟨Γ : Path baseLift e.1⟩ := PathConnectedSpace.joined baseLift e.1
  let f : C(Cover, KleinBrillouinQuotient) :=
    ContinuousMap.mk universalQuotientMap universalQuotientMap_continuous
  have hγ_source : universalQuotientMap baseLift = basePoint := rfl
  have hγ_target : universalQuotientMap e.1 = basePoint := e.2
  let γ₀ : Path basePoint basePoint :=
    (Γ.map f.continuous).cast hγ_source.symm hγ_target.symm
  refine ⟨Path.Homotopic.Quotient.mk γ₀, ?_⟩
  apply Subtype.ext
  change universalQuotientMap_isCovering.liftPath γ₀ baseLift _ 1 = e.1
  have hΓ_lifts : universalQuotientMap ∘ (Γ : C(I, Cover)) = γ₀ := by
    funext t
    rfl
  have hΓ_zero : Γ 0 = baseLift := Γ.source
  have heq : (Γ : C(I, Cover)) =
      universalQuotientMap_isCovering.liftPath γ₀ baseLift
        (γ₀.source.trans hγ_source.symm) := by
    apply (universalQuotientMap_isCovering.eq_liftPath_iff' _).2
    exact ⟨hΓ_lifts, hΓ_zero⟩
  rw [← heq]
  exact Γ.target

theorem monodromyEndpoint_injective : Function.Injective monodromyEndpoint := by
  intro p q hpq
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
  obtain ⟨δ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  let Γ := universalQuotientMap_isCovering.liftPath γ baseLift (by
    simp [basePoint])
  let Δ := universalQuotientMap_isCovering.liftPath δ baseLift (by
    simp [basePoint])
  have hΓ₀ : Γ 0 = baseLift :=
    universalQuotientMap_isCovering.liftPath_zero γ baseLift (by
      simp [basePoint])
  have hΔ₀ : Δ 0 = baseLift :=
    universalQuotientMap_isCovering.liftPath_zero δ baseLift (by
      simp [basePoint])
  have hΓΔ₁ : Γ 1 = Δ 1 := congrArg Subtype.val hpq
  let Γp : Path baseLift (Γ 1) := ⟨Γ, hΓ₀, rfl⟩
  let Δp : Path baseLift (Γ 1) := ⟨Δ, hΔ₀, hΓΔ₁.symm⟩
  have hhom : Γp.Homotopic Δp := SimplyConnectedSpace.paths_homotopic Γp Δp
  let f : C(Cover, KleinBrillouinQuotient) :=
    ContinuousMap.mk universalQuotientMap universalQuotientMap_continuous
  apply Path.Homotopic.Quotient.eq.2
  have hmap :
      (Γp.map f.continuous).Homotopic (Δp.map f.continuous) := hhom.map f
  have hs : basePoint = f baseLift := rfl
  have htΓ : basePoint = f (Γ 1) := by
    change basePoint = universalQuotientMap (Γ 1)
    have hl := congrFun (universalQuotientMap_isCovering.liftPath_lifts γ baseLift (by
      simp [basePoint])) 1
    change universalQuotientMap
      ((universalQuotientMap_isCovering.liftPath γ baseLift _) 1) = γ 1 at hl
    rw [show Γ = universalQuotientMap_isCovering.liftPath γ baseLift _ from rfl, hl]
    exact γ.target.symm
  let Γm : Path basePoint basePoint := (Γp.map f.continuous).cast hs htΓ
  let Δm : Path basePoint basePoint := (Δp.map f.continuous).cast hs htΓ
  have hΓm : Γm = γ := by
    ext t
    exact congrFun (universalQuotientMap_isCovering.liftPath_lifts γ baseLift (by
      simp [basePoint])) t
  have hΔm : Δm = δ := by
    ext t
    exact congrFun (universalQuotientMap_isCovering.liftPath_lifts δ baseLift (by
      simp [basePoint])) t
  rw [← hΓm, ← hΔm]
  exact hmap.pathCast hs htΓ

theorem loopToDeckHom_bijective : Function.Bijective loopToDeckHom := by
  constructor
  · intro p q hpq
    apply monodromyEndpoint_injective
    apply baseFiberEquivDeck.injective
    change loopToDeck p = loopToDeck q
    have := congrArg Inv.inv hpq
    simpa [loopToDeckHom, loopToDeckForward] using this
  · intro g
    obtain ⟨p, hp⟩ := monodromyEndpoint_surjective (fiberOfDeck g⁻¹)
    refine ⟨p, ?_⟩
    change (loopToDeck p)⁻¹ = g
    have hraw : loopToDeck p = g⁻¹ := by
      change deckOfFiber (monodromyEndpoint p) = g⁻¹
      rw [hp]
      exact deckOfFiber_fiberOfDeck g⁻¹
    rw [hraw, inv_inv]

def fundamentalGroupEquivAffine : KleinPiOne ≃* AffineKleinGroup :=
  MulEquiv.ofBijective loopToDeckHom loopToDeckHom_bijective

def fundamentalGroupEquivPresented : KleinPiOne ≃* KleinGroup :=
  fundamentalGroupEquivAffine.trans affineKleinEquivPresented

end KleinFundamentalGroup
end noncomputable section

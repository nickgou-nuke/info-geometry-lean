import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Pin55OrthogonalCover
import InfoGeometry.Clifford.Cl55WittFullOrthogonalSurjectivity

noncomputable section
namespace InfoGeometry.Canonical.AffinePin55Cover

open InfoGeometry.Clifford.Clifford55

def nativeOrthogonalAction :
    orthogonalGroup55 →* MulAut (Multiplicative V55) where
  toFun g := g.1.toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    change (x : V55) = x
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change (g.1 * h.1) x = g.1 (h.1 x)
    rfl

def realSplitPinAction :
    realSplitPin55 →* MulAut (Multiplicative V55) :=
  nativeOrthogonalAction.comp realSplitPinOrthogonalAction

abbrev AffinePin55Native :=
  Multiplicative V55 ⋊[realSplitPinAction] realSplitPin55

abbrev AffineNativeOrthogonal55 :=
  Multiplicative V55 ⋊[nativeOrthogonalAction] orthogonalGroup55

def affinePinToAffineNativeOrthogonal :
    AffinePin55Native →* AffineNativeOrthogonal55 :=
  SemidirectProduct.map (MonoidHom.id _) realSplitPinOrthogonalAction (by
    intro g
    apply MonoidHom.ext
    intro x
    change (realSplitPinAction g) x =
      nativeOrthogonalAction (realSplitPinOrthogonalAction g) x
    rfl)

theorem affinePinToAffineNativeOrthogonal_left
    (x : AffinePin55Native) :
    (affinePinToAffineNativeOrthogonal x).left = x.left := by
  -- left coordinate is preserved by `SemidirectProduct.map`.
  simpa [affinePinToAffineNativeOrthogonal]

theorem affinePinToAffineNativeOrthogonal_right
    (x : AffinePin55Native) :
    (affinePinToAffineNativeOrthogonal x).right =
      realSplitPinOrthogonalAction x.right := by
  -- right coordinate follows the codomain action on the second component.
  simpa [affinePinToAffineNativeOrthogonal]

theorem affinePinToAffineNativeOrthogonal_mem_kernel_iff
    (x : AffinePin55Native) :
    x ∈ affinePinToAffineNativeOrthogonal.ker ↔
      x.left = 1 ∧ x.right ∈ realSplitPinSignSubgroup := by
  constructor
  · intro hx
    have hzero : x.left = 1 := by
      have h := congrArg SemidirectProduct.left
        (MonoidHom.mem_ker.mp hx)
      simpa using h
    have hsign : x.right ∈ realSplitPinSignSubgroup := by
      have h := congrArg SemidirectProduct.right
        (MonoidHom.mem_ker.mp hx)
      change realSplitPinOrthogonalAction x.right = 1 at h
      have hk : x.right ∈ (realSplitPinOrthogonalAction).ker :=
        MonoidHom.mem_ker.mpr h
      simpa [realSplitPinOrthogonalAction_kernel_eq_signSubgroup] using hk
    exact ⟨hzero, hsign⟩
  · rintro ⟨hzero, hsign⟩
    rw [MonoidHom.mem_ker]
    apply SemidirectProduct.ext
    · simpa [hzero]
    · have hk : x.right ∈ (realSplitPinOrthogonalAction).ker :=
        by simpa [realSplitPinOrthogonalAction_kernel_eq_signSubgroup] using hsign
      exact MonoidHom.mem_ker.mp hk

def affinePinGlide (t : V55) (r : realSplitPin55) : AffinePin55Native :=
  SemidirectProduct.mk (Multiplicative.ofAdd t) r

theorem affinePinGlide_square
    (t : V55) (r : realSplitPin55)
    (hr : r * r = 1)
    (ht : (realSplitPinAction r) (Multiplicative.ofAdd t) =
      Multiplicative.ofAdd t) :
    affinePinGlide t r * affinePinGlide t r =
      SemidirectProduct.mk (Multiplicative.ofAdd (2 • t)) 1 := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd t *
      (realSplitPinAction r) (Multiplicative.ofAdd t) =
      Multiplicative.ofAdd (2 • t)
    rw [ht]
    change Multiplicative.ofAdd (t + t) =
      Multiplicative.ofAdd (2 • t)
    congr 1
    abel
  · exact hr

theorem affinePinToAffineNativeOrthogonal_surjective :
    Function.Surjective affinePinToAffineNativeOrthogonal := by
  intro x
  rcases realSplitPinOrthogonalAction_surjective x.right with ⟨r, hr⟩
  refine ⟨SemidirectProduct.mk x.left r, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact hr

noncomputable def affinePinQuotientEquiv :
    (AffinePin55Native ⧸ affinePinToAffineNativeOrthogonal.ker) ≃*
      AffineNativeOrthogonal55 :=
  QuotientGroup.quotientKerEquivOfSurjective
    affinePinToAffineNativeOrthogonal
    affinePinToAffineNativeOrthogonal_surjective

theorem affinePinQuotientEquiv_mk (x : AffinePin55Native) :
    affinePinQuotientEquiv (QuotientGroup.mk x) =
      affinePinToAffineNativeOrthogonal x :=
  by
  change
    QuotientGroup.kerLift affinePinToAffineNativeOrthogonal (QuotientGroup.mk x) =
      affinePinToAffineNativeOrthogonal x
  simpa [affinePinQuotientEquiv, QuotientGroup.quotientKerEquivOfSurjective] using
    (QuotientGroup.kerLift_mk (φ := affinePinToAffineNativeOrthogonal) x)

end AffinePin55Cover

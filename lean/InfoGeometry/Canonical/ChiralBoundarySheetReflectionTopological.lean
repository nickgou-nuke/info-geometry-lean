import InfoGeometry.Canonical.CantorCliffordFunctionModelTopological

/-!
# Chiral sheet reflection on the symbolic boundary

This owner is the global symbolic-boundary action induced coordinatewise by
the local `Cl(1,1)` sheet exchange.  It uses the existing binary arrow
involution and adds no algebraic or Pin construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordFunctionModel

open InfoGeometry.Canonical.ChiralLightConeTensorTower

def swapCausalArrow : CausalArrow ≃ CausalArrow where
  toFun := ChiralArrow.flip
  invFun := ChiralArrow.flip
  left_inv := ChiralArrow.flip_flip
  right_inv := ChiralArrow.flip_flip

@[simp] theorem swapCausalArrow_apply (a : CausalArrow) :
    swapCausalArrow a = ChiralArrow.flip a := rfl

@[simp] theorem swapCausalArrow_swapCausalArrow (a : CausalArrow) :
    swapCausalArrow (swapCausalArrow a) = a := by
  simp [swapCausalArrow]

def boundaryMirror (ξ : ChiralBoundary) : ChiralBoundary :=
  fun n => swapCausalArrow (ξ n)

@[simp] theorem boundaryMirror_apply (ξ : ChiralBoundary) (n : ℕ) :
    boundaryMirror ξ n = swapCausalArrow (ξ n) := rfl

@[simp] theorem boundaryMirror_boundaryMirror (ξ : ChiralBoundary) :
    boundaryMirror (boundaryMirror ξ) = ξ := by
  funext n
  simp [boundaryMirror]

theorem continuous_swapCausalArrow :
    Continuous (swapCausalArrow : CausalArrow → CausalArrow) :=
  continuous_of_discreteTopology

theorem continuous_boundaryMirror :
    Continuous boundaryMirror := by
  apply continuous_pi
  intro n
  exact continuous_swapCausalArrow.comp (continuous_apply n)

def boundaryMirrorHomeomorph : ChiralBoundary ≃ₜ ChiralBoundary where
  toEquiv :=
    { toFun := boundaryMirror
      invFun := boundaryMirror
      left_inv := boundaryMirror_boundaryMirror
      right_inv := boundaryMirror_boundaryMirror }
  continuous_toFun := continuous_boundaryMirror
  continuous_invFun := continuous_boundaryMirror

@[simp] theorem boundaryMirrorHomeomorph_apply
    (ξ : ChiralBoundary) :
    boundaryMirrorHomeomorph ξ = boundaryMirror ξ := rfl

@[simp] theorem boundaryMirrorHomeomorph_symm_apply
    (ξ : ChiralBoundary) :
    boundaryMirrorHomeomorph.symm ξ = boundaryMirror ξ := rfl

@[simp] theorem boundaryMirror_consBoundary
    (a : CausalArrow) (ξ : ChiralBoundary) :
    boundaryMirror (consBoundary a ξ) =
      consBoundary (swapCausalArrow a) (boundaryMirror ξ) := by
  funext n
  cases n <;> rfl

@[simp] theorem boundaryMirror_tailBoundary (ξ : ChiralBoundary) :
    boundaryMirror (tailBoundary ξ) =
      tailBoundary (boundaryMirror ξ) := by
  funext n
  rfl

def boundaryMirrorPullback
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    ContinuousBoundaryFunction Value where
  toFun ξ := f (boundaryMirror ξ)
  continuous_toFun := f.continuous.comp continuous_boundaryMirror

@[simp] theorem boundaryMirrorPullback_apply
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) (ξ : ChiralBoundary) :
    boundaryMirrorPullback f ξ = f (boundaryMirror ξ) := rfl

@[simp] theorem boundaryMirrorPullback_involutive
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback (boundaryMirrorPullback f) = f := by
  ext ξ
  simp [boundaryMirrorPullback, boundaryMirror_boundaryMirror]

@[simp] theorem boundaryMirrorPullback_prefix
    {Value : Type*} [TopologicalSpace Value]
    (a : CausalArrow) (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback (prefixPullbackContinuous a f) =
      prefixPullbackContinuous (swapCausalArrow a)
        (boundaryMirrorPullback f) := by
  ext ξ
  simp [boundaryMirrorPullback, boundaryMirror_consBoundary]

@[simp] theorem boundaryMirrorPullback_tail
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback (tailPullbackContinuous f) =
      tailPullbackContinuous (boundaryMirrorPullback f) := by
  ext ξ
  simp [boundaryMirrorPullback, boundaryMirror_tailBoundary]

@[simp] theorem boundaryMirrorPullback_conjugates_prefix
    {Value : Type*} [TopologicalSpace Value]
    (a : CausalArrow) (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback
      (prefixPullbackContinuous a (boundaryMirrorPullback f)) =
      prefixPullbackContinuous (swapCausalArrow a) f := by
  rw [boundaryMirrorPullback_prefix]
  simp

@[simp] theorem boundaryMirrorPullback_conjugates_tail
    {Value : Type*} [TopologicalSpace Value]
    (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback
      (tailPullbackContinuous (boundaryMirrorPullback f)) =
      tailPullbackContinuous f := by
  rw [boundaryMirrorPullback_tail]
  simp

def mirrorCausalWord {n : ℕ} (w : CausalWord n) : CausalWord n :=
  fun i => swapCausalArrow (w i)

@[simp] theorem mirrorCausalWord_mirrorCausalWord
    {n : ℕ} (w : CausalWord n) :
    mirrorCausalWord (mirrorCausalWord w) = w := by
  funext i
  simp [mirrorCausalWord]

@[simp] theorem mirrorCausalWord_append
    {n m : ℕ}
    (u : CausalWord n) (v : CausalWord m) :
    mirrorCausalWord (appendCausalWord u v) =
      appendCausalWord (mirrorCausalWord u) (mirrorCausalWord v) := by
  funext k
  by_cases hk : k.1 < n
  · simp [mirrorCausalWord, appendCausalWord, hk]
  · simp [mirrorCausalWord, appendCausalWord, hk]

@[simp] theorem boundaryMirror_prefixWordBoundary
    {n : ℕ} (w : CausalWord n) (ξ : ChiralBoundary) :
    boundaryMirror (prefixWordBoundary w ξ) =
      prefixWordBoundary (mirrorCausalWord w) (boundaryMirror ξ) := by
  funext k
  by_cases hk : k < n
  · simp [boundaryMirror, prefixWordBoundary, mirrorCausalWord, hk]
  · simp [boundaryMirror, prefixWordBoundary, hk]

@[simp] theorem boundaryMirrorPullback_prefixWord
    {Value : Type*} [TopologicalSpace Value]
    {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback
        (prefixWordPullbackContinuous w f) =
      prefixWordPullbackContinuous
        (mirrorCausalWord w) (boundaryMirrorPullback f) := by
  ext ξ
  simp [boundaryMirrorPullback, boundaryMirror_prefixWordBoundary]

@[simp] theorem boundaryMirrorPullback_conjugates_prefixWord
    {Value : Type*} [TopologicalSpace Value]
    {n : ℕ} (w : CausalWord n)
    (f : ContinuousBoundaryFunction Value) :
    boundaryMirrorPullback
      (prefixWordPullbackContinuous w (boundaryMirrorPullback f)) =
      prefixWordPullbackContinuous (mirrorCausalWord w) f := by
  rw [boundaryMirrorPullback_prefixWord]
  simp

end InfoGeometry.Canonical.CantorCliffordFunctionModel

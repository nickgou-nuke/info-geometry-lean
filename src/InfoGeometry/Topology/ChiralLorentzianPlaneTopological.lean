import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralLorentzianPlane

/-!
  Topological readout of the local split plane.  The null cone is defined by
  the real quadratic form `a^2 - b^2`; it is not identified with a physical
  spacetime without an additional representation map.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

def realChiralQuadratic (x : ℝ × ℝ) : ℝ :=
  x.1 ^ 2 - x.2 ^ 2

theorem continuous_realChiralQuadratic :
    Continuous realChiralQuadratic := by
  change Continuous (fun x : ℝ × ℝ => x.1 ^ 2 - x.2 ^ 2)
  fun_prop

def realChiralNullCone : Set (ℝ × ℝ) :=
  {x | realChiralQuadratic x = 0}

def realChiralNullRayPlus : Set (ℝ × ℝ) :=
  {x | x.2 = x.1}

def realChiralNullRayMinus : Set (ℝ × ℝ) :=
  {x | x.2 = -x.1}

theorem isClosed_realChiralNullCone :
    IsClosed realChiralNullCone := by
  change IsClosed (realChiralQuadratic ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage continuous_realChiralQuadratic

theorem isClosed_realChiralNullRayPlus :
    IsClosed realChiralNullRayPlus := by
  rw [show realChiralNullRayPlus =
      {x : ℝ × ℝ | x.2 = x.1} by rfl]
  exact isClosed_eq continuous_snd continuous_fst

theorem isClosed_realChiralNullRayMinus :
    IsClosed realChiralNullRayMinus := by
  rw [show realChiralNullRayMinus =
      {x : ℝ × ℝ | x.2 = -x.1} by rfl]
  exact isClosed_eq continuous_snd (continuous_neg.comp continuous_fst)

theorem realChiralNullCone_eq_nullRays :
    realChiralNullCone =
      realChiralNullRayPlus ∪ realChiralNullRayMinus := by
  ext x
  constructor
  · intro hx
    change realChiralQuadratic x = 0 at hx
    change x.1 ^ 2 - x.2 ^ 2 = 0 at hx
    have hfactor : (x.1 - x.2) * (x.1 + x.2) = 0 := by
      calc
        (x.1 - x.2) * (x.1 + x.2) = x.1 ^ 2 - x.2 ^ 2 := by ring
        _ = 0 := hx
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      dsimp [realChiralNullRayPlus]
      linarith
    · right
      dsimp [realChiralNullRayMinus]
      linarith
  · intro hx
    rcases hx with hx | hx
    · dsimp [realChiralNullRayPlus] at hx
      dsimp [realChiralNullCone, realChiralQuadratic]
      rw [hx]
      ring
    · dsimp [realChiralNullRayMinus] at hx
      dsimp [realChiralNullCone, realChiralQuadratic]
      rw [hx]
      ring

def realChiralNullRayPlusParam (t : ℝ) : ℝ × ℝ :=
  (t, t)

def realChiralNullRayMinusParam (t : ℝ) : ℝ × ℝ :=
  (t, -t)

theorem continuous_realChiralNullRayPlusParam :
    Continuous realChiralNullRayPlusParam := by
  change Continuous (fun t : ℝ => (t, t))
  fun_prop

theorem continuous_realChiralNullRayMinusParam :
    Continuous realChiralNullRayMinusParam := by
  change Continuous (fun t : ℝ => (t, -t))
  fun_prop

theorem injective_realChiralNullRayPlusParam :
    Function.Injective realChiralNullRayPlusParam := by
  intro a b h
  exact congrArg Prod.fst h

theorem injective_realChiralNullRayMinusParam :
    Function.Injective realChiralNullRayMinusParam := by
  intro a b h
  exact congrArg Prod.fst h

theorem realChiralNullRayPlusParam_leftInverse :
    Function.LeftInverse Prod.fst realChiralNullRayPlusParam := by
  intro t
  rfl

theorem realChiralNullRayMinusParam_leftInverse :
    Function.LeftInverse Prod.fst realChiralNullRayMinusParam := by
  intro t
  rfl

theorem isEmbedding_realChiralNullRayPlusParam :
    Topology.IsEmbedding realChiralNullRayPlusParam :=
  realChiralNullRayPlusParam_leftInverse.isEmbedding
    continuous_fst continuous_realChiralNullRayPlusParam

theorem isEmbedding_realChiralNullRayMinusParam :
    Topology.IsEmbedding realChiralNullRayMinusParam :=
  realChiralNullRayMinusParam_leftInverse.isEmbedding
    continuous_fst continuous_realChiralNullRayMinusParam

theorem range_realChiralNullRayPlusParam :
    Set.range realChiralNullRayPlusParam = realChiralNullRayPlus := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hx
    change x.2 = x.1 at hx
    exact ⟨x.1, by
      apply Prod.ext
      · rfl
      · change x.1 = x.2
        exact hx.symm⟩

theorem range_realChiralNullRayMinusParam :
    Set.range realChiralNullRayMinusParam = realChiralNullRayMinus := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hx
    change x.2 = -x.1 at hx
    exact ⟨x.1, by
      apply Prod.ext
      · rfl
      · change -x.1 = x.2
        exact hx.symm⟩

theorem isClosedMap_realChiralNullRayPlusParam :
    IsClosedMap realChiralNullRayPlusParam := by
  intro s hs
  have himage :
      realChiralNullRayPlusParam '' s =
        realChiralNullRayPlus ∩ Prod.fst ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by rfl, ht⟩
    · rintro ⟨hx, hsx⟩
      change x.2 = x.1 at hx
      refine ⟨x.1, hsx, ?_⟩
      apply Prod.ext
      · rfl
      · change x.1 = x.2
        exact hx.symm
  rw [himage]
  exact isClosed_realChiralNullRayPlus.inter
    (hs.preimage continuous_fst)

theorem isClosedMap_realChiralNullRayMinusParam :
    IsClosedMap realChiralNullRayMinusParam := by
  intro s hs
  have himage :
      realChiralNullRayMinusParam '' s =
        realChiralNullRayMinus ∩ Prod.fst ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by rfl, ht⟩
    · rintro ⟨hx, hsx⟩
      change x.2 = -x.1 at hx
      refine ⟨x.1, hsx, ?_⟩
      apply Prod.ext
      · rfl
      · change -x.1 = x.2
        exact hx.symm
  rw [himage]
  exact isClosed_realChiralNullRayMinus.inter
    (hs.preimage continuous_fst)

theorem isClosedEmbedding_realChiralNullRayPlusParam :
    Topology.IsClosedEmbedding realChiralNullRayPlusParam :=
  Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap
    isEmbedding_realChiralNullRayPlusParam
    isClosedMap_realChiralNullRayPlusParam

theorem isClosedEmbedding_realChiralNullRayMinusParam :
    Topology.IsClosedEmbedding realChiralNullRayMinusParam :=
  Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap
    isEmbedding_realChiralNullRayMinusParam
    isClosedMap_realChiralNullRayMinusParam

end InfoGeometry.Topology

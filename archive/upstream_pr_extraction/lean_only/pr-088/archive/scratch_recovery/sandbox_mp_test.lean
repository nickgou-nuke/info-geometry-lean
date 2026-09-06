import sandbox_mp_authoritative

open InfoGeometry.Singular.MoorePenrose.MoorePenroseClosedRange
open ContinuousLinearMap

/-! ## Analytic Moore-Penrose closed-range existence basic tests -/

-- For the identity, the Moore-Penrose inverse is itself.
example {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (h : IsClosed (range (id 𝕜 E) : Set E)) :
    ∃ B : E →L[𝕜] E,
      (id 𝕜 E) ∘L B = (Submodule.range (id 𝕜 E)).starProjection ∧
      B ∘L (id 𝕜 E) = (Submodule.ker (id 𝕜 E))ᗮ.starProjection ∧
      ((id 𝕜 E) ∘L B) ∘L (id 𝕜 E) = id 𝕜 E ∧
      (B ∘L (id 𝕜 E)) ∘L B = B :=
  exists_inverse (id 𝕜 E)
    h

-- The existence theorem for any closed-range operator
example {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) (hA : IsClosed (A.range : Set F)) :
    ∃ B : F →L[𝕜] E,
      A ∘L B = A.range.starProjection ∧
      B ∘L A = A.kerᗮ.starProjection ∧
      (A ∘L B) ∘L A = A ∧
      (B ∘L A) ∘L B = B := exists_inverse A hA

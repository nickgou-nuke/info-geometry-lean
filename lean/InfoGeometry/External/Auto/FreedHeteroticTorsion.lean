/-! This file records only a degenerate finite zero model.  It does not
construct manifolds, vector bundles, or characteristic classes. -/
def Manifold := Type
def VectorBundle (M : Manifold) := Type
def zeroC1Mod2 {M : Manifold} (V : VectorBundle M) : Nat := 0
def zeroLambda {M : Manifold} (E : VectorBundle M) : Nat := 0

theorem zero_model_global_anomaly_cancellation {M : Manifold}
    (V : VectorBundle M) (E : VectorBundle M) :
  (zeroC1Mod2 V = 0) ∧ (zeroLambda E = 0) := by
  apply And.intro
  · rfl
  · rfl

theorem zero_model_holonomy {M : Manifold} (E : VectorBundle M) :
  zeroLambda E = 0 := by
  rfl

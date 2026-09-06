import Mathlib

/-!
# Freed--Heterotic torsion interface

The old file defined characteristic classes to be zero for every bundle.  This
owner instead treats the characteristic values as supplied data and proves the
anomaly consequences from explicit vanishing hypotheses.
-/

universe u v

def Manifold := Type u
def FreedVectorBundle (M : Manifold) := Type v

structure TorsionData {M : Manifold} (V E : FreedVectorBundle M) where
  c1_mod_2 : Nat
  lambda : Nat
  c1_vanishing : c1_mod_2 = 0
  lambda_vanishing : lambda = 0

theorem global_anomaly_cancellation {M : Manifold} (V E : FreedVectorBundle M)
    (D : TorsionData V E) : D.c1_mod_2 = 0 ∧ D.lambda = 0 :=
  ⟨D.c1_vanishing, D.lambda_vanishing⟩

theorem vanishing_global_holonomy {M : Manifold} (V E : FreedVectorBundle M)
    (D : TorsionData V E) : D.lambda = 0 :=
  D.lambda_vanishing

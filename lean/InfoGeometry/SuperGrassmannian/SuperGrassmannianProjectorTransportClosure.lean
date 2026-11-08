/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge

namespace InfoGeometry.SuperGrassmannian

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A linear map intertwining two endomorphisms transports their half-sum maps. -/
theorem paraProjectorPlus_intertwines
    (KV : V →ₗ[ℝ] V) (KW : W →ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hK : f.comp KV = KW.comp f) :
    f.comp (paraProjectorPlus KV) = (paraProjectorPlus KW).comp f := by
  ext v
  change f ((1 / 2 : ℝ) • (v + KV v)) =
    (1 / 2 : ℝ) • (f v + KW (f v))
  rw [map_smul, map_add, ← LinearMap.comp_apply f KV, ← LinearMap.comp_apply KW f]
  rw [← congrArg (fun g : V →ₗ[ℝ] W => g v) hK]

/-- A linear map intertwining two endomorphisms transports their half-difference maps. -/
theorem paraProjectorMinus_intertwines
    (KV : V →ₗ[ℝ] V) (KW : W →ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hK : f.comp KV = KW.comp f) :
    f.comp (paraProjectorMinus KV) = (paraProjectorMinus KW).comp f := by
  ext v
  change f ((1 / 2 : ℝ) • (v - KV v)) =
    (1 / 2 : ℝ) • (f v - KW (f v))
  rw [map_smul, map_sub, ← LinearMap.comp_apply f KV, ← LinearMap.comp_apply KW f]
  rw [← congrArg (fun g : V →ₗ[ℝ] W => g v) hK]

end InfoGeometry.SuperGrassmannian

namespace InfoGeometry.SuperGrassmannian

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A linear map anti-intertwining two endomorphisms swaps their half-sum and
half-difference maps. -/
theorem paraProjectorPlus_antiIntertwines_to_minus
    (KV : V →ₗ[ℝ] V) (KW : W →ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hK : f.comp KV = -(KW.comp f)) :
    f.comp (paraProjectorPlus KV) = (paraProjectorMinus KW).comp f := by
  ext v
  change f ((1 / 2 : ℝ) • (v + KV v)) =
    (1 / 2 : ℝ) • (f v - KW (f v))
  rw [map_smul, map_add]
  have hkv := LinearMap.congr_fun hK v
  change f (KV v) = -KW (f v) at hkv
  rw [hkv]
  simp; module

/-- A linear map anti-intertwining two endomorphisms swaps their half-difference and
half-sum maps. -/
theorem paraProjectorMinus_antiIntertwines_to_plus
    (KV : V →ₗ[ℝ] V) (KW : W →ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hK : f.comp KV = -(KW.comp f)) :
    f.comp (paraProjectorMinus KV) = (paraProjectorPlus KW).comp f := by
  ext v
  change f ((1 / 2 : ℝ) • (v - KV v)) =
    (1 / 2 : ℝ) • (f v + KW (f v))
  rw [map_smul, map_sub]
  have hkv := LinearMap.congr_fun hK v
  change f (KV v) = -KW (f v) at hkv
  rw [hkv]
  simp

end InfoGeometry.SuperGrassmannian

import Mathlib.Tactic
import InfoGeometry.Algebra.RealSplitAlbert

set_option maxHeartbeats 2000000

/-!
# Concrete real Albert generation readout

This file exposes the diagonal matrix units and the six coordinate projections
of the real split-Albert carrier.  It deliberately separates these finite
coordinate facts from the later derivation-algebra and particle-interpretation
claims.
-/

namespace InfoGeometry.Algebra.RealAlbertMatrix

def e₁ : RealAlbertMatrix :=
  ⟨1, 0, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def e₂ : RealAlbertMatrix :=
  ⟨0, 1, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def e₃ : RealAlbertMatrix :=
  ⟨0, 0, 1, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def one : RealAlbertMatrix :=
  ⟨1, 1, 1, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

theorem e₁_idempotent : mul e₁ e₁ = e₁ := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]

theorem e₂_idempotent : mul e₂ e₂ = e₂ := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]

theorem e₃_idempotent : mul e₃ e₃ = e₃ := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]

theorem e₁_mul_e₂ : mul e₁ e₂ = zero := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero,
    RealAlbertMatrix.zero]

theorem e₁_mul_e₃ : mul e₁ e₃ = zero := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero,
    RealAlbertMatrix.zero]

theorem e₂_mul_e₃ : mul e₂ e₃ = zero := by
  ext <;> norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero,
    RealAlbertMatrix.zero]

def peirceProj₁₁ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨X.α₁, 0, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def peirceProj₂₂ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨0, X.α₂, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def peirceProj₃₃ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨0, 0, X.α₃, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def peirceProj₂₃ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨0, 0, 0, X.z₁, RealSplitOct.zero, RealSplitOct.zero⟩

def peirceProj₃₁ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨0, 0, 0, RealSplitOct.zero, X.z₂, RealSplitOct.zero⟩

def peirceProj₁₂ (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨0, 0, 0, RealSplitOct.zero, RealSplitOct.zero, X.z₃⟩

@[simp] theorem peirceProj₂₃_z₁ (X : RealAlbertMatrix) :
    (peirceProj₂₃ X).z₁ = X.z₁ := rfl

@[simp] theorem peirceProj₃₁_z₂ (X : RealAlbertMatrix) :
    (peirceProj₃₁ X).z₂ = X.z₂ := rfl

@[simp] theorem peirceProj₁₂_z₃ (X : RealAlbertMatrix) :
    (peirceProj₁₂ X).z₃ = X.z₃ := rfl

end InfoGeometry.Algebra.RealAlbertMatrix

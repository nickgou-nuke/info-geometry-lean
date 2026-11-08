import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.WeakValueSpatialReconstruction

/-!
# Guarded weak readouts in the existing cylinder colimit

The nonlinear readout commutes with the owner's successor embeddings and
cylinder maps. Embedding alone does not remove a zero overlap. No analytic
completion or identification of Cantor boundary with physical spacetime is
asserted.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValueCylinderTransport

open UHFInductiveColimitBoundary

def guardedDivision (n d : ℂ) : Option ℂ :=
  if d = 0 then none else some (n / d)

def stageReadout (k : ℕ) (n d : DiagAlg k) : BitWord k → Option ℂ :=
  fun w => guardedDivision (n w) (d w)

def boundaryReadout (k : ℕ) (n d : DiagAlg k) : CantorBoundary → Option ℂ :=
  fun b => guardedDivision (cylinder k n b) (cylinder k d b)

theorem stageReadout_embed (k : ℕ) (n d : DiagAlg k) (w : BitWord (k + 1)) :
    stageReadout (k + 1) (diagEmbedSucc k n) (diagEmbedSucc k d) w =
      stageReadout k n d (prefixSucc k w) := rfl

/-- Uses the owned cylinder compatibility laws for both homogeneous slots. -/
theorem boundaryReadout_embed (k : ℕ) (n d : DiagAlg k) :
    boundaryReadout (k + 1) (diagEmbedSucc k n) (diagEmbedSucc k d) =
      boundaryReadout k n d := by
  unfold boundaryReadout
  rw [cylinder_compatible_succ, cylinder_compatible_succ]

theorem regular_embed_iff (k : ℕ) (d : DiagAlg k) :
    (∀ w, diagEmbedSucc k d w ≠ 0) ↔ ∀ w, d w ≠ 0 := by
  constructor
  · intro h w
    simpa [diagEmbedSucc, prefixSucc_extendSucc] using h (extendSucc k w false)
  · intro h w
    exact h (prefixSucc k w)

/-- Both successor fibers preserve an undefined zero-overlap readout. -/
theorem seam_survives_embedding (k : ℕ) (n d : DiagAlg k)
    (w : BitWord k) (hd : d w = 0) (bit : Bool) :
    stageReadout (k + 1) (diagEmbedSucc k n) (diagEmbedSucc k d)
      (extendSucc k w bit) = none := by
  simp [stageReadout, guardedDivision, diagEmbedSucc, prefixSucc_extendSucc, hd]

/-- The total numerator/denominator function belongs to the algebraic cylinder
carrier; its value at zero is not a physical readout. -/
theorem quotient_cylinder (k : ℕ) (n d : DiagAlg k) :
    (fun b => cylinder k n b / cylinder k d b) ∈ CylinderColimit := by
  exact cylinder_mem_colimit k (fun w => n w / d w)

end InfoGeometry.Canonical.WeakValueCylinderTransport

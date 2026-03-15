import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Volume.Pfaffian
import InfoGeometry.Volume.ConnesCocycle

/-!
# Majorana Kitaev Chains and Tiling

Finite chain layer where macroscopic volume is the product of local Pfaffians.
-/

namespace InfoGeometry.Quantum.KitaevChain

open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Volume.Pfaffian

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A Kitaev cell: a real Majorana core with a skew channel operator. -/
structure KitaevCell where
  core : RealMajoranaCore
  [instV : NormedAddCommGroup core.V]
  [instInner : InnerProductSpace ℝ core.V]
  [instComp : CompleteSpace core.V]
  [instKrein : KreinSpace core.V]
  [instFinite : FiniteDimensional ℝ core.V]
  pairing : core.V →ₗ[ℝ] core.V
  is_skew : IsSkewSymmetric pairing

/-- Kitaev 1-cocycle transition map between adjacent cells (zero model here). -/
def KitaevCocycle (C1 C2 : KitaevCell) : ℝ → C1.core.V →ₗ[ℝ] C2.core.V :=
  fun _ => 0

/-- Pfaffian attached to a Kitaev cell. -/
noncomputable def KitaevCell.pfaffian (c : KitaevCell) : ℝ := by
  let _ : NormedAddCommGroup c.core.V := c.instV
  let _ : InnerProductSpace ℝ c.core.V := c.instInner
  let _ : CompleteSpace c.core.V := c.instComp
  let _ : KreinSpace c.core.V := c.instKrein
  let _ : FiniteDimensional ℝ c.core.V := c.instFinite
  exact InfoGeometry.Volume.Pfaffian.pfaffian (H := c.core.V) c.pairing

/--
Kitaev tiling identity: the macroscopic volume can be chosen as the product
of microscopic cell Pfaffians.
-/
theorem kitaev_tiling_identity (chain : List KitaevCell) :
    ∃ (Vol : ℝ), Vol = (chain.map (fun c : KitaevCell => c.pfaffian)).prod :=
  ⟨(chain.map (fun c : KitaevCell => c.pfaffian)).prod, rfl⟩

end InfoGeometry.Quantum.KitaevChain

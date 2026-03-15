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

/--
One-parameter cocycle on a single Kitaev cell.
The cocycle law is expressed by composition in `End(core.V)`.
-/
structure KitaevCocycle (C : KitaevCell) where
  U : ℝ → C.core.V →ₗ[ℝ] C.core.V
  cocycle : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)

/-- Trivial identity cocycle (useful neutral element in the finite scaffold). -/
def trivialKitaevCocycle (C : KitaevCell) : KitaevCocycle C where
  U := fun _ => LinearMap.id
  cocycle := by
    intro s t
    simp

/-- Pfaffian attached to a Kitaev cell. -/
noncomputable def KitaevCell.pfaffian (c : KitaevCell) : ℝ := by
  let _ : NormedAddCommGroup c.core.V := c.instV
  let _ : InnerProductSpace ℝ c.core.V := c.instInner
  let _ : CompleteSpace c.core.V := c.instComp
  let _ : KreinSpace c.core.V := c.instKrein
  let _ : FiniteDimensional ℝ c.core.V := c.instFinite
  exact InfoGeometry.Volume.Pfaffian.pfaffian (H := c.core.V) c.pairing

/-- Macroscopic volume proxy: product of microscopic cell Pfaffians. -/
noncomputable def macroscopicVolume (chain : List KitaevCell) : ℝ :=
  (chain.map (fun c : KitaevCell => c.pfaffian)).prod

/-- Definitional form of the tiling identity. -/
theorem macroscopicVolume_eq_prod_pfaffians (chain : List KitaevCell) :
    macroscopicVolume chain = (chain.map (fun c : KitaevCell => c.pfaffian)).prod := rfl

/--
Kitaev tiling identity: the macroscopic volume is the product
of microscopic cell Pfaffians.
-/
theorem kitaev_tiling_identity (chain : List KitaevCell) :
    ∃ (Vol : ℝ), Vol = (chain.map (fun (c : KitaevCell) => c.pfaffian)).prod :=
  ⟨macroscopicVolume chain, rfl⟩

/--
If each microscopic cell has normalized Pfaffian `1`, then the macroscopic
volume proxy is pinned to `1`.
-/
theorem macroscopicVolume_eq_one_of_pfaffian_one
    (chain : List KitaevCell)
    (hPf : ∀ c : KitaevCell, c ∈ chain → c.pfaffian = 1) :
    macroscopicVolume chain = 1 := by
  induction chain with
  | nil =>
      simp [macroscopicVolume]
  | cons c cs ih =>
      have hc : c.pfaffian = 1 := hPf c (by simp)
      have hcs : macroscopicVolume cs = 1 := by
        apply ih
        intro c' hc'
        exact hPf c' (by simp [hc'])
      have hcs' : (cs.map (fun c : KitaevCell => c.pfaffian)).prod = 1 := by
        simpa [macroscopicVolume] using hcs
      simp [macroscopicVolume, hc, hcs']

end InfoGeometry.Quantum.KitaevChain

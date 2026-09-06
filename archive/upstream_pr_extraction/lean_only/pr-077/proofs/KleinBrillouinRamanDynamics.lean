import proofs.WallpaperHolographicSelectionRules
import proofs.ChiralIsospinEOMSU2
import proofs.ModularParabolicTimeBridge
import proofs.ProjectiveWallpaperGaugePSA

/-!
# Klein Brillouin Raman dynamics

Thin dynamic-spectroscopy capstone over the already compiled crystallographic
selection layer.  It records the intended passage

```text
static wallpaper selection rules → dynamic Raman/Bloch/Klein vibration sectors
```

Kernel-proved content remains finite:

* `pg` odd fixed-line extinction;
* reflection fixed loci for the Klein/critical axis bookkeeping;
* nilpotent Itakura--Saito remainder vanishes;
* parabolic modular clocks add;
* `M₂(ℂ)` chiral tile/projector trace facts;
* finite S₃/GNS color-selection scaffold;
* `pg` and `p6m` remain distinct layers.

-/

noncomputable section

namespace KleinBrillouinRamanDynamics



/-- Finite Bloch-sector labels for the dynamics layer. -/
inductive BlochSector where
  | gammaSinglet
  | kPointStandard
  | glideExtinguished
  deriving DecidableEq, Repr

/-- Which finite sectors are visible to the selection-rule spectrometer. -/
def RamanVisible : BlochSector → Bool
  | .gammaSinglet => true
  | .kPointStandard => false
  | .glideExtinguished => false

@[simp] theorem gamma_singlet_raman_visible : RamanVisible BlochSector.gammaSinglet = true := rfl
@[simp] theorem kpoint_standard_raman_inactive : RamanVisible BlochSector.kPointStandard = false := rfl
@[simp] theorem glide_extinguished_raman_inactive : RamanVisible BlochSector.glideExtinguished = false := rfl

/-- A named finite extinction statement: odd `pg` fixed-line modes vanish. -/
theorem pg_glide_extinction_selection_rule {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = FixedLineRiemannKlein.pgPhase k * c) : c = 0 :=
  FixedLineRiemannKlein.pg_fixed_line_extinction hodd hrel

/-- The dynamic capstone: the finite selection-rule spine supports a typed
Raman/Bloch/Klein dynamics interpretation, without proving the analytic mass
spectrum or physical QFT realization. -/
theorem klein_brillouin_raman_dynamics_synthesis
    (P Q : ModularParabolicTimeBridge.ParabolicTimeClock) :
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = FixedLineRiemannKlein.pgPhase k * c → c = 0) ∧
    (∀ k : ℤ × ℤ, FixedLineRiemannKlein.glideReflect k = k ↔ k.2 = 0) ∧
    (∀ s : FixedLineRiemannKlein.ScalePoint,
      FixedLineRiemannKlein.scaleReflect s = s ↔ FixedLineRiemannKlein.criticalLine s) ∧
    (∀ K : FixedLineRiemannKlein.M2C, FixedLineRiemannKlein.nilItakuraSaito K = 0) ∧
    (P.comp Q).τ = P.τ + Q.τ ∧
    ProjectiveWallpaperGaugePSA.WallpaperGroup.pg ≠
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m ∧
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.pg = 1 ∧
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 4 ∧
    ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 ∧
    ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 ∧
    ChiralConeAlgebraFinality.NPlus + ChiralConeAlgebraFinality.NMinus =
      (1 : ChiralConeAlgebraFinality.M2C) ∧
    ChiralConeAlgebraFinality.τ ChiralConeAlgebraFinality.NPlus = 1 / 2 ∧
    ChiralConeAlgebraFinality.τ ChiralConeAlgebraFinality.NMinus = 1 / 2 ∧
    RamanVisible BlochSector.gammaSinglet = true ∧
    RamanVisible BlochSector.kPointStandard = false ∧
    RamanVisible BlochSector.glideExtinguished = false ∧
    ((2 : ℂ)*1 + (0 : ℂ)*1 + (1 : ℂ)*2 = (4 : ℂ) ∧
      (3 : ℂ) ≠ (4 : ℂ) ∧
      WeylSU3ColorSymmetry.swap12 ∘ WeylSU3ColorSymmetry.swap23 ∘
        WeylSU3ColorSymmetry.swap12 =
        WeylSU3ColorSymmetry.swap23 ∘ WeylSU3ColorSymmetry.swap12 ∘
          WeylSU3ColorSymmetry.swap23 ∧
      (1 : ℂ)^2 + (1 : ℂ)^2 + (2 : ℂ)^2 = (6 : ℂ)) := by
  rcases ChiralConeAlgebraFinality.thermal_self_dual_occupations with
    ⟨hTauPlus, hTauMinus, _hTauUnit⟩
  constructor
  · exact FixedLineRiemannKlein.pg_fixed_line_extinction
  constructor
  · exact FixedLineRiemannKlein.glide_fixed_iff
  constructor
  · exact FixedLineRiemannKlein.scale_fixed_iff_critical
  constructor
  · exact FixedLineRiemannKlein.nilItakuraSaito_zero
  constructor
  · exact ModularTimeDeRhamBridge.parabolic_shear_clock_add P Q
  constructor
  · decide
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact ChiralConeAlgebraFinality.sPlus_sq_zero
  constructor
  · exact ChiralConeAlgebraFinality.sMinus_sq_zero
  constructor
  · exact ChiralConeAlgebraFinality.chiral_projector_completeness
  constructor
  · exact hTauPlus
  constructor
  · exact hTauMinus
  constructor
  · exact gamma_singlet_raman_visible
  constructor
  · exact kpoint_standard_raman_inactive
  constructor
  · exact glide_extinguished_raman_inactive
  · exact ColorConfinementGNS.color_confinement_gns_synthesis

end KleinBrillouinRamanDynamics

end noncomputable section

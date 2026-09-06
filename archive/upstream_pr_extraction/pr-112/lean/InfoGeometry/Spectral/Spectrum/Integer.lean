import Mathlib

/-!
# Integer-indexed prespectra

The original Spectral development uses a successor-indexed, integer-graded
prespectrum.  This file provides that carrier natively.  Structure maps are
equivalences for `IntegerSpectrum`; no topological loop-space realization is
silently assumed.
-/

namespace InfoGeometry.Spectral.Spectrum.Integer

structure Prespectrum where
  space : ℤ → Type*
  step : ∀ n, space n → space (n + 1)

structure Spectrum extends Prespectrum where
  stepEquiv : ∀ n, space n ≃ space (n + 1)
  stepEquiv_apply : ∀ n x, stepEquiv n x = step n x

structure Map (E F : Prespectrum) where
  toFun : ∀ n, E.space n → F.space n
  comm : ∀ n x, toFun (n + 1) (E.step n x) = F.step n (toFun n x)

instance {E F : Prespectrum} : CoeFun (Map E F)
    (fun _ => ∀ n, E.space n → F.space n) where
  coe f := f.toFun

@[simp] theorem Map.comm_apply {E F : Prespectrum} (f : Map E F) (n : ℤ)
    (x : E.space n) :
    f (n + 1) (E.step n x) = F.step n (f n x) :=
  f.comm n x

def Map.id (E : Prespectrum) : Map E E where
  toFun := fun _ x => x
  comm := by intro n x; rfl

@[simp] theorem Map.id_apply (E : Prespectrum) (n : ℤ) (x : E.space n) :
    Map.id E n x = x :=
  rfl

def Map.comp {E F G : Prespectrum} (g : Map F G) (f : Map E F) : Map E G where
  toFun := fun n x => g n (f n x)
  comm := by
    intro n x
    rw [f.comm, g.comm]

@[simp] theorem Map.comp_apply {E F G : Prespectrum} (g : Map F G) (f : Map E F)
    (n : ℤ) (x : E.space n) :
    Map.comp g f n x = g n (f n x) :=
  rfl

theorem Map.ext {E F : Prespectrum} {f g : Map E F}
    (h : ∀ n x, f n x = g n x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfun : f = g := by
        funext n x
        exact h n x
      cases hfun
      rfl

def Spectrum.of (E : Prespectrum) (e : ∀ n, E.space n ≃ E.space (n + 1))
    (h : ∀ n x, e n x = E.step n x) : Spectrum where
  toPrespectrum := E
  stepEquiv := e
  stepEquiv_apply := h

@[simp] theorem Spectrum.stepEquiv_readback (E : Spectrum) (n : ℤ) (x : E.space n) :
    E.stepEquiv n x = E.step n x :=
  E.stepEquiv_apply n x

/-! Maps between genuine spectra.  The structure maps are already
equivalences in this carrier, so a spectrum map is precisely a prespectrum
map between the underlying carriers. -/

structure SpectrumMap (E F : Spectrum) where
  toMap : Map E.toPrespectrum F.toPrespectrum

instance {E F : Spectrum} : CoeFun (SpectrumMap E F)
    (fun _ => ∀ n, E.space n → F.space n) where
  coe f := f.toMap

@[simp] theorem SpectrumMap.comm_apply {E F : Spectrum} (f : SpectrumMap E F)
    (n : ℤ) (x : E.space n) :
    f (n + 1) (E.step n x) = F.step n (f n x) :=
  f.toMap.comm n x

def SpectrumMap.id (E : Spectrum) : SpectrumMap E E where
  toMap := Map.id E.toPrespectrum

@[simp] theorem SpectrumMap.id_apply (E : Spectrum) (n : ℤ) (x : E.space n) :
    SpectrumMap.id E n x = x :=
  rfl

def SpectrumMap.comp {E F G : Spectrum} (g : SpectrumMap F G) (f : SpectrumMap E F) :
    SpectrumMap E G where
  toMap := Map.comp g.toMap f.toMap

@[simp] theorem SpectrumMap.comp_apply {E F G : Spectrum} (g : SpectrumMap F G)
    (f : SpectrumMap E F) (n : ℤ) (x : E.space n) :
    SpectrumMap.comp g f n x = g n (f n x) :=
  rfl

theorem SpectrumMap.ext {E F : Spectrum} {f g : SpectrumMap E F}
    (h : ∀ n x, f n x = g n x) : f = g := by
  apply congrArg (fun m : Map E.toPrespectrum F.toPrespectrum =>
    SpectrumMap.mk m) (Map.ext h)

end InfoGeometry.Spectral.Spectrum.Integer

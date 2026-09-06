import InfoGeometry.Spectral.Spectrum.Basic

/-!
# Maps and spectrum contracts for the finite spectral port

This is the algebraic portion of the old `spectrum/basic` interface.  The
stable homotopy realization remains outside this module.
-/

namespace InfoGeometry.Spectral.Spectrum.GPreSpectrum

open InfoGeometry.Spectral.Spectrum.Basic

/-- A map of prespectrum-shaped sequences, with its structure-square law. -/
structure Map (E F : Prespectrum) where
  toFun : ∀ n, E.space n → F.space n
  comm : ∀ n x, toFun (n + 1) (E.step n x) = F.step n (toFun n x)

instance {E F : Prespectrum} : CoeFun (Map E F) (fun _ => ∀ n, E.space n → F.space n) where
  coe f := f.toFun

@[simp]
theorem Map.comm_apply {E F : Prespectrum} (f : Map E F) (n : ℕ) (x : E.space n) :
    f (n + 1) (E.step n x) = F.step n (f n x) :=
  f.comm n x

/-- Identity map of a prespectrum. -/
def Map.id (E : Prespectrum) : Map E E where
  toFun := fun _ x => x
  comm := by intro n x; rfl

@[simp]
theorem Map.id_apply (E : Prespectrum) (n : ℕ) (x : E.space n) :
    Map.id E n x = x :=
  rfl

/-- Composition of maps of prespectra. -/
def Map.comp {E F G : Prespectrum} (g : Map F G) (f : Map E F) : Map E G where
  toFun := fun n x => g n (f n x)
  comm := by
    intro n x
    rw [f.comm, g.comm]

@[simp]
theorem Map.comp_apply {E F G : Prespectrum} (g : Map F G) (f : Map E F)
    (n : ℕ) (x : E.space n) :
    Map.comp g f n x = g n (f n x) :=
  rfl

theorem Map.ext {E F : Prespectrum} {f g : Map E F}
    (h : ∀ n x, f n x = g n x) : f = g := by
  cases f with
  | mk f hf =>
      cases g with
      | mk g hg =>
          congr
          funext n x
          exact h n x

/-- A prespectrum whose structure maps are equivalences. -/
structure IsSpectrum (E : Prespectrum) where
  stepEquiv : ∀ n, E.space n ≃ E.space (n + 1)
  stepEquiv_apply : ∀ n x, stepEquiv n x = E.step n x

/-- The explicit algebraic spectrum object. -/
structure Spectrum where
  prespectrum : Prespectrum
  isSpectrum : IsSpectrum prespectrum

/-- A map of spectrum objects; the spectrum condition is inherited from the
underlying prespectrum map rather than reproved as an additional axiom. -/
structure SpectrumMap (E F : Spectrum) where
  toMap : Map E.prespectrum F.prespectrum

instance {E F : Spectrum} : CoeFun (SpectrumMap E F)
    (fun _ => ∀ n, E.prespectrum.space n → F.prespectrum.space n) where
  coe f := f.toMap

namespace SpectrumMap

/-- Identity map of spectrum objects. -/
def id (E : Spectrum) : SpectrumMap E E where
  toMap := Map.id E.prespectrum

@[simp]
theorem id_apply (E : Spectrum) (n : ℕ) (x : E.prespectrum.space n) :
    id E n x = x :=
  rfl

/-- Composition of spectrum maps. -/
def comp {E F G : Spectrum} (g : SpectrumMap F G) (f : SpectrumMap E F) :
    SpectrumMap E G where
  toMap := Map.comp g.toMap f.toMap

@[simp]
theorem comp_apply {E F G : Spectrum} (g : SpectrumMap F G)
    (f : SpectrumMap E F) (n : ℕ) (x : E.prespectrum.space n) :
    comp g f n x = g n (f n x) :=
  rfl

theorem ext {E F : Spectrum} {f g : SpectrumMap E F}
    (h : ∀ n x, f n x = g n x) : f = g := by
  cases f with
  | mk f =>
      cases g with
      | mk g =>
          congr
          apply Map.ext
          exact h

@[simp] theorem comp_id {E F : Spectrum} (f : SpectrumMap E F) :
    comp (id F) f = f := by
  cases f with
  | mk f =>
      congr

@[simp] theorem id_comp {E F : Spectrum} (f : SpectrumMap E F) :
    comp f (id E) = f := by
  cases f with
  | mk f =>
      congr

end SpectrumMap

@[simp]
theorem stepEquiv_apply (E : Spectrum) (n : ℕ) (x : E.prespectrum.space n) :
  E.isSpectrum.stepEquiv n x = E.prespectrum.step n x :=
  E.isSpectrum.stepEquiv_apply n x

end InfoGeometry.Spectral.Spectrum.GPreSpectrum

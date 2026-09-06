import InfoGeometry.Spectral.Spectrum.Integer

/-!
# Truncation contracts for integer-indexed spectra

The HoTT reference uses a hierarchy of truncation levels.  Mathlib does not
provide that same loop-space truncation carrier, so the port keeps the
property explicit rather than silently replacing it by a weaker proposition.
This interface is enough to transport any later, concrete truncation theory.
-/

namespace InfoGeometry.Spectral.Spectrum.Integer

universe u v

/-- A level-indexed property of stage carriers. -/
abbrev StageProperty := ℤ → (Type u) → Prop

/-- A prespectrum satisfies a level-indexed property stage by stage. -/
def Satisfies (P : StageProperty) (k : ℤ) (E : Prespectrum) : Prop :=
  ∀ n, P (k + n) (E.space n)

/-- A prespectrum equipped with an explicit truncation/property witness. -/
structure TruncatedPrespectrum (P : StageProperty) where
  carrier : Prespectrum
  level : ℤ
  satisfies : Satisfies P level carrier

namespace TruncatedPrespectrum

variable {P : StageProperty}

@[simp] theorem satisfies_at
    (E : TruncatedPrespectrum P) (n : ℤ) :
    P (E.level + n) (E.carrier.space n) :=
  E.satisfies n

/-- Reindexing a truncation witness without changing its carrier. -/
def changeLevel (E : TruncatedPrespectrum P) (k : ℤ)
    (h : ∀ n, P (k + n) (E.carrier.space n)) :
    TruncatedPrespectrum P where
  carrier := E.carrier
  level := k
  satisfies := h

@[simp] theorem changeLevel_carrier (E : TruncatedPrespectrum P) (k : ℤ)
    (h : ∀ n, P (k + n) (E.carrier.space n)) :
    (changeLevel E k h).carrier = E.carrier :=
  rfl

end TruncatedPrespectrum

/-- A spectrum with the same explicit stagewise property witness. -/
structure TruncatedSpectrum (P : StageProperty) where
  carrier : Spectrum
  level : ℤ
  satisfies : ∀ n, P (level + n) (carrier.space n)

namespace TruncatedSpectrum

variable {P : StageProperty}

@[simp] theorem satisfies_at
    (E : TruncatedSpectrum P) (n : ℤ) :
    P (E.level + n) (E.carrier.space n) :=
  E.satisfies n

/-- Forget the invertible structure maps while retaining the truncation data. -/
def toPrespectrum (E : TruncatedSpectrum P) : TruncatedPrespectrum P where
  carrier := E.carrier.toPrespectrum
  level := E.level
  satisfies := E.satisfies

@[simp] theorem toPrespectrum_carrier (E : TruncatedSpectrum P) :
    E.toPrespectrum.carrier = E.carrier.toPrespectrum :=
  rfl

def changeLevel (E : TruncatedSpectrum P) (k : ℤ)
    (h : ∀ n, P (k + n) (E.carrier.space n)) :
    TruncatedSpectrum P where
  carrier := E.carrier
  level := k
  satisfies := h

@[simp] theorem changeLevel_carrier (E : TruncatedSpectrum P) (k : ℤ)
    (h : ∀ n, P (k + n) (E.carrier.space n)) :
    (changeLevel E k h).carrier = E.carrier :=
  rfl

end TruncatedSpectrum

/-- A stagewise map preserving a level-indexed property. -/
structure PropertyMap (P : StageProperty) (E F : Prespectrum) where
  map : Integer.Map E F
  preserves : ∀ k n, P (k + n) (E.space n) → P (k + n) (F.space n)

instance {P : StageProperty} {E F : Prespectrum} :
    CoeFun (PropertyMap P E F) (fun _ => ∀ n, E.space n → F.space n) where
  coe f := f.map

@[simp] theorem PropertyMap.comm_apply
    {P : StageProperty} {E F : Prespectrum} (f : PropertyMap P E F)
    (n : ℤ) (x : E.space n) :
    f (n + 1) (E.step n x) = F.step n (f n x) :=
  f.map.comm n x

def PropertyMap.id (P : StageProperty) (E : Prespectrum) : PropertyMap P E E where
  map := Integer.Map.id E
  preserves := by
    intro k n h
    exact h

@[simp] theorem PropertyMap.id_apply
    {P : StageProperty} {E : Prespectrum} (n : ℤ) (x : E.space n) :
    PropertyMap.id P E n x = x :=
  rfl

def PropertyMap.comp
    {P : StageProperty} {E F G : Prespectrum}
    (g : PropertyMap P F G) (f : PropertyMap P E F) : PropertyMap P E G where
  map := Integer.Map.comp g.map f.map
  preserves := by
    intro k n h
    exact g.preserves k n (f.preserves k n h)

@[simp] theorem PropertyMap.comp_apply
    {P : StageProperty} {E F G : Prespectrum}
    (g : PropertyMap P F G) (f : PropertyMap P E F)
    (n : ℤ) (x : E.space n) :
    PropertyMap.comp g f n x = g n (f n x) :=
  rfl

theorem PropertyMap.map_satisfies
    {P : StageProperty} {E F : Prespectrum}
    (f : PropertyMap P E F) (k : ℤ)
    (hE : Satisfies P k E) :
    Satisfies P k F := by
  intro n
  exact f.preserves k n (hE n)

/-! A property-preserving map transports a bundled truncation witness. -/

def PropertyMap.map_truncated
    {P : StageProperty} {F : Spectrum}
    (source : TruncatedSpectrum P)
    (f : PropertyMap P source.carrier.toPrespectrum F.toPrespectrum) :
    TruncatedSpectrum P where
  carrier := F
  level := source.level
  satisfies := by
    intro n
    exact f.preserves source.level n (source.satisfies n)

@[simp] theorem PropertyMap.map_truncated_carrier
    {P : StageProperty} {F : Spectrum}
    (source : TruncatedSpectrum P)
    (f : PropertyMap P source.carrier.toPrespectrum F.toPrespectrum) :
    (f.map_truncated source).carrier = F :=
  rfl

@[simp] theorem PropertyMap.map_truncated_level
    {P : StageProperty} {F : Spectrum}
    (source : TruncatedSpectrum P)
    (f : PropertyMap P source.carrier.toPrespectrum F.toPrespectrum) :
    (f.map_truncated source).level = source.level :=
  rfl

end InfoGeometry.Spectral.Spectrum.Integer

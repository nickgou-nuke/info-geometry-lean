import InfoGeometry.Spectral.Homotopy.Suspension

/-!
# Dependent pointed function carriers

This is the ordinary carrier-level portion of the old `pointed_pi` file.
Pointwise homotopy and truncation properties are separate from this API.
-/

namespace InfoGeometry.Spectral.Homotopy.DependentPi

open InfoGeometry.Spectral.Homotopy.Suspension

def PiPointed {ι : Type*} (F : ι → Type*) (base : ∀ i, F i) : PointedReadout :=
  Pointed.mk (∀ i, F i) base

@[simp] theorem PiPointed_base {ι : Type*} (F : ι → Type*) (base : ∀ i, F i) (i : ι) :
    (PiPointed F base).base i = base i :=
  rfl

def PiPointed.map {ι : Type*} {F G : ι → Type*}
    {baseF : ∀ i, F i} {baseG : ∀ i, G i}
    (f : ∀ i, F i → G i)
    (hf : ∀ i, f i (baseF i) = baseG i) :
    PointedMap (PiPointed F baseF) (PiPointed G baseG) where
  toFun x i := f i (x i)
  map_base := by
    funext i
    exact hf i

@[simp] theorem PiPointed.map_apply {ι : Type*} {F G : ι → Type*}
    {baseF : ∀ i, F i} {baseG : ∀ i, G i}
    (f : ∀ i, F i → G i) (hf : ∀ i, f i (baseF i) = baseG i)
    (x : ∀ i, F i) (i : ι) :
    PiPointed.map f hf x i = f i (x i) :=
  rfl

theorem PiPointed.map_id {ι : Type*} {F : ι → Type*} {base : ∀ i, F i}
    (x : ∀ i, F i) :
    PiPointed.map (baseF := base) (baseG := base)
      (fun _i y => y) (fun _ => rfl) x = x := by
  funext i
  rfl

theorem PiPointed.map_comp {ι : Type*} {F G H : ι → Type*}
    {baseF : ∀ i, F i} {baseG : ∀ i, G i} {baseH : ∀ i, H i}
    (f : ∀ i, F i → G i) (g : ∀ i, G i → H i)
    (hf : ∀ i, f i (baseF i) = baseG i)
    (hg : ∀ i, g i (baseG i) = baseH i) (x : ∀ i, F i) :
    PiPointed.map g hg (PiPointed.map f hf x) =
      PiPointed.map (fun i y => g i (f i y))
        (fun i => (congrArg (g i) (hf i)).trans (hg i)) x := by
  funext i
  rfl

def PiPointed.constant {ι : Type*} (F : ι → Type*) (base : ∀ i, F i) :
    PointedMap (Pointed.mk PUnit PUnit.unit) (PiPointed F base) where
  toFun := fun _ => base
  map_base := rfl

@[simp] theorem PiPointed.constant_apply {ι : Type*} (F : ι → Type*)
    (base : ∀ i, F i) (x : PUnit) (i : ι) :
    PiPointed.constant F base x i = base i :=
  rfl

end InfoGeometry.Spectral.Homotopy.DependentPi

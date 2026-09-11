import InfoGeometry.Topology.D4StarFlowInvariantObservables
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Pointwise algebraic closure of orbit-invariant observables. -/

theorem orbitInvariant_zero
    {Y : Type*} [Zero Y] :
    OrbitInvariant (fun _ : FourPlaneVertex => (0 : Y)) := by
  intro v w h
  rfl

theorem orbitInvariant_one
    {Y : Type*} [One Y] :
    OrbitInvariant (fun _ : FourPlaneVertex => (1 : Y)) := by
  intro v w h
  rfl

theorem orbitInvariant_add
    {Y : Type*} [Add Y]
    {f g : FourPlaneVertex → Y}
    (hf : OrbitInvariant f) (hg : OrbitInvariant g) :
    OrbitInvariant (fun v => f v + g v) := by
  intro v w h
  exact congrArg₂ (fun a b => a + b) (hf v w h) (hg v w h)

theorem orbitInvariant_mul
    {Y : Type*} [Mul Y]
    {f g : FourPlaneVertex → Y}
    (hf : OrbitInvariant f) (hg : OrbitInvariant g) :
    OrbitInvariant (fun v => f v * g v) := by
  intro v w h
  exact congrArg₂ (fun a b => a * b) (hf v w h) (hg v w h)

theorem orbitInvariant_star
    {Y : Type*} [Star Y]
    {f : FourPlaneVertex → Y}
    (hf : OrbitInvariant f) :
    OrbitInvariant (fun v => star (f v)) := by
  intro v w h
  exact congrArg star (hf v w h)

theorem continuous_orbitInvariant_add
    {Y : Type*} [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]
    {f g : FourPlaneVertex → Y}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun v => f v + g v) :=
  hf.add hg

theorem continuous_orbitInvariant_mul
    {Y : Type*} [TopologicalSpace Y] [Mul Y] [ContinuousMul Y]
    {f g : FourPlaneVertex → Y}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun v => f v * g v) :=
  hf.mul hg

theorem descendObservable_add
    {Y : Type*} [Add Y]
    (f g : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (hg : OrbitInvariant g) (q : D4StarQuotient) :
    descendObservable (fun v => f v + g v)
      (orbitInvariant_add hf hg) q =
      descendObservable f hf q + descendObservable g hg q := by
  induction q using Quotient.inductionOn with
  | _ v => rfl

theorem descendObservable_mul
    {Y : Type*} [Mul Y]
    (f g : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (hg : OrbitInvariant g) (q : D4StarQuotient) :
    descendObservable (fun v => f v * g v)
      (orbitInvariant_mul hf hg) q =
      descendObservable f hf q * descendObservable g hg q := by
  induction q using Quotient.inductionOn with
  | _ v => rfl

theorem descendObservable_star
    {Y : Type*} [Star Y]
    (f : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (q : D4StarQuotient) :
    descendObservable (fun v => star (f v))
      (orbitInvariant_star hf) q =
      star (descendObservable f hf q) := by
  induction q using Quotient.inductionOn with
  | _ v => rfl

end InfoGeometry.Topology.PauliJungD4Star

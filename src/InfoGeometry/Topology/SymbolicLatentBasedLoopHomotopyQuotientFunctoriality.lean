import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientConcatenation
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientAssociativity
import InfoGeometry.Topology.SymbolicLatentBasedLoopPathFunctoriality
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Functoriality of the based-loop endpoint fiber

A continuous map carrying `x` to `y` transports the endpoint fiber over
`(x,x)` to the endpoint fiber over `(y,y)`.  This is only a topological
transport statement; it does not assert a quotient-level loop composition.
-/

def mapSymbolicLatentBasedLoopHomotopyQuotient
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    SymbolicLatentBasedLoopHomotopyQuotient x →
      SymbolicLatentBasedLoopHomotopyQuotient y :=
  fun q =>
    ⟨mapSymbolicLatentPathHomotopyQuotient f q.1, by
      rw [mapSymbolicLatentPathHomotopyQuotient_endpoint f q.1, q.2]
      simp [mapSymbolicLatentPathHomotopyEndpoint, hxy]⟩

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q).1 =
      mapSymbolicLatentPathHomotopyQuotient f q.1 :=
  rfl

theorem continuous_mapSymbolicLatentBasedLoopHomotopyQuotient
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    Continuous (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy) := by
  exact (continuous_symbolicLatentPathHomotopyQuotientMap f).comp
    continuous_subtype_val |>.subtype_mk
    (fun q => by
      change symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentPathHomotopyQuotient f q.1) = (y, y)
      rw [mapSymbolicLatentPathHomotopyQuotient_endpoint f q.1, q.2]
      simp [mapSymbolicLatentPathHomotopyEndpoint, hxy])

def symbolicLatentBasedLoopHomotopyQuotientTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient y) :=
  TopCat.ofHom
    { toFun := mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
      continuous_toFun :=
        continuous_mapSymbolicLatentBasedLoopHomotopyQuotient f hxy }

theorem symbolicLatentBasedLoopHomotopyQuotientTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy q =
      mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q :=
  rfl

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_constant
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f (x := x) (y := f x) rfl
        (symbolicLatentBasedLoopHomotopyQuotient_constant x) =
      symbolicLatentBasedLoopHomotopyQuotient_constant (f x) := by
  apply Subtype.ext
  apply Quotient.sound
  exact ⟨constantSymbolicLatentPathHomotopy (f.comp (constantSymbolicLatentPath x))⟩

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_id
    {X : Type} [TopologicalSpace X] {x : X} :
    mapSymbolicLatentBasedLoopHomotopyQuotient
        (ContinuousMap.id X) (x := x) (y := x) rfl = id := by
  funext q
  apply Subtype.ext
  change mapSymbolicLatentPathHomotopyQuotient
      (ContinuousMap.id X) q.1 = q.1
  exact congrFun
    (mapSymbolicLatentPathHomotopyQuotient_id (X := X)) q.1

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    mapSymbolicLatentBasedLoopHomotopyQuotient g hyz ∘
        mapSymbolicLatentBasedLoopHomotopyQuotient f hxy =
      mapSymbolicLatentBasedLoopHomotopyQuotient (g.comp f)
        (by exact (congrArg g hxy).trans hyz) := by
  funext q
  apply Subtype.ext
  change mapSymbolicLatentPathHomotopyQuotient g
      (mapSymbolicLatentPathHomotopyQuotient f q.1) =
    mapSymbolicLatentPathHomotopyQuotient (g.comp f) q.1
  exact congrFun
    (mapSymbolicLatentPathHomotopyQuotient_comp f g) q.1 |>.symm

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_endpoint_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentBasedLoopHomotopyQuotient g hyz
          (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q)) =
      mapSymbolicLatentPathHomotopyEndpoint g
        (mapSymbolicLatentPathHomotopyEndpoint f
          (symbolicLatentPathHomotopyEndpointMap q)) := by
  change symbolicLatentPathHomotopyEndpointMap
      (mapSymbolicLatentPathHomotopyQuotient g
        (mapSymbolicLatentPathHomotopyQuotient f q.1)) =
    mapSymbolicLatentPathHomotopyEndpoint g
      (mapSymbolicLatentPathHomotopyEndpoint f
        (symbolicLatentPathHomotopyEndpointMap q))
  rw [mapSymbolicLatentPathHomotopyQuotient_endpoint]
  rw [mapSymbolicLatentPathHomotopyQuotient_endpoint]

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_mk
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (basedLoopHomotopyQuotient_mk γ) =
      basedLoopHomotopyQuotient_mk
        (mapSymbolicLatentBasedLoopPath f hxy γ) := by
  apply Subtype.ext
  apply congrArg symbolicLatentPathHomotopyQuotientMap
  ext t
  rfl

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_concatenation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (basedLoopHomotopyQuotientConcatenation q₀ q₁) =
      basedLoopHomotopyQuotientConcatenation
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₀)
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₁) := by
  let γ₀ := basedLoopHomotopyQuotientRepresentativeLoop q₀
  let γ₁ := basedLoopHomotopyQuotientRepresentativeLoop q₁
  let q₀' := mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₀
  let q₁' := mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₁
  let γ₀' := basedLoopHomotopyQuotientRepresentativeLoop q₀'
  let γ₁' := basedLoopHomotopyQuotientRepresentativeLoop q₁'
  have h₀ : SymbolicLatentPathHomotopic γ₀'.1
      (mapSymbolicLatentPathContinuous f f.continuous γ₀.1) := by
    have hq : symbolicLatentPathHomotopyQuotientMap γ₀'.1 =
        symbolicLatentPathHomotopyQuotientMap
          (mapSymbolicLatentPathContinuous f f.continuous γ₀.1) := by
      have hbase : q₀'.1 = mapSymbolicLatentPathHomotopyQuotient f q₀.1 := by
        change q₀'.1 = mapSymbolicLatentPathHomotopyQuotient f q₀.1
        rfl
      exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₀').trans
        (hbase.trans (congrArg (mapSymbolicLatentPathHomotopyQuotient f)
          (basedLoopHomotopyQuotientRepresentative_quotient_eq q₀).symm))
    exact Quotient.exact hq
  have h₁ : SymbolicLatentPathHomotopic γ₁'.1
      (mapSymbolicLatentPathContinuous f f.continuous γ₁.1) := by
    have hq : symbolicLatentPathHomotopyQuotientMap γ₁'.1 =
        symbolicLatentPathHomotopyQuotientMap
          (mapSymbolicLatentPathContinuous f f.continuous γ₁.1) := by
      have hbase : q₁'.1 = mapSymbolicLatentPathHomotopyQuotient f q₁.1 := by
        change q₁'.1 = mapSymbolicLatentPathHomotopyQuotient f q₁.1
        rfl
      exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₁').trans
        (hbase.trans (congrArg (mapSymbolicLatentPathHomotopyQuotient f)
          (basedLoopHomotopyQuotientRepresentative_quotient_eq q₁).symm))
    exact Quotient.exact hq
  apply Subtype.ext
  change mapSymbolicLatentPathHomotopyQuotient f
      (basedLoopHomotopyQuotientConcatenation q₀ q₁).1 =
    (basedLoopHomotopyQuotientConcatenation q₀' q₁').1
  rw [basedLoopHomotopyQuotientConcatenation_eq_mk_representatives,
    basedLoopHomotopyQuotientConcatenation_eq_mk_representatives]
  change mapSymbolicLatentPathHomotopyQuotient f
      (symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1) =
    symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicLatentBasedLoopConcatenation γ₀' γ₁').1
  rw [mapSymbolicLatentPathHomotopyQuotient_mk]
  have hnat := congrArg Subtype.val
    (mapSymbolicLatentBasedLoopPath_canonicalSymbolicLatentBasedLoopConcatenation
      f hxy γ₀ γ₁)
  have hcomp : f.comp
      (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1 =
      mapSymbolicLatentPathContinuous f f.continuous
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1 := by
    ext t
    rfl
  have hcompQ :
      symbolicLatentPathHomotopyQuotientMap
          (f.comp (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1) =
        symbolicLatentPathHomotopyQuotientMap
          (mapSymbolicLatentPathContinuous f f.continuous
            (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1) :=
    congrArg symbolicLatentPathHomotopyQuotientMap hcomp
  have hnatQ :
      symbolicLatentPathHomotopyQuotientMap
          (mapSymbolicLatentPathContinuous f f.continuous
            (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1) =
        symbolicLatentPathHomotopyQuotientMap
          (canonicalSymbolicLatentBasedLoopConcatenation
            (mapSymbolicLatentBasedLoopPath f hxy γ₀)
            (mapSymbolicLatentBasedLoopPath f hxy γ₁)).1 := by
    exact congrArg symbolicLatentPathHomotopyQuotientMap hnat
  have hconcatQ :
      symbolicLatentPathHomotopyQuotientMap
          (canonicalSymbolicLatentBasedLoopConcatenation
            (mapSymbolicLatentBasedLoopPath f hxy γ₀)
            (mapSymbolicLatentBasedLoopPath f hxy γ₁)).1 =
        symbolicLatentPathHomotopyQuotientMap
          (canonicalSymbolicLatentBasedLoopConcatenation γ₀' γ₁').1 := by
    rcases SymbolicLatentPathHomotopic.symm h₀ with ⟨H₀⟩
    rcases SymbolicLatentPathHomotopic.symm h₁ with ⟨H₁⟩
    apply basedLoopConcatenation_quotient_congr
    · exact H₀
    · exact H₁
  exact hcompQ.trans (hnatQ.trans hconcatQ)

theorem symbolicLatentBasedLoopHomotopyQuotientTopCatHom_id
    {X : Type} [TopologicalSpace X] {x : X} :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom
        (ContinuousMap.id X) (x := x) (y := x) rfl =
      𝟙 (TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x)) := by
  ext q
  simpa [symbolicLatentBasedLoopHomotopyQuotientTopCatHom] using
    congrArg (fun r => r.1)
      (congrFun
        (mapSymbolicLatentBasedLoopHomotopyQuotient_id (X := X) (x := x)) q)

theorem symbolicLatentBasedLoopHomotopyQuotientTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz =
      symbolicLatentBasedLoopHomotopyQuotientTopCatHom (g.comp f)
        (by exact (congrArg g hxy).trans hyz) := by
    ext q
    simpa [symbolicLatentBasedLoopHomotopyQuotientTopCatHom] using
    congrArg (fun r => r.1)
      (congrFun
        (mapSymbolicLatentBasedLoopHomotopyQuotient_comp f g hxy hyz) q)

theorem symbolicLatentBasedLoopHomotopyQuotientTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz) q =
      symbolicLatentBasedLoopHomotopyQuotientTopCatHom (g.comp f)
        (by exact (congrArg g hxy).trans hyz) q := by
  exact congrArg (fun m => m q)
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom_comp
      (f := f) (g := g) (hxy := hxy) (hyz := hyz))

end InfoGeometry.Topology

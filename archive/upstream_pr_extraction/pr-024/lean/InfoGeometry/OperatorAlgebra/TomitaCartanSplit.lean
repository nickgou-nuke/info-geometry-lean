/-
InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean

Tomita-Cartan splitting and the origin of the doubled Krein sign.

This module isolates the algebraic mechanism:

* Tomita reflection routes algebra generators into the commutant.
* Cartan parity decides whether the mirror contribution enters with `+` or `-`.
* The doubled carrier has a natural Krein pairing.
* Trivial center/factor hypotheses collapse algebra-commutant overlaps to
  scalars; a separate representation bridge is needed to identify such collapse
  with a null/isotropic defect.
-/

import Mathlib
import InfoGeometry.Geometry.KreinIsotropicCone
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TomitaCartanSplit

universe uOp uSplit uCarrier uH

/-! ## 0. Cartan routing, overlap, and chiral-stage sockets -/

/-! ## 0a. Tomita mirror involution -/

/--
A Tomita-style mirror involution on an ambient operator algebra.

The intended model is `mirror X = J X J`, sending an algebra into its commutant
and back.  This socket records only the algebraic laws needed to prove the
mirror-even/mirror-odd lift theorems.
-/
structure MirrorInvolution
    (Op : Type uOp) [Ring Op] where
  /-- Mirror operation, morally `X ↦ J X J`. -/
  mirror : Op → Op

  map_zero :
    mirror 0 = 0

  map_one :
    mirror 1 = 1

  map_add :
    ∀ x y : Op, mirror (x + y) = mirror x + mirror y

  map_neg :
    ∀ x : Op, mirror (-x) = -mirror x

  map_mul :
    ∀ x y : Op, mirror (x * y) = mirror x * mirror y

  involutive :
    ∀ x : Op, mirror (mirror x) = x

namespace MirrorInvolution

variable {Op : Type uOp} [Ring Op]
variable (M : MirrorInvolution Op)

/-- Mirror preserves subtraction. -/
theorem map_sub
    (x y : Op) :
    M.mirror (x - y) = M.mirror x - M.mirror y := by
  simp [sub_eq_add_neg, M.map_add, M.map_neg]

/-- The compact/Tomita-even lift: `X ↦ X + mirror X`. -/
def compactLift
    (x : Op) : Op :=
  x + M.mirror x

/-- The noncompact/Tomita-odd lift: `X ↦ X - mirror X`. -/
def noncompactLift
    (x : Op) : Op :=
  x - M.mirror x

/-- Compact lifts are mirror-even. -/
theorem mirror_compactLift
    (x : Op) :
    M.mirror (M.compactLift x) = M.compactLift x := by
  dsimp [compactLift]
  rw [M.map_add, M.involutive]
  ac_rfl

/-- Noncompact lifts are mirror-odd. -/
theorem mirror_noncompactLift
    (x : Op) :
    M.mirror (M.noncompactLift x) = -M.noncompactLift x := by
  dsimp [noncompactLift]
  rw [M.map_sub, M.involutive]
  abel

end MirrorInvolution

/-! ## 0b. Cartan sign classification for mirror lifts -/

/-- Cartan sign of a generator relative to the Tomita mirror. -/
inductive CartanSign where
  /-- Compact/mirror-even sector. -/
  | compact
  /-- Noncompact/mirror-odd sector. -/
  | noncompact
deriving DecidableEq, Repr

/-- Lift a generator according to its Cartan sign. -/
def cartanLift
    {Op : Type uOp} [Ring Op]
    (M : MirrorInvolution Op)
    (sign : CartanSign)
    (x : Op) : Op :=
  match sign with
  | CartanSign.compact => M.compactLift x
  | CartanSign.noncompact => M.noncompactLift x

namespace MirrorInvolution

variable {Op : Type uOp} [Ring Op]
variable (M : MirrorInvolution Op)

/-- Compact Cartan lifts are mirror-even. -/
theorem mirror_cartanLift_compact
    (x : Op) :
    M.mirror (cartanLift M CartanSign.compact x) =
      cartanLift M CartanSign.compact x :=
  M.mirror_compactLift x

/-- Noncompact Cartan lifts are mirror-odd. -/
theorem mirror_cartanLift_noncompact
    (x : Op) :
    M.mirror (cartanLift M CartanSign.noncompact x) =
      -cartanLift M CartanSign.noncompact x :=
  M.mirror_noncompactLift x

end MirrorInvolution

/--
Abstract Cartan/Tomita routing datum on an operator-like ring.

`theta` is the Cartan involution/sign routing on generators.  `mirror` is the
Tomita mirror, morally `X ↦ J X J`.  Only the negation law for `mirror` is
needed to prove the compact/noncompact sign split.
-/
structure TomitaCartanDatum
    (Op : Type uOp) [Ring Op] where
  /-- Cartan involution/sign routing. -/
  theta : Op → Op

  /-- Tomita mirror, morally `X ↦ J X J`. -/
  mirror : Op → Op

  /-- The mirror respects negation. -/
  mirror_neg :
    ∀ X : Op, mirror (-X) = -mirror X

namespace TomitaCartanDatum

variable {Op : Type uOp} [Ring Op]
variable (C : TomitaCartanDatum Op)

/-- A compact generator is fixed by the Cartan involution. -/
def IsCompactGenerator
    (X : Op) : Prop :=
  C.theta X = X

/-- A noncompact generator is negated by the Cartan involution. -/
def IsNoncompactGenerator
    (X : Op) : Prop :=
  C.theta X = -X

/--
The Tomita-Cartan global lift:

`X ↦ X + mirror(theta X)`.

This single formula produces the compact `+` sign and noncompact `-` sign.
-/
def globalGenerator
    (X : Op) : Op :=
  X + C.mirror (C.theta X)

/-- Compact generators lift symmetrically: `X ↦ X + mirror X`. -/
theorem globalGenerator_compact
    {X : Op}
    (hX : C.IsCompactGenerator X) :
    C.globalGenerator X = X + C.mirror X := by
  unfold globalGenerator IsCompactGenerator at *
  rw [hX]

/--
Noncompact generators lift antisymmetrically: `X ↦ X - mirror X`.

This is the formal Cartan sign source of the doubled/Krein relative minus.
-/
theorem globalGenerator_noncompact
    {X : Op}
    (hX : C.IsNoncompactGenerator X) :
    C.globalGenerator X = X - C.mirror X := by
  unfold globalGenerator IsNoncompactGenerator at *
  rw [hX, C.mirror_neg]
  simp [sub_eq_add_neg]

end TomitaCartanDatum

/-- An element is central if it commutes with every element of the ambient ring. -/
def IsCentral
    {Op : Type uOp} [Ring Op]
    (x : Op) : Prop :=
  ∀ y : Op, x * y = y * x

/--
Abstract routing between an algebra and its commutant.

If an element is declared to live in both the algebra and the commutant, it is
central.  This is the algebraic content of `M ∩ M' ⊆ Z(M)`.
-/
structure AlgebraCommutantRouting
    (Op : Type uOp) [Ring Op] where
  InAlgebra : Op → Prop
  InCommutant : Op → Prop

  overlap_central :
    ∀ x : Op,
      InAlgebra x →
      InCommutant x →
        IsCentral x

/--
Factor-like trivial-center datum.

`IsScalar` is left abstract because the scalar embedding depends on the
concrete model.  In a von Neumann factor this means `Z(M) = C * 1`, or the real
analogue.
-/
structure FactorCenterDatum
    (Op : Type uOp) [Ring Op] where
  IsScalar : Op → Prop

  center_trivial :
    ∀ x : Op,
      IsCentral x →
        IsScalar x

namespace FactorCenterDatum

variable {Op : Type uOp} [Ring Op]
variable (R : AlgebraCommutantRouting Op)
variable (F : FactorCenterDatum Op)

/--
If an element lies in both the algebra and the commutant, then in a factor-like
model it is scalar.
-/
theorem overlap_is_scalar
    {x : Op}
    (hM : R.InAlgebra x)
    (hC : R.InCommutant x) :
    F.IsScalar x :=
  F.center_trivial x (R.overlap_central x hM hC)

end FactorCenterDatum

/--
A Krein quadratic datum on a carrier.

The isotropic cone is geometric.  It is not definitionally a zero-divisor
locus.
-/
structure KreinQuadraticDatum
    (H : Type uH) [Zero H] where
  q : H → ℝ
  q_zero :
    q 0 = 0

/-- The isotropic/null cone of the Krein quadratic datum. -/
def IsotropicCone
    {H : Type uH} [Zero H]
    (Q : KreinQuadraticDatum H) : Set H :=
  {v : H | Q.q v = 0}

@[simp]
theorem zero_mem_isotropicCone
    {H : Type uH} [Zero H]
    (Q : KreinQuadraticDatum H) :
    (0 : H) ∈ IsotropicCone Q := by
  simp [IsotropicCone, Q.q_zero]

/--
A bridge saying that algebra/commutant overlap is read geometrically as
isotropic.

This is representation-dependent.  It should not be derived from the factor
property alone.
-/
structure TomitaOverlapToIsotropicBridge
    (Op : Type uOp) [Ring Op]
    (H : Type uH) [Zero H]
    (R : AlgebraCommutantRouting Op) where
  quadratic : KreinQuadraticDatum H

  /-- Carrier readout of an operator. -/
  carrierReadout : Op → H

  /-- Overlap elements land on the isotropic cone under the chosen representation. -/
  overlap_maps_to_isotropic :
    ∀ x : Op,
      R.InAlgebra x →
      R.InCommutant x →
        carrierReadout x ∈ IsotropicCone quadratic

namespace TomitaOverlapToIsotropicBridge

variable {Op : Type uOp} [Ring Op]
variable {H : Type uH} [Zero H]
variable {R : AlgebraCommutantRouting Op}

/-- Re-export: an algebra/commutant overlap element maps to the Krein null cone. -/
theorem overlap_isotropic
    (B : TomitaOverlapToIsotropicBridge Op H R)
    {x : Op}
    (hM : R.InAlgebra x)
    (hC : R.InCommutant x) :
    B.carrierReadout x ∈ IsotropicCone B.quadratic :=
  B.overlap_maps_to_isotropic x hM hC

end TomitaOverlapToIsotropicBridge

/--
A chiral stage is kinematic data: complementary projectors already exist before
a gauge force acts on them.
-/
structure ChiralStage
    (Op : Type uOp) [Ring Op] where
  Pleft : Op
  Pright : Op

  Pleft_idem :
    Pleft * Pleft = Pleft

  Pright_idem :
    Pright * Pright = Pright

  complementary :
    Pleft + Pright = 1

  disjoint_left :
    Pleft * Pright = 0

  disjoint_right :
    Pright * Pleft = 0

/--
Dynamics on a chiral stage.

The action depends on the stage.  The stage does not depend on the action. This
is the type-theoretic version of kinematics before dynamics.
-/
structure ChiralDynamics
    (G : Type*) [Group G]
    (Op : Type uOp) [Ring Op]
    (Stage : ChiralStage Op) where
  act : G → Op → Op

  /-- Left sector is preserved by the dynamics. -/
  preserves_left_sector :
    ∀ g : G, ∀ X : Op, act g (Stage.Pleft * X) = Stage.Pleft * act g X

  /-- Right sector is preserved by the dynamics. -/
  preserves_right_sector :
    ∀ g : G, ∀ X : Op, act g (Stage.Pright * X) = Stage.Pright * act g X

/--
An action may be left-chiral.  This is contingent dynamics, not the definition
of the left projector itself.
-/
structure LeftChiralDynamics
    (G : Type*) [Group G]
    (Op : Type uOp) [Ring Op]
    (Stage : ChiralStage Op)
    extends ChiralDynamics G Op Stage where
  /-- Right sector is dynamically trivial. -/
  right_sector_trivial :
    ∀ g : G, ∀ X : Op, act g (Stage.Pright * X) = Stage.Pright * X

namespace ChiralDynamics

variable {G : Type*} [Group G]
variable {Op : Type uOp} [Ring Op]
variable {Stage : ChiralStage Op}

/-- The left sector is preserved exactly as recorded in the dynamics witness. -/
theorem act_preserves_left_sector
    (D : ChiralDynamics G Op Stage)
    (g : G) (X : Op) :
    D.act g (Stage.Pleft * X) = Stage.Pleft * D.act g X :=
  D.preserves_left_sector g X

/-- The right sector is preserved exactly as recorded in the dynamics witness. -/
theorem act_preserves_right_sector
    (D : ChiralDynamics G Op Stage)
    (g : G) (X : Op) :
    D.act g (Stage.Pright * X) = Stage.Pright * D.act g X :=
  D.preserves_right_sector g X

end ChiralDynamics

namespace LeftChiralDynamics

variable {G : Type*} [Group G]
variable {Op : Type uOp} [Ring Op]
variable {Stage : ChiralStage Op}

/-- Left-chiral dynamics is trivial on the right sector. -/
theorem act_right_sector_trivial
    (D : LeftChiralDynamics G Op Stage)
    (g : G) (X : Op) :
    D.act g (Stage.Pright * X) = Stage.Pright * X :=
  D.right_sector_trivial g X

end LeftChiralDynamics

/--
Owner target for the Tomita-Cartan algebraic routing layer.

The nontrivial analytic/von-Neumann content is supplied by concrete modules.
This owner target only records that once the data are supplied, the compact and
noncompact lift signs are formally available.
-/
structure TomitaCartanSplitOwnerTarget where
  /-- Compact Cartan lifts follow the `+` sign rule. -/
  compact_transport :
    ∀ (Op : Type uOp) [Ring Op],
    ∀ C : TomitaCartanDatum Op,
    ∀ X : Op,
      C.IsCompactGenerator X → C.globalGenerator X = X + C.mirror X

  /-- Noncompact Cartan lifts follow the `-` sign rule. -/
  noncompact_transport :
    ∀ (Op : Type uOp) [Ring Op],
    ∀ C : TomitaCartanDatum Op,
    ∀ X : Op,
      C.IsNoncompactGenerator X → C.globalGenerator X = X - C.mirror X

/-- The owner target is proved by the Cartan sign-routing theorems. -/
theorem tomitaCartanSplitOwnerTarget :
    TomitaCartanSplitOwnerTarget := by
  refine ⟨?_, ?_⟩
  · intro Op _ C X hX
    exact C.globalGenerator_compact hX
  · intro Op _ C X hX
    exact C.globalGenerator_noncompact hX

/-! ## 1. Tomita algebra/commutant skeleton -/

/--
Abstract Tomita commutant datum.

`M` is the algebra side, `Mcomm` is the commutant side, and `tomitaMirror`
is the abstract operation corresponding to `x ↦ J x J`.

The field `overlap_scalar` is the factor-like condition: anything lying in
both `M` and `Mcomm` is scalar.
-/
structure TomitaCommutantDatum
    (Op : Type uOp) [Ring Op] where
  /-- Algebra side. -/
  M : Set Op

  /-- Commutant side. -/
  Mcomm : Set Op

  /-- Scalar/central sector. -/
  scalar : Set Op

  /-- Tomita mirror, morally `x ↦ J x J`. -/
  tomitaMirror : Op → Op

  /-- The Tomita mirror sends algebra elements to the commutant. -/
  mirror_M_to_comm :
    ∀ x : Op, x ∈ M → tomitaMirror x ∈ Mcomm

  /-- The Tomita mirror sends commutant elements back to the algebra. -/
  mirror_comm_to_M :
    ∀ x : Op, x ∈ Mcomm → tomitaMirror x ∈ M

  /--
  Factor-like center condition: if an element belongs to both the algebra and
  the commutant, it is scalar.
  -/
  overlap_scalar :
    ∀ x : Op, x ∈ M → x ∈ Mcomm → x ∈ scalar

namespace TomitaCommutantDatum

variable {Op : Type uOp} [Ring Op]
variable (T : TomitaCommutantDatum Op)

/-- An element lies in the algebra/commutant overlap. -/
def InOverlap
    (x : Op) : Prop :=
  x ∈ T.M ∧ x ∈ T.Mcomm

/-- The overlap is scalar. -/
theorem overlap_is_scalar
    {x : Op}
    (hx : T.InOverlap x) :
    x ∈ T.scalar :=
  T.overlap_scalar x hx.1 hx.2

end TomitaCommutantDatum

/-! ## 1a. Tomita algebra pair and factor-overlap exclusion -/

/--
Abstract Tomita algebra pair.

`M` is the algebra side.  `Mcomm` is the commutant side.  `Jconj` is the
Tomita mirror operation at this abstract layer.

The key factor property is encoded by `overlap_is_scalar`.
-/
structure TomitaAlgebraPair
    (Op : Type uOp) where
  /-- Algebra side. -/
  M : Set Op

  /-- Commutant side. -/
  Mcomm : Set Op

  /-- Tomita mirror operation, morally `X ↦ J X J`. -/
  Jconj : Op → Op

  /-- Predicate for scalar/central elements. -/
  IsScalar : Op → Prop

  /-- Tomita mirror maps algebra-side elements into the commutant side. -/
  J_maps_M_to_comm :
    ∀ x : Op, x ∈ M → Jconj x ∈ Mcomm

  /-- Tomita mirror maps commutant-side elements back into the algebra side. -/
  J_maps_comm_to_M :
    ∀ x : Op, x ∈ Mcomm → Jconj x ∈ M

  /--
  Factor-center/trivial-overlap principle: if an element lies in both `M` and
  `Mcomm`, it is scalar.
  -/
  overlap_is_scalar :
    ∀ x : Op, x ∈ M → x ∈ Mcomm → IsScalar x

namespace TomitaAlgebraPair

variable {Op : Type uOp}
variable (T : TomitaAlgebraPair Op)

/-- The overlap of the algebra and commutant is scalar. -/
theorem overlap_scalar
    {x : Op}
    (hM : x ∈ T.M)
    (hC : x ∈ T.Mcomm) :
    T.IsScalar x :=
  T.overlap_is_scalar x hM hC

/-- The Tomita mirror of an algebra-side element is commutant-side. -/
theorem mirror_mem_comm
    {x : Op}
    (hM : x ∈ T.M) :
    T.Jconj x ∈ T.Mcomm :=
  T.J_maps_M_to_comm x hM

/-- The Tomita mirror of a commutant-side element is algebra-side. -/
theorem mirror_mem_M
    {x : Op}
    (hC : x ∈ T.Mcomm) :
    T.Jconj x ∈ T.M :=
  T.J_maps_comm_to_M x hC

end TomitaAlgebraPair

/--
A factor-overlap exclusion datum.

`Dynamic x` means that `x` carries non-scalar dynamical information.  The field
`scalar_not_dynamic` says scalars carry no such information.

Together with `overlap_is_scalar`, this proves that no dynamic operator can
live simultaneously in the algebra and its commutant.
-/
structure FactorOverlapExclusion
    (Op : Type uOp) where
  pair : TomitaAlgebraPair Op

  /-- Predicate for non-scalar dynamical content. -/
  Dynamic : Op → Prop

  /-- Scalars carry no dynamical content. -/
  scalar_not_dynamic :
    ∀ x : Op, pair.IsScalar x → ¬ Dynamic x

namespace FactorOverlapExclusion

variable {Op : Type uOp}
variable (F : FactorOverlapExclusion Op)

/--
No dynamical operator can occupy both the algebra and commutant sides.

This is the formal “no room in the center” theorem.
-/
theorem no_dynamic_in_overlap
    {x : Op}
    (hM : x ∈ F.pair.M)
    (hC : x ∈ F.pair.Mcomm) :
    ¬ F.Dynamic x :=
  F.scalar_not_dynamic x
    (F.pair.overlap_scalar hM hC)

/--
Equivalently: if an element is dynamic and lies on the algebra side, then it
cannot also lie in the commutant.
-/
theorem dynamic_M_not_comm
    {x : Op}
    (hdyn : F.Dynamic x)
    (hM : x ∈ F.pair.M) :
    x ∉ F.pair.Mcomm := by
  intro hC
  exact F.no_dynamic_in_overlap hM hC hdyn

/--
Equivalently: if an element is dynamic and lies on the commutant side, then it
cannot also lie in the algebra.
-/
theorem dynamic_comm_not_M
    {x : Op}
    (hdyn : F.Dynamic x)
    (hC : x ∈ F.pair.Mcomm) :
    x ∉ F.pair.M := by
  intro hM
  exact F.no_dynamic_in_overlap hM hC hdyn

end FactorOverlapExclusion

/-! ## 2. Cartan sign routing in a represented algebra -/

/--
Cartan sector of a symmetry generator.

Compact directions are routed symmetrically across the Tomita mirror.
Noncompact directions are routed antisymmetrically.
-/
inductive CartanSector where
  | compact
  | noncompact
deriving DecidableEq, Repr

namespace CartanSector

/--
Mirror sign for the Tomita-routed global generator.

Compact generators use `+`; noncompact generators use `-`.
-/
def mirrorSign : CartanSector → ℝ
  | compact => 1
  | noncompact => -1

@[simp]
theorem mirrorSign_compact :
    mirrorSign compact = 1 :=
  rfl

@[simp]
theorem mirrorSign_noncompact :
    mirrorSign noncompact = -1 :=
  rfl

end CartanSector

/--
Global generator formed from a local component and its Tomita mirror.

Compact sector: `local + mirror`.

Noncompact sector: `local - mirror`.
-/
def globalFrom
    {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]
    (sector : CartanSector)
    (localPart mirror : Op) : Op :=
  localPart + CartanSector.mirrorSign sector • mirror

@[simp]
theorem globalFrom_compact
    {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]
    (localPart mirror : Op) :
    globalFrom CartanSector.compact localPart mirror = localPart + mirror := by
  simp [globalFrom]

@[simp]
theorem globalFrom_noncompact
    {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]
    (localPart mirror : Op) :
    globalFrom CartanSector.noncompact localPart mirror = localPart - mirror := by
  simp [globalFrom, sub_eq_add_neg]

/--
A Tomita-routed Cartan generator.

`localPart` lies on the algebra side.  `mirror` lies on the commutant side.
The sector determines whether the global routed generator is symmetric or
antisymmetric.
-/
structure RoutedCartanGenerator
    (Op : Type uOp) [AddCommGroup Op] [Module ℝ Op] where
  sector : CartanSector
  localPart : Op
  mirror : Op

namespace RoutedCartanGenerator

variable
    {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]

/-- The global routed generator. -/
def global
    (G : RoutedCartanGenerator Op) : Op :=
  globalFrom G.sector G.localPart G.mirror

/-- Compact routed generators are local plus mirror. -/
theorem global_eq_plus
    (localPart mirror : Op) :
    (RoutedCartanGenerator.global
      ({ sector := CartanSector.compact, localPart := localPart, mirror := mirror } :
        RoutedCartanGenerator Op)) =
      localPart + mirror := by
  simp [global]

/-- Noncompact routed generators are local minus mirror. -/
theorem global_eq_minus
    (localPart mirror : Op) :
    (RoutedCartanGenerator.global
      ({ sector := CartanSector.noncompact, localPart := localPart, mirror := mirror } :
        RoutedCartanGenerator Op)) =
      localPart - mirror := by
  simp [global]

end RoutedCartanGenerator

/-- A Cartan generator with explicit Tomita routing evidence. -/
structure TomitaRoutedCartanGenerator
    (Op : Type uOp) [AddCommGroup Op] [Module ℝ Op]
    (T : TomitaAlgebraPair Op) where
  sector : CartanSector

  /-- Local algebra-side component. -/
  localPart : Op

  /-- Local component lies in `M`. -/
  local_mem_M :
    localPart ∈ T.M

  /-- Mirror commutant-side component. -/
  mirror : Op

  /-- The mirror is obtained by Tomita conjugation. -/
  mirror_eq :
    mirror = T.Jconj localPart

namespace TomitaRoutedCartanGenerator

variable
    {Op : Type uOp} [AddCommGroup Op] [Module ℝ Op]
    {T : TomitaAlgebraPair Op}

variable (G : TomitaRoutedCartanGenerator Op T)

/-- The mirror component lies in the commutant. -/
theorem mirror_mem_comm :
    G.mirror ∈ T.Mcomm := by
  rw [G.mirror_eq]
  exact T.J_maps_M_to_comm G.localPart G.local_mem_M

/-- The routed global generator. -/
def global : Op :=
  globalFrom G.sector G.localPart G.mirror

end TomitaRoutedCartanGenerator

/--
Mirror combination dictated by the Cartan sector.

`compact`: `x + xJ`

`noncompact`: `x - xJ`
-/
def mirrorCombination
    {Op : Type uOp} [AddGroup Op]
    (sector : CartanSector)
    (x xJ : Op) : Op :=
  match sector with
  | CartanSector.compact => x + xJ
  | CartanSector.noncompact => x - xJ

@[simp]
theorem mirrorCombination_compact
    {Op : Type uOp} [AddGroup Op]
    (x xJ : Op) :
    mirrorCombination CartanSector.compact x xJ = x + xJ :=
  rfl

@[simp]
theorem mirrorCombination_noncompact
    {Op : Type uOp} [AddGroup Op]
    (x xJ : Op) :
    mirrorCombination CartanSector.noncompact x xJ = x - xJ :=
  rfl

/-- A Cartan generator together with its Tomita mirror. -/
structure CartanTomitaGenerator
    {Op : Type uOp} [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Local/algebra-side generator. -/
  localGen : Op

  /-- Mirror/commutant-side generator. -/
  mirror : Op

  /-- Compact or noncompact sector. -/
  sector : CartanSector

  /-- The local generator belongs to the algebra. -/
  local_mem :
    localGen ∈ T.M

  /-- The mirror is the Tomita mirror of the local generator. -/
  mirror_eq :
    mirror = T.tomitaMirror localGen

namespace CartanTomitaGenerator

variable {Op : Type uOp} [Ring Op]
variable {T : TomitaCommutantDatum Op}

/-- The mirror generator belongs to the commutant. -/
theorem mirror_mem_comm
    (X : CartanTomitaGenerator T) :
    X.mirror ∈ T.Mcomm := by
  rw [X.mirror_eq]
  exact T.mirror_M_to_comm X.localGen X.local_mem

/-- The doubled/global Cartan generator in the represented algebra. -/
def globalGenerator
    (X : CartanTomitaGenerator T) : Op :=
  mirrorCombination X.sector X.localGen X.mirror

/--
If the local generator also belongs to the commutant, then it is scalar.

This is the formal exclusion principle for a factor-like datum.
-/
theorem local_scalar_of_also_comm
    (X : CartanTomitaGenerator T)
    (hcomm : X.localGen ∈ T.Mcomm) :
    X.localGen ∈ T.scalar :=
  T.overlap_scalar X.localGen X.local_mem hcomm

/-- If the mirror generator also belongs to the algebra, then it is scalar. -/
theorem mirror_scalar_of_also_M
    (X : CartanTomitaGenerator T)
    (hM : X.mirror ∈ T.M) :
    X.mirror ∈ T.scalar :=
  T.overlap_scalar X.mirror hM (X.mirror_mem_comm)

end CartanTomitaGenerator

/-! ## 3. Symmetric versus antisymmetric mirror readouts -/

/-- Symmetric mirror readout: compact-like routing. -/
def symmetricMirrorReadout
    (a b : ℝ) : ℝ :=
  a + b

/-- Antisymmetric mirror readout: noncompact/Krein-like routing. -/
def antisymmetricMirrorReadout
    (a b : ℝ) : ℝ :=
  a - b

/-- The compact/symmetric readout is invariant under swapping mirror sectors. -/
theorem symmetricMirrorReadout_swap
    (a b : ℝ) :
    symmetricMirrorReadout b a = symmetricMirrorReadout a b := by
  dsimp [symmetricMirrorReadout]
  ring

/-- The noncompact/antisymmetric readout changes sign under swapping sectors. -/
theorem antisymmetricMirrorReadout_swap
    (a b : ℝ) :
    antisymmetricMirrorReadout b a =
      - antisymmetricMirrorReadout a b := by
  dsimp [antisymmetricMirrorReadout]
  ring

/--
The antisymmetric readout vanishes on the diagonal overlap.

This is the toy algebraic shadow of the statement that forcing both sides into
the same slot kills the noncompact/Krein readout.
-/
theorem antisymmetricMirrorReadout_diagonal_zero
    (a : ℝ) :
    antisymmetricMirrorReadout a a = 0 := by
  dsimp [antisymmetricMirrorReadout]
  ring

/-! ## 3a. Split/Krein pairing from doubled routing -/

/--
Minimal quadratic pairing datum on a real module.

The only property needed here is that the diagonal value is invariant under
negating both inputs.  This is enough to prove that both diagonal and
anti-diagonal doubled vectors are null for the split form.
-/
structure SplitPairingDatum
    (X : Type*) [AddCommGroup X] [Module ℝ X] where
  form : X → X → ℝ
  neg_neg :
    ∀ x : X, form (-x) (-x) = form x x

namespace SplitPairingDatum

variable
    {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (B : SplitPairingDatum X)

/--
The split/Krein quadratic form on the doubled carrier `X × X`.

`Q(x, y) = B(x, x) - B(y, y)`.
-/
def splitQuadratic
    (u : X × X) : ℝ :=
  B.form u.1 u.1 - B.form u.2 u.2

/-- The diagonal is isotropic for the split quadratic form. -/
theorem diagonal_isotropic
    (x : X) :
    B.splitQuadratic (x, x) = 0 := by
  simp [splitQuadratic]

/--
The anti-diagonal is also isotropic, provided the base form has
`B(-x, -x) = B(x, x)`.
-/
theorem antiDiagonal_isotropic
    (x : X) :
    B.splitQuadratic (x, -x) = 0 := by
  dsimp [splitQuadratic]
  rw [B.neg_neg x]
  exact sub_self (B.form x x)

/--
Equal local/mirror norm gives a null doubled vector.

This is the algebraic source of the null boundary in the doubled Krein model.
-/
theorem equal_magnitude_isotropic
    (x y : X)
    (h : B.form x x = B.form y y) :
    B.splitQuadratic (x, y) = 0 := by
  dsimp [splitQuadratic]
  exact sub_eq_zero.mpr h

end SplitPairingDatum

/-! ## 4. Defect-to-null bridge socket -/

/--
A bridge from algebraic Tomita/Drazin defects to a carrier null readout.

This structure deliberately does not define defects as isotropic vectors. It
says that a representation/readout maps algebraic defects to a null carrier
condition.
-/
structure TomitaDefectNullBridge
    (Op : Type uOp) [Ring Op]
    (Split : Type uSplit)
    (Carrier : Type uCarrier)
    [AddCommGroup Carrier] [Module ℝ Carrier]
    (T : TomitaCommutantDatum Op) where
  /-- Algebraic defect locus in the split source. -/
  defectLocus : Set Split

  /-- Carrier readout of split data. -/
  carrierReadout : Split → Carrier

  /-- Quadratic/null readout on the carrier. -/
  q : Carrier → ℝ

  /-- Operator image of a split element. -/
  representedOperator : Split → Op

  /-- Defects try to land in the algebra/commutant overlap. -/
  defect_overlap :
    ∀ a : Split,
      a ∈ defectLocus →
        T.InOverlap (representedOperator a)

  /-- Defects are null under the carrier quadratic readout. -/
  defect_null :
    ∀ a : Split,
      a ∈ defectLocus →
        q (carrierReadout a) = 0

namespace TomitaDefectNullBridge

variable
    {Op : Type uOp} [Ring Op]
    {Split : Type uSplit}
    {Carrier : Type uCarrier}
    [AddCommGroup Carrier] [Module ℝ Carrier]
    {T : TomitaCommutantDatum Op}
    (B : TomitaDefectNullBridge Op Split Carrier T)

/-- A defect overlap is scalar by the factor-like Tomita datum. -/
theorem defect_overlap_scalar
    {a : Split}
    (ha : a ∈ B.defectLocus) :
    B.representedOperator a ∈ T.scalar :=
  T.overlap_is_scalar (B.defect_overlap a ha)

/-- A defect is null under the carrier readout. -/
theorem defect_is_null
    {a : Split}
    (ha : a ∈ B.defectLocus) :
    B.q (B.carrierReadout a) = 0 :=
  B.defect_null a ha

end TomitaDefectNullBridge

/-! ## 1. Doubled Krein carrier -/

/--
The doubled carrier `H × H`.

The first component is the algebra side; the second component is the Tomita
mirror/commutant side.
-/
abbrev Doubled
    (H : Type*) :=
  H × H

/--
The canonical split Krein form on `H × H`.

`((x1, x2), (y1, y2)) ↦ inner x1 y1 - inner x2 y2`.
-/
def doubledKreinForm
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : Doubled H) : ℝ :=
  inner (𝕜 := ℝ) x.1 y.1 - inner (𝕜 := ℝ) x.2 y.2

/--
The diagonal copy is isotropic for the doubled Krein form.

This is the algebraic model of "same state on both sides has zero split norm."
-/
theorem diagonal_isotropic
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : H) :
    doubledKreinForm (v, v) (v, v) = 0 := by
  simp [doubledKreinForm]

/-- The anti-diagonal copy is also isotropic. -/
theorem antidiagonal_isotropic
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : H) :
    doubledKreinForm (v, -v) (v, -v) = 0 := by
  simp [doubledKreinForm]

/-! ## 2. Cartan parity and signed Tomita mirror -/

/--
Cartan parity of a symmetry generator.

Compact generators are fixed by the Cartan involution. Noncompact generators
are negated by it.
-/
inductive CartanParity where
  | compact
  | noncompact
deriving DecidableEq, Repr

namespace CartanParity

/--
Mirror sign induced by Cartan parity.

Compact generators use `+`; noncompact generators use `-`.
-/
def mirrorSign : CartanParity → ℝ
  | compact => 1
  | noncompact => -1

@[simp]
theorem mirrorSign_compact :
    mirrorSign compact = 1 :=
  rfl

@[simp]
theorem mirrorSign_noncompact :
    mirrorSign noncompact = -1 :=
  rfl

end CartanParity

/-- Real bounded endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/--
Tomita-Cartan signed generator datum.

`localGen X` is the algebra-side generator, `mirror X` is the
Tomita-reflected commutant-side generator, and `parity X` records whether the
Cartan involution fixes or negates the generator.
-/
structure TomitaCartanGeneratorDatum
    (Gen H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  localGen : Gen → EndR H
  mirror : Gen → EndR H
  parity : Gen → CartanParity

/--
Signed global generator:

`Xhat = X + sign(X) * JXJ`.

This is the abstract form of compact `Khat = K + J K J` and noncompact
`Phat = P - J P J`.
-/
def globalGenerator
    {Gen H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : TomitaCartanGeneratorDatum Gen H)
    (X : Gen) : EndR H :=
  D.localGen X + (D.parity X).mirrorSign • D.mirror X

/-- Compact generators have symmetric Tomita doubling. -/
theorem globalGenerator_compact
    {Gen H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : TomitaCartanGeneratorDatum Gen H)
    (X : Gen)
    (hX : D.parity X = CartanParity.compact) :
    globalGenerator D X = D.localGen X + D.mirror X := by
  simp [globalGenerator, hX]

/-- Noncompact generators have antisymmetric Tomita doubling. -/
theorem globalGenerator_noncompact
    {Gen H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : TomitaCartanGeneratorDatum Gen H)
    (X : Gen)
    (hX : D.parity X = CartanParity.noncompact) :
    globalGenerator D X = D.localGen X - D.mirror X := by
  simp [globalGenerator, hX, sub_eq_add_neg]

/-! ## 3. Factor-center exclusion -/

/--
A factor-style algebra/commutant separation package.

The point is not to prove Tomita-Takesaki theory here. The point is to expose
the algebraic consequence needed downstream: if something lies in both the
algebra and the commutant, then it is scalar.
-/
structure FactorCenterExclusion
    (Op : Type*) [Ring Op] [SMul ℝ Op] where
  algebra : Set Op
  commutant : Set Op

  /-- `M ∩ M'` consists only of real scalar multiples of the identity. -/
  overlap_is_scalar :
    ∀ x : Op,
      x ∈ algebra →
      x ∈ commutant →
        ∃ r : ℝ, x = r • (1 : Op)

  /--
  Dynamic part/readout of an operator.

  This should kill scalars; concrete models may use commutator with a Dirac
  operator, quotient by scalars, traceless part, or another readout.
  -/
  dynamicPart : Op → Op

  /-- Scalars have zero dynamic part. -/
  dynamicPart_scalar_zero :
    ∀ r : ℝ, dynamicPart (r • (1 : Op)) = 0

namespace FactorCenterExclusion

variable
    {Op : Type*} [Ring Op] [SMul ℝ Op]

/-- Anything in both the algebra and its commutant has zero dynamic part. -/
theorem overlap_dynamicPart_zero
    (F : FactorCenterExclusion Op)
    {x : Op}
    (hxM : x ∈ F.algebra)
    (hxC : x ∈ F.commutant) :
    F.dynamicPart x = 0 := by
  rcases F.overlap_is_scalar x hxM hxC with ⟨r, hr⟩
  rw [hr]
  exact F.dynamicPart_scalar_zero r

end FactorCenterExclusion

/-! ## 4. Representation bridge to isotropic defects -/

/--
A bridge from center-collapse/dynamic collapse to the Krein isotropic cone.

This is intentionally separate. Trivial-center algebra alone does not imply
isotropy until a carrier readout and Krein form are supplied.
-/
structure CenterCollapseMapsToIsotropic
    (Op H : Type*)
    [Ring Op] [SMul ℝ Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : FactorCenterExclusion Op) where

  /-- Carrier readout of an operator. -/
  carrierReadout : Op → Doubled H

  /-- If the dynamic part vanishes, the carrier readout is isotropic. -/
  dynamic_zero_is_isotropic :
    ∀ x : Op,
      F.dynamicPart x = 0 →
        doubledKreinForm (carrierReadout x) (carrierReadout x) = 0

namespace CenterCollapseMapsToIsotropic

variable
    {Op H : Type*}
    [Ring Op] [SMul ℝ Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : FactorCenterExclusion Op}

/-- Overlap of algebra and commutant maps to an isotropic carrier vector. -/
theorem overlap_maps_to_isotropic
    (B : CenterCollapseMapsToIsotropic Op H F)
    {x : Op}
    (hxM : x ∈ F.algebra)
    (hxC : x ∈ F.commutant) :
    doubledKreinForm (B.carrierReadout x) (B.carrierReadout x) = 0 := by
  apply B.dynamic_zero_is_isotropic
  exact F.overlap_dynamicPart_zero hxM hxC

end CenterCollapseMapsToIsotropic

/-! ## 5. Mirror-involution Tomita-Cartan split datum -/

/--
A factor-style overlap condition.

This abstracts the statement `M ∩ M' = scalars`.  The predicate `isScalar`
identifies the scalar/central part of the ambient operator algebra.
-/
structure FactorOverlapDatum
    (Op : Type uOp) [Ring Op] where
  /-- Predicate for membership in the algebra. -/
  inAlgebra : Op → Prop

  /-- Predicate for membership in the commutant. -/
  inCommutant : Op → Prop

  /-- Predicate for scalar operators. -/
  isScalar : Op → Prop

  /-- The overlap of algebra and commutant is scalar. -/
  overlap_scalar :
    ∀ x : Op, inAlgebra x → inCommutant x → isScalar x

namespace FactorOverlapDatum

variable {Op : Type uOp} [Ring Op]
variable (F : FactorOverlapDatum Op)

/-- Any element in both the algebra and commutant is scalar. -/
theorem scalar_of_overlap
    {x : Op}
    (hM : F.inAlgebra x)
    (hC : F.inCommutant x) :
    F.isScalar x :=
  F.overlap_scalar x hM hC

end FactorOverlapDatum

/--
Tomita-Cartan split datum.

This records the mirror operation, the factor-overlap condition, and the
interpretive bridge from algebraic defects to a Krein isotropic cone.

The null-cone statement is deliberately a witness field.  It is not a theorem
of Tomita theory alone; it depends on the chosen Krein quadratic readout.
-/
structure TomitaCartanSplitDatum
    (Op Split H : Type*)
    [Ring Op]
    [AddCommGroup H] [Module ℝ H] where
  /-- Tomita mirror, morally `X ↦ J X J`. -/
  mirror : MirrorInvolution Op

  /-- Factor-style trivial center/overlap datum. -/
  factorOverlap : FactorOverlapDatum Op

  /-- Krein quadratic form on the carrier. -/
  kreinQuadratic :
    InfoGeometry.Geometry.KreinIsotropicCone.KreinQuadraticDatum H

  /-- Representation-level defect-to-isotropic bridge. -/
  defectToIsotropic :
    InfoGeometry.Geometry.KreinIsotropicCone.DefectMapsToIsotropic
      Split H kreinQuadratic


namespace TomitaCartanSplitDatum

variable {Op Split H : Type*}
variable [Ring Op]
variable [AddCommGroup H] [Module ℝ H]
variable (T : TomitaCartanSplitDatum Op Split H)

/-- Compact lifts are mirror-even in the Tomita-Cartan datum. -/
theorem compact_lift_even
    (x : Op) :
    T.mirror.mirror (T.mirror.compactLift x) =
      T.mirror.compactLift x :=
  T.mirror.mirror_compactLift x

/-- Noncompact lifts are mirror-odd in the Tomita-Cartan datum. -/
theorem noncompact_lift_odd
    (x : Op) :
    T.mirror.mirror (T.mirror.noncompactLift x) =
      -T.mirror.noncompactLift x :=
  T.mirror.mirror_noncompactLift x

/-- An algebra/commutant overlap element is scalar. -/
theorem overlap_is_scalar
    {x : Op}
    (hM : T.factorOverlap.inAlgebra x)
    (hC : T.factorOverlap.inCommutant x) :
    T.factorOverlap.isScalar x :=
  T.factorOverlap.scalar_of_overlap hM hC

/-- A represented defect maps to the carrier isotropic cone. -/
theorem defect_maps_to_isotropic
    {a : Split}
    (ha : a ∈ T.defectToIsotropic.defectLocus) :
    T.defectToIsotropic.carrierReadout a ∈
      InfoGeometry.Geometry.KreinIsotropicCone.IsotropicCone T.kreinQuadratic :=
  T.defectToIsotropic.defect_mem_isotropic ha

end TomitaCartanSplitDatum

/--
Owner target for constructing a mirror-involution Tomita-Cartan split model.

Concrete QFT/operator-algebra modules should supply the Tomita mirror, the
factor overlap theorem, and the Krein defect-to-null readout.
-/
def TomitaCartanSplitModelOwnerTarget
    (Op Split H : Type*)
    [Ring Op]
    [AddCommGroup H] [Module ℝ H] : Prop :=
  ∀ T : TomitaCartanSplitDatum Op Split H,
    (∀ x : Op,
      T.mirror.mirror (T.mirror.compactLift x) =
        T.mirror.compactLift x) ∧
    (∀ x : Op,
      T.mirror.mirror (T.mirror.noncompactLift x) =
        -T.mirror.noncompactLift x) ∧
    (∀ x : Op,
      T.factorOverlap.inAlgebra x →
        T.factorOverlap.inCommutant x →
          T.factorOverlap.isScalar x) ∧
    (∀ a : Split,
      a ∈ T.defectToIsotropic.defectLocus →
        T.defectToIsotropic.carrierReadout a ∈
          InfoGeometry.Geometry.KreinIsotropicCone.IsotropicCone T.kreinQuadratic)

/-! ## 6. Concise Tomita/Drazin bridge sockets -/

/-- Abstract membership data for an algebra and its commutant. -/
structure AlgebraCommutantDatum
    (Op : Type uOp) [Ring Op] where
  algebra : Set Op
  commutant : Set Op
  center : Set Op

  center_eq_intersection :
    center = algebra ∩ commutant
  /-- Factor-like overlap datum identifying the scalar sector. -/
  factorOverlap : FactorOverlapDatum Op

namespace AlgebraCommutantDatum

variable {Op : Type uOp} [Ring Op]
variable (A : AlgebraCommutantDatum Op)

/-- Any central element is scalar, via the stored overlap witness. -/
theorem center_is_scalar
    {x : Op}
    (hAlg : ∀ y : Op, y ∈ A.algebra → A.factorOverlap.inAlgebra y)
    (hComm : ∀ y : Op, y ∈ A.commutant → A.factorOverlap.inCommutant y)
    (hx : x ∈ A.center) :
    A.factorOverlap.isScalar x := by
  have hx' : x ∈ A.algebra ∧ x ∈ A.commutant := by
    simpa [A.center_eq_intersection] using hx
  exact A.factorOverlap.scalar_of_overlap (hAlg x hx'.1) (hComm x hx'.2)

end AlgebraCommutantDatum

/--
Tomita mirror data.

In concrete von Neumann theory this is implemented by `x ↦ J x J`.
-/
abbrev TomitaMirror
    (Op : Type uOp) [Ring Op] : Type uOp :=
  MirrorInvolution Op

/-- Cartan sign of a generator. -/
inductive CartanKind where
  | compact
  | noncompact
deriving DecidableEq, Repr

/--
Cartan-routed generator.

Compact generators lift with a plus sign across the Tomita mirror. Noncompact
generators lift with a minus sign.
-/
structure CartanRoutedGenerator
    (Gen Op : Type*) [Add Op] [Neg Op] where
  gen : Gen
  left : Op
  rightMirror : Op
  kind : CartanKind

namespace CartanRoutedGenerator

/-- The formal routed lift of a generator. -/
def lift
    {Gen Op : Type*} [Add Op] [Neg Op]
    (X : CartanRoutedGenerator Gen Op) : Op :=
  match X.kind with
  | CartanKind.compact => X.left + X.rightMirror
  | CartanKind.noncompact => X.left + (-X.rightMirror)

end CartanRoutedGenerator

/--
Doubled Krein quadratic form.

This is the carrier-level source of the indefinite sign.
-/
structure DoubledKreinQuadratic
    (H : Type*) [Zero H] where
  q0 : H → ℝ

namespace DoubledKreinQuadratic

variable
    {H : Type*} [Zero H]
    (Q : DoubledKreinQuadratic H)

/-- Quadratic readout on doubled states. -/
def q
    (u : H × H) : ℝ :=
  Q.q0 u.1 - Q.q0 u.2

/-- The mirror-balanced diagonal sector is isotropic. -/
theorem diagonal_isotropic
    (v : H) :
    Q.q (v, v) = 0 := by
  dsimp [q]
  ring

end DoubledKreinQuadratic

/--
Bridge from Tomita overlap/mirror-balanced data to isotropic carrier data.

This is deliberately a bridge, not a definition.
-/
structure TomitaIsotropicBridge
    (Op H : Type*)
    [Ring Op]
    [SMul ℝ H] where
  algebraCommutant : AlgebraCommutantDatum Op
  mirror : TomitaMirror Op
  quadratic : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H

  carrierRep : Op → H

  overlap_maps_to_isotropic :
    ∀ x : Op,
      x ∈ algebraCommutant.algebra →
      x ∈ algebraCommutant.commutant →
        quadratic.IsNull (carrierRep x)

namespace TomitaIsotropicBridge

variable
    {Op H : Type*}
    [Ring Op]
    [SMul ℝ H]
    (B : TomitaIsotropicBridge Op H)

/-- Re-export the overlap-to-isotropic bridge theorem. -/
theorem overlap_isotropic
    {x : Op}
    (hM : x ∈ B.algebraCommutant.algebra)
    (hC : x ∈ B.algebraCommutant.commutant) :
    B.quadratic.IsNull (B.carrierRep x) :=
  B.overlap_maps_to_isotropic x hM hC

end TomitaIsotropicBridge

/-- Bridge from Tomita isotropic data to a represented Drazin nil branch. -/
structure TomitaDrazinBridge
    (Op : Type*) [Ring Op] where
  projectors : DrazinProjectorPair Op

  tomitaDefect : Set Op

  defect_maps_to_nilpotent :
    ∀ x : Op,
      x ∈ tomitaDefect →
        IsNilpotentElement x

  defect_supported_by_nil :
    ∀ x : Op,
      x ∈ tomitaDefect →
        IsLeftNilSupported projectors x

namespace TomitaDrazinBridge

variable {Op : Type*} [Ring Op]
variable (B : TomitaDrazinBridge Op)

/-- Re-export nilpotence of Tomita defects. -/
theorem defect_nilpotent
    {x : Op}
    (hx : x ∈ B.tomitaDefect) :
    IsNilpotentElement x :=
  B.defect_maps_to_nilpotent x hx

/-- Re-export nil-projector support of Tomita defects. -/
theorem defect_nil_supported
    {x : Op}
    (hx : x ∈ B.tomitaDefect) :
    IsLeftNilSupported B.projectors x :=
  B.defect_supported_by_nil x hx

end TomitaDrazinBridge

end InfoGeometry.OperatorAlgebra.TomitaCartanSplit

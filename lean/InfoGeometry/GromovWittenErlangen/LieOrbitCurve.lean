import Mathlib

/-!
# InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness

Theorem-safe witness surface for the Klein--Gromov synthesis:

* homogeneous/projective targets with torus-fixed sectors;
* one-dimensional torus-orbit curve edges;
* root/coroot degree labels;
* localization graph sectors for GW-style fixed-sector sums.

This module does not assert a full Gromov--Witten localization theorem. It
records explicit combinatorial/algebraic witness data used by later owner-level
constructions.
-/

noncomputable section

namespace InfoGeometry

namespace GromovWittenErlangen

/--
Root/coroot shadow of a homogeneous target.

For a homogeneous target `G/P`, `FixedLabel` should be read as the Weyl coset
indexing set `W / W_P` (for `P = B`, this is the full Weyl group), and
`CurveDegree` as the corresponding effective curve-degree type
(often an image of the coroot lattice, e.g. in `H₂(G/P,ℤ)`).
-/
structure HomogeneousRootShadow (G : Type*) where
  /-- Labels of torus-fixed sectors, typically `W / W_P`. Pinned to `Type` to avoid
      universe metavariables in `Nonempty (...)` owner props. -/
  FixedLabel  : Type
  /-- Root/coroot labels for one-dimensional torus-orbit closures. -/
  RootLabel   : Type
  /-- Effective curve-degree classes, e.g. coroot-lattice data mod parabolic classes. -/
  CurveDegree : Type
  /-- Map from root label to curve-degree class. -/
  rootDegree  : RootLabel → CurveDegree

/--
Witness that a target has a GKM/Lie-orbit curve skeleton.

`OrbitCurve x y` is the type of one-dimensional torus-orbit closures between
fixed labels `x` and `y`. For `G/B`, this includes the Schubert line sectors
governed by roots; for `G/P` this records the corresponding partial-flag
quotient.
-/
structure LieOrbitCurveWitness (G T Target : Type*) where
  /-- Root/coroot shadow for symmetry combinatorics. -/
  rootShadow : HomogeneousRootShadow G
  /-- Realization of fixed labels as fixed sectors in the target. -/
  fixedSector : rootShadow.FixedLabel → Target
  /-- One-dimensional torus-orbit sectors between fixed labels. -/
  OrbitCurve : rootShadow.FixedLabel → rootShadow.FixedLabel → Type
  /-- Root/coroot label of an orbit sector. -/
  orbitRoot : ∀ {x y : rootShadow.FixedLabel},
    OrbitCurve x y → rootShadow.RootLabel
  /-- Degree class carried by the orbit sector. -/
  orbitDegree : ∀ {x y : rootShadow.FixedLabel},
    OrbitCurve x y → rootShadow.CurveDegree
  /-- Degree is the root-degree attached to the orbit root label. -/
  orbitDegree_eq_rootDegree :
    ∀ {x y : rootShadow.FixedLabel} (C : OrbitCurve x y),
      orbitDegree C = rootShadow.rootDegree (orbitRoot C)

/-- Terminology alias for the GKM presentation of the same skeleton. -/
abbrev GKMOrbitCurveWitness (G T Target : Type*) :=
  LieOrbitCurveWitness G T Target

/--
Localization graph witness for fixed-sector contributions.

Vertices are fixed sectors; edges are orbit sectors between vertices.
-/
structure LocalizationGraphWitness (G T Target : Type*) where
  /-- Underlying orbit skeleton. -/
  orbitWitness : LieOrbitCurveWitness G T Target
  /-- Vertices of the localization graph. Pinned to `Type` for universe safety. -/
  Vertex : Type
  /-- Map from graph vertices to fixed labels. -/
  vertexLabel : Vertex → orbitWitness.rootShadow.FixedLabel
  /-- Edges of the localization graph. Pinned to `Type` for universe safety. -/
  Edge : Type
  /-- Edge source. -/
  source : Edge → Vertex
  /-- Edge target. -/
  target : Edge → Vertex
  /-- Edge orbit realization. -/
  edgeCurve :
    ∀ e : Edge,
      orbitWitness.OrbitCurve
        (vertexLabel (source e))
        (vertexLabel (target e))
  /-- Edge degree class. -/
  edgeDegree : Edge → orbitWitness.rootShadow.CurveDegree
  /-- Compatibility with orbit-degree. -/
  edgeDegree_eq :
    ∀ e : Edge,
      edgeDegree e = orbitWitness.orbitDegree (edgeCurve e)

/--
Minimal virtual-localization sector packet.

This records the fixed/edge-sector shape used by the localization sum; no
analytic/algebro-geometric localization theorem is asserted here.
-/
structure VirtualLocalizationOrbitPacket (G T Target Coeff : Type*) where
  graph : LocalizationGraphWitness G T Target
  /-- Vertex-sector contribution term. -/
  vertexContribution : graph.Vertex → Coeff
  /-- Edge-sector contribution term / inverse Euler denominator. -/
  edgeContribution : graph.Edge → Coeff

/--
Langlands-dual transport of orbit-curve degree labels.

This is the structural bridge only: coroot-like classes on the `G` side are
ported to dual root-like classes on the dual side.
-/
structure LanglandsDualCurveDegreeTransport
    (G LG : Type*)
    (shadowG : HomogeneousRootShadow G)
    (shadowLG : HomogeneousRootShadow LG) where
  /-- Transport: curve-degree on the `G` side to dual root labels. -/
  degreeToDualRoot : shadowG.CurveDegree → shadowLG.RootLabel
  /-- Optional transport: `G` roots to dual curve degrees. -/
  rootToDualDegree : shadowG.RootLabel → shadowLG.CurveDegree

/--
Langlands/Klein/Gromov packet that pairs an orbit skeleton with dual transport.
-/
structure LanglandsKleinGromovPacket (G LG T Target : Type*) where
  orbit : LieOrbitCurveWitness G T Target
  dualShadow : HomogeneousRootShadow LG
  dualTransport :
    LanglandsDualCurveDegreeTransport G LG orbit.rootShadow dualShadow

structure LanglandsDualOrbitCurveWitness {G T Target : Type*}
    (C : LieOrbitCurveWitness G T Target) where
  /-- Langlands-dual group type. Pinned to `Type` for universe safety. -/
  DualGroup : Type
  dualShadow : HomogeneousRootShadow DualGroup
  dualTransport :
    LanglandsDualCurveDegreeTransport G DualGroup C.rootShadow dualShadow

/--
Integrated Klein--Gromov packet used in downstream owner assembly.
-/
structure KleinGromovPacket (G T Target Coeff : Type*) where
  orbitCurves : LieOrbitCurveWitness G T Target
  localizationGraph : LocalizationGraphWitness G T Target
  dualTransport : LanglandsDualOrbitCurveWitness orbitCurves
  virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff

/--
Constructor for the integrated packet.
-/
def constructKleinGromovPacket
    {G T Target Coeff : Type*}
    (C : LieOrbitCurveWitness G T Target)
    (Γ : LocalizationGraphWitness G T Target)
    (D : LanglandsDualOrbitCurveWitness C)
    (V : VirtualLocalizationOrbitPacket G T Target Coeff) :
    KleinGromovPacket G T Target Coeff :=
  { orbitCurves := C
    localizationGraph := Γ
    dualTransport := D
    virtualLocalization := V }

end GromovWittenErlangen

end InfoGeometry

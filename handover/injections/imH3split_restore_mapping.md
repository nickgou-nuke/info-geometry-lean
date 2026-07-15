# imH3split restore mapping

Source
- URL: http://agt2.cie.uma.es/~loos/jordan/archive/imH3split/imH3split.pdf
- Local snapshot used in this session: `/tmp/imH3split.pdf`
- Title (from extracted text): "Computing the derivation Lie algebra of the quadratic Jordan algebra H3+Os,- at any characteristic"
- Authors: Pablo Alberca Bjerregaard, Cándido Martín González
- Date in extracted text: 2001-11-20

Why this source matters
- It is a credible external restore surface for the split-octonion / Albert / F4 lane.
- It discusses exactly the `H₃(O_s)` quadratic Jordan setting, Zorn-matrix split octonions, McCrimmon equations, and the derivation Lie algebra of that Jordan algebra.
- It is useful as recovery evidence for owner files dealing with:
  - concrete split-Albert carriers;
  - split-octonion Jordan products / adjoints / cubic norms;
  - F4 / derivation-algebra readback surfaces;
  - boundary files that currently overclaim or have been depleted.

Extracted content anchors from the PDF
- Uses Zorn matrices for split octonions with scalar product and cross product on `F^3`.
- Defines `H₃(O_s)` as Hermitian `3×3` matrices over split octonions.
- Uses the `tri(a,b,c) := a (b c)` pattern in the McCrimmon equations.
- States the derivation Lie algebra `f4(O_s,-)` is 52-dimensional.
- Emphasizes no characteristic restriction in the computational environment.

Mapped maintained owner surfaces in this repo

1. Concrete split-Albert owner
- File: `lean/InfoGeometry/Canonical/SplitAlbert.lean`
- Namespace: `SplitAlbert`
- Current role:
  - theorem-first canonical owner for the split-Albert route;
  - concrete `27`-dimensional carrier;
  - trace / cubic norm / adjoint / trilinear polarization;
  - explicitly does **not** claim full octonionic Hermitian multiplication.
- Mapping to PDF:
  - strongest canonical owner analogue of the paper's `H₃(O_s)` lane;
  - already exposes the `27`-dimensional carrier and cubic-Jordan datum needed for the Freudenthal route.
- Restore implication:
  - if archive/chat fragments mention `H₃(O_s)` or split Albert dimension/cubic data, they should be mapped here first.

2. Concrete split-octonion Albert matrix carrier
- File: `lean/InfoGeometry/Algebra/CubicJordanOs.lean`
- Namespace: `CubicJordanOs`
- Current role:
  - concrete `AlbertMatrix` carrier with diagonal real coordinates and `SplitOct` off-diagonals;
  - defines `traceBilin`, `normCubic`, `adjointQuad`;
  - contains partial concrete Freudenthal identity lanes.
- Mapping to PDF:
  - closest repo-local concrete analogue to the paper's Hermitian `3×3` split-octonion matrices;
  - already uses Zorn split octonion operations and cubic/adjoint formulas.
- Restore implication:
  - if the paper is used to recover explicit `H₃(O_s)` formulas, this is the first owner file to compare against.

3. Split-octonion multiplication owner
- File: `lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean`
- Namespace root opened by `CubicJordanOs`
- Current role:
  - concrete split-octonion operations (`mulZ`, `conjZ`, `detZ`, etc.).
- Mapping to PDF:
  - matches the paper's Zorn-matrix lane and the split-octonion composition formulas.
- Restore implication:
  - any recovered multiplication/conjugation/norm identities from the paper must be checked here before being propagated upward.

4. Exact derivation / G2 certificate lane
- File: `lean/InfoGeometry/Lie/RealSplitOctonionG2Classification.lean`
- Namespace: `RealSplitOctonionG2Classification`
- Current role:
  - exact CA readback for the split-octonion derivation algebra;
  - records dimension `14` and Dmodules root-chart checks;
  - explicitly keeps finite `G₂(2)` separate from real split `G_{2(2)}`.
- Mapping to PDF:
  - related but not identical: the PDF focuses on derivations of the split-Albert/Jordan `H₃(O_s)` lane (F4, dimension `52`), while this file is the split-octonion derivation lane (G2, dimension `14`).
- Restore implication:
  - do **not** merge these surfaces;
  - the PDF is evidence for a missing or depleted F4/Jordan-derivation owner lane, not for changing the current G2 classification owner.

5. Abstract Freudenthal / cubic Jordan datum lane
- File: `lean/InfoGeometry/Exceptional/Freudenthal.lean`
- Current role:
  - abstract `CubicJordanDatum` owner surface.
- Mapping to PDF:
  - the paper's quadratic Jordan structure is external evidence for a concrete instance feeding this abstract route.
- Restore implication:
  - recovered `H₃(O_s)` structure should feed a truthful concrete datum / bridge, not bypass the current abstract owner.

What the PDF does NOT authorize by itself
- It does not justify identifying the repo's split-octonion G2 derivation owner with an Albert/F4 owner.
- It does not justify replacing theorem-honest current owners with external prose.
- It does not justify claiming a native Lean proof of the full Albert/F4 derivation theorem.
- It does not justify touching pinned Lean deps/toolchain/cache surfaces.

Concrete restore opportunities suggested by this source

A. F4 / split-Albert derivation packet inventory
- Search archive/chat/memory fragments for depleted references to:
  - `F4`
  - `52-dimensional`
  - `H₃(O_s)` / `H3+Os`
  - `McCrimmon`
  - `tri(a,b,c)`
  - derivations of the split Albert / Jordan lane
- Likely owner targets:
  - `lean/InfoGeometry/Canonical/SplitAlbert.lean`
  - `lean/InfoGeometry/Algebra/CubicJordanOs.lean`
  - bridge files mentioning Albert / Freudenthal / F4.

B. Concrete formula comparison against `CubicJordanOs`
- Compare the paper's:
  - Hermitian `3×3` layout,
  - cubic norm terms,
  - adjoint / triple-product formulas,
  - `tri(a,b,c)` usage,
  against the current `AlbertMatrix`, `normCubic`, and `adjointQuad` definitions.
- Goal:
  - detect whether rogue-agent depletion removed concrete identities that used to sit above this owner.

C. Missing F4 owner/bridge surface
- The repo currently has a clean G2 exact-certificate lane, but this PDF suggests a distinct restore lane around the split-Albert derivation algebra (`52`-dimensional F4).
- If archive fragments exist for this lane, they should become either:
  - a new theorem-honest readback/certificate owner for the F4 Jordan-derivation packet, or
  - a bridge file from `CubicJordanOs` / `SplitAlbert` into an explicitly external exact-CA packet.

Immediate next search terms for the restore loop
- `McCrimmon`
- `tri(`
- `52-dimensional`
- `H3+Os`
- `H₃(O_s)`
- `split Albert`
- `derivation Lie algebra`
- `f4`

Session notes
- Direct Firecrawl PDF extraction failed for billing reasons in this session.
- The PDF was successfully downloaded directly and text-extracted locally.
- This note is evidence inventory only; no theorem claims are promoted from it without current owner integration and verification.

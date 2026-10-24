# Motion v8: abstract the tower before elaborating the bundled hom

New source-only sandbox. No builds, owner edits, budget increases, transparency
changes or new mathematical premises. All previous candidates are preserved.

## Evidence and diagnosis

Read full v7 and terminal /tmp/qa-a-seedfinitefirstmotion20261024v7-i_bwoxv0/compile.log.
The first error is 58:9 whnf at 1M, in the binder
`f : MatrixStage k →⋆ₐ[ℂ] representedCStarClosure CStarMatrixStage ... ω`.
The body has not been reached. The second maxErrors diagnostic at105 is not
independent evidence of a later mathematical failure. Unlike v6, this is not a
reported synthInstance SeminormedRing timeout. It does not justify another
stack of inherited instances. The terminal log contains no profiler identifying
a unique expanded definition, so the exact expensive reduction is not certified.

Source-grounded reduction boundary:
- StarAlgHom (Mathlib Algebra/Star/StarAlgHom.lean:286) extends AlgHom and
  carries source/target semiring, algebra and star parameters.
- representedCStarClosure (native FilteredGNSRepresentedCStarClosure:47) is a
  StarSubalgebra defined as the topological closure of a represented range;
  its carrier and structures depend on GNSHilbertColimit Stage sys ω.
- Its CStarAlgebra instance (line56) is StarSubalgebra.cstarAlgebra, whose
  native inherited structures are built on that actual subtype.
- The native matrixGenerator/matrixRealTimeAut bind their hom over ABSTRACT
  I, Stage, sys and ω in FiniteSeedRepresentedRealTime. V7 had already fixed
  the concrete matrix stage family/system before elaborating this same binder.

## Targeted delta

Generalize only matrixStageAut_eq_finitePath over an abstract Type-level
I/Stage/sys/ω matching the native owner's construction boundary. Keep its
finite source MatrixStage k and finite CStarMatrix path. Delete the six local
projection instances in that generic helper section; use the native instance
as the native matrixRealTimeAut owner does. No additional instance is added.
Pass CStarMatrixStage/cstarMatrixInductiveSystem at the existing seed call.
The seed-section inherited projections and remaining proof bodies are unchanged.

This prevents concrete matrix tower definitions from being substituted while
elaborating the generic bundled-hom binder. It does not guarantee that the
later concrete specialization is cheap; that boundary is explicitly pending QA.
The intended test is whether the first failure moves beyond this binder, then
whether the actual seed readback and final theorem elaborate within unchanged
1M maxHeartbeats / 500k synthInstance limits. No performance success is claimed.

## Preserved actual conclusion and dependencies

For EVERY β:ℝ and h:ℝ with h≠0, some real t moves the ACTUAL represented switch
under native seedRealTimeAut for seed H=h•tilt2 and its native Gibbs family.
No chosen replacement state/flow, no faithfulness hypothesis, no presumed
naturality. FiniteExponentialMotion supplies the finite witness and map law;
native FiniteSeedRepresentationFaithfulness supplies actual seed injectivity;
accepted scratch action-alignment v2 supplies the whole-action application bridge.
The final tiltSeed_exists_realTime_move statement and proof are unchanged.

Source SHA256 read:
- v7: 627c6e68b604071cf0d0e2dea4fbbc43131de9222120ddfb3448703b1513f661
- FiniteSeedRepresentedRealTime: de19e22b0619c2d9a743dac42355971c4223c27bff1135862232e
- FilteredGNSRepresentedCStarClosure: c37c36415bffda27c186dee09d6ac00af2224cd5c2db6adda07c574d2ded12f9
- FiniteExponentialMotion: 93f2c6b5af7f729693d1aac9eb574d4109c270042993167906525982426a4541
- FiniteSeedRepresentationFaithfulness: eff6a9847572d55866cfba5fae4474a4c651b84df6f9137fdf05c1527437e2b0

Uncompiled G-A candidate requiring separate AA and serial QA; no self-AA claim.

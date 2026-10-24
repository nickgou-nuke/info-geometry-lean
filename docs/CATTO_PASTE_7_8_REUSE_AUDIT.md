# Paste 7 / 8: source audit and owner reuse

## Scope and verification boundary

Inputs read in full: `/home/goutev/.hermes/pastes/paste_7_082303.txt` and
`/home/goutev/.hermes/pastes/paste_8_082736.txt`.

The source findings below are not a fresh kernel receipt. The revised standalone
readout has NOT yet been compiled. A bounded preflight waited for other compiler
and test processes, then exited 75 because another pytest process remained active.
Log: `/home/goutev/.hermes/cache/scratch/catto_reuse_build.log`.
The earlier standalone build is not verification of this revision.

## Structural reuse applied

`lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicStandalone.lean` no longer
defines its own Vec3, split-octonion record, or multiplication. Its carrier is an
abbreviation for `InfoGeometry.Algebra.ZornVectorMatrix ℤ`; operations come from
the existing owners and the nonassociative instance in ZornDerivationBridge.

The multiplication-table statement and its historical namespace are retained.
Its proof now uses existing singlet, absorption, cyclic-product, and mixed-table
lemmas instead of recomputing a duplicated integer algebra with `decide`.
The old record constructor/Vec3 API is intentionally not retained; content search
found no external Lean usages of this module's namespace or table declaration.

Convention is preserved: u0=E11, u0Star=E22, u=-U, uStar=V. This exchanges the two
families and singlets relative to Canonical.GunaydinGursey, whose convention is
uZero=E22, uStarZero=E11, u=V, uStar=-U. Operator claims in the pastes instead use
Q=L(U), C=-L(V). These conventions must not be silently identified.

## Existing source paths for the supplied claims

- `Algebra/ZornSignedCAR.lean`: `L_map_anticommutator_of_left_alternative`,
  `L_U_square_zero`, `L_negV_square_zero`, and the three signed CAR identities.
- `Algebra/ZornLeftGrading.lean`: `left_E11_apply`,
  `left_diagonal_difference_apply`, `left_E11_idempotent`,
  `left_diagonal_difference_involution`,
  `left_diagonal_difference_eq_two_projector_sub_one`,
  `left_E11_tangent_offDiagonal`.
- `Algebra/ZornLeftParity.lean`: `left_signed_mode_commutator_eq`,
  `left_three_mode_product`.
- `Algebra/ZornColorBilinears.lean`: `E_action_U`, `E_action_negV`,
  `E_commutator`, `E_commutes_left_E11`.
- `Algebra/ZornLeftMajorana.lean`: vector-parametric square and anticommutator
  identities; `leftMajorana_mode_product`, `leftMajorana_six_factor_product`,
  mode flips, commuting mode products, total squares and total anticommutation.
- `Algebra/ZornMajoranaRotations.lean`: rotation covariance of both signatures,
  projector commutation, and the mode-product involution theorem.
- `Algebra/ZornMajoranaColorAudit.lean`: existing axiom audit for this corridor.

All paths above are relative to `lean/InfoGeometry/`. Existing source supports
arbitrary commutative rings where stated; an integer-only replacement is not
needed for the general operator layer.

## Corrections to paste 7 and inherited claims in paste 8

1. The supplied projector P(a,v,w,b)=(0,v,0,b) is right multiplication by E22,
   not the native left projector. `ZornRightProjectionObstruction.lean` proves
   its tangent defect on E22 is U0 and proves non-tangency over the reals.
   The native positive projector is L(E11): (a,v,w,b) ↦ (a,v,0,0).
   Its grading is (a,v,-w,-b), not (-a,v,-w,b).
2. The mode-product grading in `ZornLeftParity.lean` is exactly L(E11-E22).
   Nonassociativity alone does not prohibit this left action from grading the
   six operators; the native anticommutation theorem explicitly proves it.
3. The raw CAR odd brackets are central. Bilinear gl(3) closure does not imply
   the claimed gl(3|1) identification. `ZornColorOddDerived.lean` proves
   `oddDerived_eq_scalar`; `ZornColorGL31Obstruction.lean` proves
   `not_faithful_gl31_with_CAR_odd`, with precise odd-image and bracket-preserving
   hypotheses over a nontrivial commutative ring.
4. Paste 8's valid Majorana relations already have native owners above, but its
   global grading/projector claims inherit paste 7's wrong coordinate projector.
   The rotation definition uses the DIFFERENCE of signature bivectors; the
   earlier prose mentioning their sum must not be treated as the same identity.
5. No Hilbert adjoint, unitarity, physical N=6 supersymmetry, or Grassmannian
   functor is established merely by these algebraic identities.

## Search and supplementary algebra

Content searches covered lean, external_refs, tools, scripts, and formalizations
for the submitted symbols and native equivalents. The default external_refs
search excludes ignored files; a broader filesystem pass timed out. Therefore
this report makes no exhaustive external-library absence claim. Graph/session
searches were not used as proof evidence.

Existing exact checker: `scripts/check_zorn_color_operator_closure.py` imports
`tools/sympy/split_octonion_multiplication.py`; its assertions cover signed CAR,
grading, color bilinears, Majorana identities, the wrong-projector counterexample,
and the distinction between CAR and standard gl(3|1) odd-derived ranks.
It was read but NOT rerun during this pass because verification is serialized
with the already-running test process. CAS remains supplementary, not kernel proof.

## Pending targeted verification

After other test/compiler jobs finish:

    python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Superalgebra.CattoGurseyOctonionicStandalone InfoGeometry.Algebra.ZornMajoranaColorAudit InfoGeometry.Algebra.ZornColorGL31Obstruction InfoGeometry.Algebra.ZornRightProjectionObstruction

Then, sequentially, run the existing CAS checker with an installed SymPy-capable
interpreter. No dependency changes, umbrella build, commit, or push are part of
this audit pass.

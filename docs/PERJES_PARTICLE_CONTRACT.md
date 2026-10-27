# Perjes particle geometry and Klein glide transport

Source: Z. Perjes, *Introduction to Twistor Particle Theory*, KFKI-1980-76 (1980), sections 2--6. The Klein/Mobius extension is a separate user-requested construction, not a claim made by that report.

## Provenance and starting point

Base: PR #228, `d6d7a86cf5cadef212082e879605390f0fafaea8`, itself based on main `b143075bbf27e75860a1011e04423a0f227b7c41`. This branch is stacked; it does not silently treat PR #228 as merged. `PenroseIncidence`, `PenroseTwistor`, `SpinorOuterProduct`, `PenrosePolynomialCCR`, `InfinityTwistor`, `KleinBrillouinBase`, `KleinBottleOrbitQuotient`, and their actual source definitions are the starting owners. Existing carrier types and theorem names are retained. No dependency-pin update is authorized or performed.

## Ground-truth contracts (implementation targets, not proof certificates)

1. `PerjesConventions`: the existing `Twistor4 = Spinor2 × Spinor2`, its `omega = +i X pi` incidence, a sign adapter for the paper's `-i` convention, the off-diagonal Hermitian form and an explicit invertible conversion to the existing diagonal (2,2) form. Keep the factor of two in physical helicity explicit. Keep the paper's `1/sqrt(2)` Pauli normalization explicit.
2. `TwistorKinematicTensor`: construct the symmetric contravariant kinematic tensor in equation (6.4), and its momentum and angular-spinor blocks. Construct the upper infinity bivector as a dual-to-vector map, not as an inverse of the degenerate lower infinity form. Prove symmetry, phase invariance and block readbacks. Distinguish this tensor from the alternating Plucker bivector.
3. `TwistorConstituentKinematics`: construct total momentum and total kinematic tensor for a finite family of the same twistors. Reuse `SpinorOuterProduct.det_sum_self_outer` rather than duplicating its proof. Derive nonnegative mass-square and nondegeneracy criteria with the declared normalization.
4. `TwistorConstituentCCR`: actual multiplication and partial-derivative operators on `MvPolynomial (Fin n × Fin 4) ℂ`; derive diagonal and cross-constituent CCR. Do not use finite square matrices to realize a nonzero central CCR. Connect the single-constituent operations to the existing polynomial owner.
5. `PerjesNullLineCorrespondence`: use actual matrix kernels/incidence fibers, not surrogate predicates. Separate the complex affine incidence plane from its Hermitian real locus. A real null ray uses an explicit future-positive outer product.
6. Homogeneous/Cech/transform layer: use actual local sections, restriction maps and native linear quotients. Prove descent from cogauges, rather than storing the desired correspondence as a structure field. An algebraic Laurent/residue calculation must be labelled algebraic; it is not by itself the analytic Penrose transform or the positive-frequency theorem. Any analytic contour result must declare its domain, integrability and derivative hypotheses.
7. `TwistorInternalSymmetry`: prove invariance for actual constituent transformations. Unitary mixing alone is only part of equation (6.14); its skew-complex shift is a separate target. Do not infer the historical particle-classification proposals from an invariant.
8. Klein/Mobius transport: reuse `KleinBrillouinBase.glide (x,y) = (x+pi,-y)`, `glide_sq`, `glide_conj_ty`, and the actual torus orbit quotient. On the universal cover, a glide squares to longitudinal translation, while it inverts the *transverse* translation. A chosen pinorial lift has a separately declared and proved fiber square. Orientation reversal, a central minus sign, and a 2pi spin rotation are distinct constructions until an intertwiner proves otherwise. Do not impose a Pin-minus lift squaring to -1 as an involutive action on an ordinary periodic product torus: its double-cover boundary condition must retain the sign.

## Search and mathematical boundary

Live source confirms the existing `Physics.Pin.IsPinGlide` theorem assumes `R*T = T^-1*R`; it is a reversed-translation product, not the commuting axial translation of a geometric glide. Preserve its valid algebraic theorem and correct its scope in documentation. The existing orbit-quotient and two-sheeted-covering owners are reused rather than recreated.

The Perjes paper does not establish that a Klein bottle universally explains physical spin. The extension is a precise model of equivariant spinor/pinor transport. Likewise, the positive-frequency condition, a global Penrose cohomology isomorphism, Hilbert-space adjoints of polynomial CCR, shock-wave dynamics and internal-group classification require their own theorems. No such results may be reported solely from names, comments, assumptions or Boolean certificates.

## Verification

Status at initial commit: implementation in progress; no new kernel verification claimed. A scoped checker must record exact source hashes, Lean/Mathlib revisions, compiled import closure, warnings and transitive axiom audit. It must not conflate a scoped source check with a root-package build. The unchanged repository dependency pins remain protected.

# Perjes particle theory and Klein spinor descent: theorem contract

Base: PR #228, commit d6d7a86cf5cadef212082e879605390f0fafaea8.
Source: Z. Perjes, Introduction to Twistor Particle Theory, KFKI-1980-76,
printed pp. 5-18 (PDF pp. 9-22). The Klein glide extension is a separate
repository-motivated construction, not a claim found in that report.

## Source owners to reuse

- PenroseIncidence: Spinor2, Twistor4, ComplexSpacetime, incidenceLinearMap.
  Its incidence sign is +i, whereas the report uses -i.
- PenroseTwistor: diagonal signature-(2,2) Hermitian form and helicity readout.
- InfinityTwistor (PR #228): alternating covariant infinity form, radical.
  The contravariant infinity bivector is not its inverse.
- SpinorOuterProduct.det_sum_self_outer: determinant of two Hermitian dyads.
- PenrosePolynomialCCR: actual polynomial multiplication/differentiation CCR.
- Cl11Matrix: native Clifford algebra equivalence and Eminus^2 = -1.
- KleinBrillouinBase: actual affine covering glide and transverse translation.
- KleinPresentedGroup: the presented group and universal representation.

## Claims and conventions

1. Construct the incidence-sign adapter and a Witt-to-diagonal complex-linear
   equivalence, retaining its factor two. Physical helicity is one half of the
   Witt self-pairing. Projective sign invariance is not numerical helicity invariance.
2. Construct the actual symmetric kinematic tensor Z sym (I-sharp conjugate Z),
   its momentum/angular blocks, phase covariance and constituent sum.
3. Derive constituent CCR and quadratic generator commutators in native
   MvPolynomial endomorphisms. No Hilbert adjoint is inferred from a name.
4. Real null incidence: construct a Hermitian solution and characterize its
   affine null-line fibre. Complex incidence fibres remain distinct.
5. Implement unitary constituent mixing and skew nilpotent shifts; prove actual
   kinematic invariance. No group classification is supplied as a field.
6. Construct the two-chart finite-Laurent Cech quotient for O(-n-2), prove its
   coefficient/residue model, and connect finite Laurent representatives to
   genuine circle integrals. This is not the global analytic Penrose theorem.
7. Construct a specific Clifford/Pin lift of the existing affine Klein glide.
   Its square, the affine glide square, its projective action, and the induced
   bilinear action are separate theorems. The lift's central sign is explicit,
   not a consequence of nonorientability alone. A split-signature Pin lift is
   not silently identified with either Euclidean Pin convention.

## Validation

Pinned dependency metadata and toolchain remain unchanged. Scoped validation
must compile the exact transitive source closure and audit every owned kernel
declaration. It is not a root-package build. Missing analytic completeness,
full internal-group classification, a positive-frequency Hilbert completion,
and a curved-spacetime scattering construction must remain explicitly recorded.

# Reflexive flow / Klein representation completion contract

## Inspected current source

`Canonical/ReflexiveNilpotentFlows.lean` now contains the associative-ring
three-shear factorization, Weyl unit/inverse, fourth power, support exchange,
negative-CAR normalization, diagonal multiplication/scaling and rotor laws.
`ReflexiveFlowUnits.lean` already constructs `diagonalUnitsHom : Rˣ →* Aˣ`
and its inverse-conjugation law. `ReflexiveKleinRepresentation.lean` already
uses `KleinPresentedGroup.kleinRep` to construct `reflexiveKleinRep` and proves
that the fourth power of the glide generator maps to one. These recent shared
owner additions will be preserved, not duplicated or attributed to this task.
`SuperMetriplectic/WittKleinRepresentation.lean` instantiates that representation
on the existing neutral Witt matrices and ket-bra soldering carrier.

## Precise completion

For `[CommRing R] [Ring A] [Algebra R A]`, square-zero d,B satisfying
d*B*d=d and B*d*B=B:

1. Reuse the concurrently added `ReflexiveParabolicUnits.parabolicUnitsHom`
   (in namespace `ReflexiveNilpotentFlows`), a native homomorphism
   `Multiplicative R →* Aˣ`. Its implementation belongs to the shared owner,
   not this task. Repair downstream calls after the reduced-hypothesis
   `weylUnit hd hB hr` constructor.
2. Reuse the existing semidirect-product realization of the presented Klein
   group to show that every nonzero integer power of its glide is nonidentity.
3. Consequently prove that every `reflexiveKleinRep` is noninjective: its
   glide-fourth-power kernel element is genuinely nonidentity. This makes the
   boundary between an algebraic representation and a faithful deck action
   explicit, rather than merely withholding a faithfulness assertion.
4. Supply a noncommuting rational matrix specialization with distinct inverse
   diagonal parameters, and verify the actual generator images.
5. Integrate and strictly replay the affected owner chain, preserving valid
   signatures and checking source drift in this shared checkout.
6. Latest intake: correct the false Jordan bracket order in the concurrently
   added `UnifiedGeometryOperatorSignificance.lean`, including its master
   theorem and registered claim. Reuse `Core/JordanAssociatorRing` rather than
   reproving this identity. Replace overstated module documentation with the
   precise algebraic scope; retain historical names for compatibility.
   The correction intentionally changes the false theorem statement.
7. Add exact rational counterexamples to the reversed Jordan bracket and to
   the claim that square-zero localization annihilates all Jordan associators.

## Owners and exact connecting facts

- `weyl_factorization`: `(1+d)*(1-B)*(1+d)=complement d B+(d-B)`.
- `diagonalUnitsHom` and `weylUnit_conjugates_diagonalUnitsHom`: conjugation
  sends parameter t to its inverse, not the infinitesimal grading to its inverse.
- `reflexiveKleinRep_genA_fourth`: rho(a^4)=1.
- `KleinNativeSemidirectProductBridge.nativeKleinPresentationRep_generators`:
  a maps to `SemidirectProduct.inr (Multiplicative.ofAdd 1)`; the native right
  projection therefore reads its integer exponent.
- `KleinPresentedGroup` is an algebraic group presentation. Its own source
  does not identify it with a topological fundamental group.

## Search and exclusions

Searched repo-owned Lean for flow/Weyl/unit identities, Klein generator powers,
integer projections, winding maps, and current imports. Traced the actual
semidirect-product, free-group quotient and Witt implementation.
No global absence claim is made. No new law-bearing structure, duplicate Klein
presentation, octonion Ring instance, analytic exponential, loxodromic
classification, principal bundle, CPT, or global super-Grassmannian is claimed.
The ring operations remain noncommutative and the scalar ring arbitrary.

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ClassicalSimpleFamilyCatalog
public import InfoGeometry.Exceptional.CFSGPort.QuasisimpleTransport
public import InfoGeometry.Exceptional.CFSGPort.CoxeterMatsumoto.PositiveLift
public import InfoGeometry.Exceptional.CFSGPort.RankOneSimplicity
public import InfoGeometry.Exceptional.CFSGPort.TitsSimplicitySupport
public import InfoGeometry.Exceptional.CFSGPort.ReeG2SimplicityArithmetic
public import InfoGeometry.Exceptional.CFSGPort.CommutatorTorus
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootTorusSubgroup
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyBorelIntersection
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyNormalizerTriviality
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyProductInjectivity
public import InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne
public import InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOneBruhat
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyOperatorPolynomial
public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseCertificate
public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparsePolynomial
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorCertificate
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorFamily
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorGroup
public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseWeyl
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastWeylTables
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecks
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamily
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorValidity
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamilyData
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamilyBridge
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorMirror
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootHeightDescent
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyBraidWalk
public import InfoGeometry.Exceptional.CFSGPort.OperatorCurtisTitsDatum
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalModelSimplicity
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCartanHelpers
public import InfoGeometry.Exceptional.CFSGPort.PrimitiveCoprimeSimplicity
public import InfoGeometry.Exceptional.CFSGPort.J1GeneratorOrders
public import InfoGeometry.Exceptional.CFSGPort.SuzukiOvoid
public import InfoGeometry.Exceptional.CFSGPort.SuzukiOvoidKernel
public import InfoGeometry.Exceptional.CFSGPort.SuzukiBruhatFactorization
public import InfoGeometry.Exceptional.CFSGPort.SuzukiSimplicity

/-!
The root-project adaptation of exceptional finite Lie-type models and the
sporadic group carriers from `external_refs/CFSG`. This import exposes root
systems, pinned root groups, Weyl elements, torus actions, and model predicates
for G₂, F₄, D₄, E₆, E₇, E₈, ²E₆, ³D₄, ²B₂, ²G₂, ²F₄, and the Tits group,
along with classical PSL/PSU/PSp/PΩ models and all 26 sporadic carrier models.
`FiniteGroupModelCatalog` combines the cyclic, alternating, classical,
exceptional, and sporadic model families. The simple-family modules prove
simplicity for cyclic-prime and alternating-degree-at-least-five models, and
for the classical PSL₂ branch over fields of cardinality at least four. Other
model branches do not by themselves prove simplicity or the CFSG classification
theorem. The six untwisted exceptional adjoint root-group models also expose
source-level perfectness theorems over fields with at least three elements.
The operator rank-one carriers include their simple-root Weyl and torus
elements, proved containment of the torus in its rank-one group, and the
torus-normalizer action on pinned root subgroups. The simple Weyl operator
also exchanges the positive and negative pinned simple-root subgroups by
conjugation. Their alternating products satisfy the certified Coxeter braid
relations for types G₂, F₄, D₄, E₆, E₇, and E₈. The adjoint groups on these
root modules have explicit
noncommuting pairs of endomorphism units, obtained from the opposite-root
normalizer-triviality theorem. The generic rank-one
normal-core simplicity criterion is also ported, but no exceptional model has
yet been shown to satisfy all of its Bruhat, conjugation, and generation
hypotheses. Perfectness and the criterion therefore remain inputs rather than
unconditional simplicity proofs for these exceptional models. Separately, the
finite Suzuki upper-matrix operator group has a conditional simplicity theorem
assembled from its proved faithful two-transitive ovoid action, exact local
point-stabilizer recognition, solvable root–torus subgroup, and perfectness.
-/

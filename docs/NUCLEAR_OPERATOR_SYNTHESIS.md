# Canonical operator synthesis: five grades, parity, and ordered coefficients

## Source and status

Existing declarations are pinned to
[`00b41c37ad68b0dd24690be03ab8c714365ffb5f`](https://github.com/nickgou-nuke/info-geometry-lean/tree/00b41c37ad68b0dd24690be03ab8c714365ffb5f).
The six new owner modules below contain 45 explicit theorems and three
definitions. All compiled with Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete integration target
compiled a closure of 92 repository source files and checked 34 interfaces.
Independent acceptance checked every new declaration and 13 reused interfaces
(61 total); their transitive axiom union is exactly `propext`, `Quot.sound`,
and `Classical.choice`. The delivered verification records bind these results
to the exact source bytes. This is the checked integration scope.

This is a map of mathematical construction dependencies. It is not a complete
transitive import graph. Every carrier change is recorded explicitly.

## 1. Common-source matrix units to a tripotent and tetraktys

Let `A` be an associative ring with a star operation, `d b : ι → A`, and
`hS : IsSupercolorSystem d b`. Put

\[
E_{ij}=d_i b_j.
\]

The native `IsSupercolorSystem` supplies the individual Moore–Penrose laws,
the two square-zero families, and the unmatched-middle annihilation laws.
The **additional common-source hypothesis** is

\[
b_i d_i=q\quad\text{for all }i.
\]

Under this hypothesis the existing multiplication owner proves

\[
E_{ij}E_{\ell m}=\delta_{j\ell}E_{im},\qquad
[E_{ij},E_{\ell m}]=\delta_{j\ell}E_{im}-\delta_{mi}E_{\ell j}.
\]

The if-indexed multiplication interface uses decidable equality on `ι`.
The abstract two-color construction does not require finitely many colors;
the concrete matrix examples and embedding use their stated finite-index
instances.

| Construction or law | Canonical source |
|---|---|
| `IsSupercolorSystem`, `colorBoson`, unmatched-middle products | [Core.SuperGrassmannianSusy][susy] |
| `coexact_absorption_iff_equal`, `colorBoson_mul_of_common_source`, `colorBoson_lieBracket_of_common_source` | [Core.SupercolorMultiplication][color-mul] |
| Ordered source endpoint actions and `odd_pair_closure` | [Core.SupercolorSourceClosure][color-source] |
| Concrete common-source matrices indexed by `Option ι`, `matrix_supercolor`, `colorBoson_eq_single`, `colorBoson_mul` | [Core.SupercolorMatrixExamples][color-examples] |
| Actual injective nonunital `colorEmbeddingHom`, `colorEmbedding_single`, and commutator preservation | [Core.SupercolorMatrixUnitBridge][color-embedding] |

The common-source `Option ι` representation retains off-diagonal color matrix
units. The separately owned `ι × Bool` orthogonal-sector example has different
cross-color products; the common-source and fully orthogonal hypotheses must
be applied according to their actual theorem types.

For distinct colors `i ≠ j`, choose

\[
p=E_{ii},\quad r=E_{jj},\quad T=p-r,
\quad u=E_{ij},\quad v=E_{ji}.
\]

The diagonal idempotence and orthogonality imply

\[
T^3=T,\qquad T^2=p+r.
\]

These facts reuse
`orthogonal_idempotents_color_tripotent` from
[PeirceSpine.TripotentDefect][tripotent-defect]; its zero-projector readout is
`triProj0 (colorTripotent p r) = colorBlue p r = 1-p-r`.

The matching-middle products use the common source:

\[
uv=p,\quad vu=r,\quad
\Phi=u+v,\quad J=u-v,\quad
V=uv+vu=p+r,\quad\Sigma=uv-vu=p-r=T.
\]

These are elements of the original ring `A`; `V` is the two-color support
operator and is not normalized to the ambient identity. The existing
[PeirceSpine.Basic][peirce-basic] and [PeirceSpine.Tetraktys][tetraktys]
owners provide the canonical `conePlus`, `coneMinus`, `genPhi`, `genJ`, `genV`,
and `genSig` constructions. In particular,

\[
\Phi^2=V,\qquad J^2=-V,\qquad
J\Phi=\Sigma,\qquad\Phi J=-\Sigma,\qquad\Sigma^2=V^2.
\]

The new `SupercolorTripotentParity` adapter connects the native `colorBoson`
expressions to those existing Peirce corners and then to the tripotent
projector/parity owners. Its exact declaration list is recorded in §7.

## 2. Tripotent projectors to full five-grade parity and tangent equations

For `A` an associative real algebra and `T*T*T=T`, the existing polynomial
projectors are

\[
p_+=\tfrac12(T^2+T),\qquad p_0=1-T^2,
\qquad p_-=\tfrac12(T^2-T).
\]

The existing [TripotentFiveGradingDecomposition][five-projectors] constructs
five linear projectors `fiveGradeProjector T k` on `A` by grouping the joint
corners `p_a X p_b` according to `a−b=k`. It proves idempotence, pairwise
orthogonality, recomposition, and a linear equivalence with the product of
their ranges. [Core.TripotentEigenspaces][five-eigenspaces] proves the exact
native eigenspace identification

\[
\operatorname{fiveGradeRange}(T,k)
=\ker(\operatorname{ad}_T-kI).
\]

The new `TripotentParity` reuses these projectors and the existing
[Core.PeirceGrading][peirce-grading] maps. Writing `π_k` for the five projectors,

\[
\begin{aligned}
\operatorname{odd}_{p_0}(X)&=\pi_{-1}(X)+\pi_{+1}(X),\\
\operatorname{even}_{p_0}(X)&=\pi_{-2}(X)+\pi_0(X)+\pi_{+2}(X),\\
\gamma_0&=2p_0-1=1-2T^2.
\end{aligned}
\]

The first two equations are polynomial identities without a tripotence
hypothesis. Tripotence then supplies `p₀²=p₀` and `γ₀²=1`. Conjugation by `γ₀`
acts on all native grade ranges with sign

| Grade | −2 | −1 | 0 | +1 | +2 |
|---|---:|---:|---:|---:|---:|
| `γ₀ X γ₀` | `X` | `−X` | `X` | `−X` | `X` |

The same owner proves the exact native tangent characterization

\[
p_0X+Xp_0=X
\quad\Longleftrightarrow\quad
\pi_{-1}(X)+\pi_{+1}(X)=X.
\]

This uses `IsGrassmannianTangent` from [Core.SuperGrassmannianSusy][susy], not a
separately introduced tangent predicate. The even sum commutes with `p₀`.
The ±2 corners connect the two nonzero spectral spaces, so they are even for
this zero-mode cut.

In the two-color construction of §1, `Eᵢⱼ` and `Eⱼᵢ` have adjoint grades
`+2` and `−2` for `T=Eᵢᵢ−Eⱼⱼ`. The existing
`colorTripotent_corner_charge` theorem records these charges. Thus those
operators are off-diagonal at the cut `Eᵢᵢ` but even at the different cut
`p₀=1−Eᵢᵢ−Eⱼⱼ`. The grade-±1 coefficients of §3 are the corners between the
zero and nonzero spectral spaces; their membership must come from the stated
range hypotheses or the native projector construction.

## 3. Five-grade membership to the operator block's total parity

The existing [NuclearOperatorSuperSoloviev][soloviev] defines, for an arbitrary
ring `A`,

\[
B=\begin{pmatrix}E_0&V\\W&E_1\end{pmatrix}
\in\operatorname{Matrix}_{2}(A).
\]

For an internal involution `Γ`, the existing
[NuclearInternalExternalParityFactorization][parity-factor] constructs

\[
I_\Gamma=\operatorname{diag}(\Gamma,\Gamma),\quad
F=\operatorname{diag}(1,-1),\quad
\Pi=I_\Gamma F=F I_\Gamma=\operatorname{diag}(\Gamma,-\Gamma).
\]

The old theorem `invariant_of_even_diagonal_odd_offDiagonal` proves `ΠBΠ=B`
from internally even diagonal entries and internally odd off-diagonal
entries. The existing [NuclearSuperSolovievPeirceBridge][soloviev-five]
records compatible blocks using native grade-zero and grade-±1 membership.

The new `NuclearFiveGradeParity` **derives** the needed signs by choosing
`Γ=γ₀=invS (projZero T)`:

\[
E_0,E_1\in\mathfrak g_0,\quad V\in\mathfrak g_{+1},\quad
W\in\mathfrak g_{-1}
\quad\Longrightarrow\quad\Pi B\Pi=B.
\]

`totalParity_invariant_projected_block` constructs such a block from arbitrary
inputs by replacing its entries with `π₀ E₀`, `π₀ E₁`, `π₊₁ V`, `π₋₁ W`.
`PeirceCompatibleBlock.totalParity_invariant` adds the resulting theorem to
the existing compatible-block interface without adding a symmetry field.

The carrier change in this branch is explicit: five-grade operators lie in
`A`; the resulting block lies in `Matrix (Fin 2) (Fin 2) A`.

## 4. Signed RPA blocks retain ordered products

The new `OperatorRPABlock` reuses the same native `blockHamiltonian` over an
arbitrary ring. With

\[
M=\begin{pmatrix}a&b\\-b&-a\end{pmatrix},\quad
K=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
R=\begin{pmatrix}0&a-b\\a+b&0\end{pmatrix},
\]

its dependency chain is

\[
K^2=2I,\quad KM=RK
\quad\Longrightarrow\quad KMK=2R,\quad KM^2=R^2K.
\]

No inverse for `K` is used. The exact squares are

\[
M^2=\begin{pmatrix}a^2-b^2&[a,b]\\[a,b]&a^2-b^2\end{pmatrix},
\qquad
R^2=\begin{pmatrix}(a-b)(a+b)&0\\0&(a+b)(a-b)\end{pmatrix}.
\]

The ordered diagonal products expand to `a²−b²+[a,b]` and
`a²−b²−[a,b]`, respectively. `rpa_square_offDiagonal_eq_zero_iff` identifies
vanishing of the original off-diagonal square with `ab=ba`. The existing
external involution satisfies `FRF=−R` and `FR²F=R²`.

This branch is a construction on `Matrix₂(A)` from arbitrary `a,b : A`.
It does not require an identification of `a,b` with a particular compressed
matrix model.

## 5. Operator coefficients in the finite phonon sum

The native [NuclearPhononRPAAlgebra][phonon] supplies `PhononRPA ι A`, its
operators `Q_i`, `Qdag_i`, the exact commutation hypotheses, and
`numberOp i = Qdag_i * Q_i`.

The new `NuclearPhononOperatorWeights` keeps coefficients in that same ring:

\[
H_\Omega=\sum_{i\in s}\Omega_iN_i,\qquad\Omega_i\in A.
\]

`comm_operatorWeightedHamiltonian` proves the full ordered identity

\[
[H_\Omega,X]
=\sum_{i\in s}\bigl(\Omega_i[N_i,X]+[\Omega_i,X]N_i\bigr).
\]

Using the existing same-mode and distinct-mode commutator theorems gives, for
`k∈s`,

\[
[H_\Omega,Q_k^\dagger]
=\Omega_kQ_k^\dagger
+\sum_{i\in s}[\Omega_i,Q_k^\dagger]N_i.
\]

If `[N_i,X]=0` for every `i∈s`,
`operatorWeightedHamiltonian_commute_iff` characterizes exact commutation by

\[
[H_\Omega,X]=0
\quad\Longleftrightarrow\quad
\sum_{i\in s}[\Omega_i,X]N_i=0.
\]

The criterion allows cancellation in the sum. It does not demand that every
coefficient commute separately with `X`.

## 6. An external anticommuting involution and the native zero carrier

This branch uses `T Γ : Module.End ℝ V`, with the **explicit** intertwining law
`Γ*T=−(T*Γ)`. It is independent of the internally constructed `γ₀` above.
The new `TripotentChiralRestriction` proves

\[
\Gamma T^2=T^2\Gamma,\quad
\Gamma p_0=p_0\Gamma,\quad
\Gamma p_+=p_-\Gamma,\quad
\Gamma p_-=p_+\Gamma.
\]

These polynomial laws require only anticommutation. With `T³=T`, the existing
[TripotentInvariantCarrierBridge][horizon] identifies

\[
\operatorname{zeroModeCarrier}(T)=\ker T=\operatorname{range}(p_0)
\]

and provides the native `zeroModeRestriction`. With `Γ²=1`, the new owner
proves that this restriction squares to one and constructs

```lean
zeroModeChiralEquiv : zeroModeCarrier T ≃ₗ[ℝ] zeroModeCarrier T
```

whose underlying action is `x ↦ Γ x`. The separate existing
[ChiralEigenspaceEquivalence][chiral-spectral] already owns eigenvalue and
generalized-eigenvalue transport from `λ` to `−λ`.

Conjugation by `γ₀`, which commutes with `T`, gives the parity signs of §2.
An external `Γ` anticommuting with `T` exchanges its positive and negative
projectors. The two actions have different hypotheses and conclusions.

## 7. Six new owners and their immediate dependencies

| New module | Immediate canonical imports | Principal declarations |
|---|---|---|
| `OperatorAlgebra.PeirceSpine.TripotentParity` | `Core.PeirceGrading`; `Core.SuperGrassmannianSusy`; `PeirceSpine.Supercharge`; `Physics.Algebra.TripotentFiveGradingDecomposition` | `oddGrade_projZero`; `evenGrade_projZero`; `invS_projZero_sq`; `parityConj_projZero_of_mem_fiveGradeRange`; `isGrassmannianTangent_iff_oddGrades_fixed` |
| `OperatorAlgebra.PeirceSpine.SupercolorTripotentParity` | `Core.SupercolorMultiplication`; `PeirceSpine.TripotentDefect`; `PeirceSpine.TripotentParity` | `supercolor_tetraktys_corners`; `supercolor_colorTripotent_tripotent`; `supercolor_reverse_products`; `supercolor_tetraktys_mass`; `supercolor_tetraktys_spin`; `supercolor_colorTripotent_sq_eq_mass`; `supercolor_projZero_colorTripotent`; `supercolor_zero_reflection_eq_mass`; `supercolor_oddGrades_isGrassmannianTangent`; `supercolor_fiveGrade_parity` |
| `Core.TripotentChiralRestriction` (declaration namespace `Physics.Algebra`) | `Physics.Algebra.TripotentInvariantCarrierBridge` | `anticommute_commutes_square`; `anticommute_endProjZero`; `anticommute_endProjPos`; `anticommute_endProjNeg`; `zeroModeRestriction_sq_of_anticommute`; `zeroModeChiralEquiv` |
| `Physics.OperatorRPABlock` | `Physics.NuclearInternalExternalParityFactorization` | `rpa_square`; `rpa_square_offDiagonal_eq_zero_iff`; `hadamard_intertwines_rpa`; `chiral_rpa_square`; `ordered_rpa_products`; `hadamard_intertwines_rpa_square` |
| `Physics.NuclearPhononOperatorWeights` | `Physics.NuclearPhononRPAAlgebra` | `PhononRPA.operatorWeightedHamiltonian`; `comm_operatorWeightedHamiltonian`; `comm_operatorWeightedHamiltonian_Qdag`; `operatorWeightedHamiltonian_commute_iff` |
| `Physics.NuclearFiveGradeParity` | `PeirceSpine.TripotentParity`; `Physics.NuclearSuperSolovievPeirceBridge`; `Physics.NuclearInternalExternalParityFactorization` | `zeroModeInternalParity`; `totalParity_invariant_of_fiveGrade`; `totalParity_invariant_projected_block`; `PeirceCompatibleBlock.totalParity_invariant` |

The `SupercolorTripotentParity` source distinguishes the common-source
requirements: the two diagonal color idempotents already provide the
tripotent; the reverse products and tetraktys mass/spin identifications use
the additional common-source hypothesis. The imported owners and all ten
declarations above are included in the completed compilation and independent
acceptance. The final signatures record these hypotheses explicitly.

## 8. Existing operator observables and explicit carrier distinctions

| Carrier | Exact existing definitions and theorems | Source |
|---|---|---|
| An arbitrary associative algebra `A` | Square-zero-pair `V=uv+vu`, `Σ=uv−vu`; `mass_commute_left/right`, `mass_spin_squares_equal`; left multiplication `L_V` commutes with the relevant inner derivations | [SquareZeroPairSpectral.MassCommutant][mass] |
| `Module.End ℤ A` | `opposite_lie_comm`, `sigma_lie_mem_sector`, `plus_sandwich_mem_sector`, `minus_sandwich_mem_sector` | [PeirceSpine.CornerChargeSectors][charge-sectors] |
| `MatStage 5`, the five-mode real CAR matrix carrier | `e`, `f`, `H`; `isospinPlus/Minus/Cartan`; `pairingPlus/Minus/Cartan`; `five_graded_isospin_and_pairing_grades` | [Physics.Cl55SpinorCartanFock][cl55] |
| The same `MatStage 5` | `isospinCartan_projector_eigenvalues`; `isospinCasimir`; `pairingCasimir`; `casimir_partition_of_three_one` | [Physics.Cl55SpinorCartanFock][cl55] |
| The same `MatStage 5`, distinct modes | `gammaPlus n=e_n+f_n`, `gammaPlus_sq`, `pin_majorana_conjugates_isospin_to_pairing` | [Physics.Cl55SpinorCartanFock][cl55] |
| `M₂(ℂ) ⊗[ℂ] M₂(ℂ)` | `spinAction A=A⊗1`, `isospinAction B=1⊗B`, their noncommuting Pauli brackets, `spin_isospin_actions_commute`, distinct chirality involutions | [NuclearSpinIsospinTensorRepresentation][spin-isospin] |
| `Endℝ(ℕ → Fin 4 → NativeZorn)` | `representation` of the two-mode matrix algebra; `coefficientLift` of native Zorn endomorphisms; actual phonon shifts; `five_grade_common_representation_packet` | [NuclearFiveGradeCommonCarrierRepresentation][common-rep] |
| The same common carrier | `commonRepresentationLieHom : M4R →ₗ⁅ℝ⁆ Operator`; commutator and named grade preservation | [NuclearFiveGradeCommonCarrierLieHom][common-lie] |

The full operator Casimir equations for distinct modes are

\[
C_{\rm iso}=3\Delta_{\rm iso},\qquad
C_{\rm pair}=3\Delta_{\rm pair},\qquad
C_{\rm iso}+C_{\rm pair}=3I.
\]

The constructed Pin involution transports
`(isospinPlus, isospinMinus, isospinCartan)` to
`(−pairingPlus, −pairingMinus, pairingCartan)`. This is the exact existing
operator conjugation theorem; it is distinct from a general `k ↦ −k` grade
exchange. No equality of the complex tensor carrier, the five-mode matrix
carrier, and the common coefficient carrier is asserted by this map.

## 9. Verified integration

The complete entry point `tests/NuclearOperatorSynthesis.lean` imports the
six new owners and the existing owners whose interfaces it checks. All 34
checks passed. The following thirteen reused declarations are included in
that entry and in the independent axiom audit:

```lean
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.SupercolorTripotentParity
import InfoGeometry.Core.TripotentChiralRestriction
import InfoGeometry.Physics.OperatorRPABlock
import InfoGeometry.Physics.NuclearPhononOperatorWeights
import InfoGeometry.Physics.NuclearFiveGradeParity
import InfoGeometry.Core.SupercolorMatrixUnitBridge
import InfoGeometry.Core.SupercolorSourceClosure
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom

#check InfoGeometry.Core.SuperGrassmannianSusy.colorBoson_mul_of_common_source
#check InfoGeometry.Core.SupercolorMatrixUnitBridge.colorEmbeddingHom
#check InfoGeometry.Core.SupercolorMatrixUnitBridge.colorEmbedding_injective
#check InfoGeometry.Core.TripotentAdjoint.fiveGradeRange_eq_eigenspace
#check InfoGeometry.Physics.Algebra.zeroModeCommutantRestriction
#check InfoGeometry.Physics.NuclearOperatorSuperSoloviev.invariant_of_even_diagonal_odd_offDiagonal
#check InfoGeometry.Physics.NuclearInternalExternalParityFactorization.parity_factorization_packet
#check InfoGeometry.Physics.NuclearPhononRPA.PhononRPA.comm_numberOp_Qdag_same
#check InfoGeometry.Physics.Cl55SpinorCartanFock.five_graded_isospin_and_pairing_grades
#check InfoGeometry.Physics.Cl55SpinorCartanFock.casimir_partition_of_three_one
#check InfoGeometry.Physics.Cl55SpinorCartanFock.pin_majorana_conjugates_isospin_to_pairing
#check InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.spin_isospin_actions_commute
#check InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom.commonRepresentationLieHom
```

The standalone source package includes the complete import closure, its
source-import DAG and induced reachability partial order, the exact dependency
pins, and both independent acceptance logs. Each accepted declaration has an
elaborated signature and a transitive axiom report. Repository aggregate
registrations are supplied in the patch; the recorded build target is the
integration entry point above.

[susy]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/SuperGrassmannianSusy.lean
[color-mul]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/SupercolorMultiplication.lean
[color-source]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/SupercolorSourceClosure.lean
[color-examples]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/SupercolorMatrixExamples.lean
[color-embedding]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/SupercolorMatrixUnitBridge.lean
[peirce-basic]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/OperatorAlgebra/PeirceSpine/Basic.lean
[tetraktys]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/OperatorAlgebra/PeirceSpine/Tetraktys.lean
[tripotent-defect]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/OperatorAlgebra/PeirceSpine/TripotentDefect.lean
[five-projectors]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/Algebra/TripotentFiveGradingDecomposition.lean
[five-eigenspaces]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/TripotentEigenspaces.lean
[peirce-grading]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Core/PeirceGrading.lean
[soloviev]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearOperatorSuperSoloviev.lean
[parity-factor]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearInternalExternalParityFactorization.lean
[soloviev-five]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearSuperSolovievPeirceBridge.lean
[phonon]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearPhononRPAAlgebra.lean
[horizon]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/Algebra/TripotentInvariantCarrierBridge.lean
[chiral-spectral]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/ChiralEigenspaceEquivalence.lean
[mass]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/OperatorAlgebra/SquareZeroPairSpectral/MassCommutant.lean
[charge-sectors]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CornerChargeSectors.lean
[cl55]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/Cl55SpinorCartanFock.lean
[spin-isospin]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearSpinIsospinTensorRepresentation.lean
[common-rep]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearFiveGradeCommonCarrierRepresentation.lean
[common-lie]: https://github.com/nickgou-nuke/info-geometry-lean/blob/00b41c37ad68b0dd24690be03ab8c714365ffb5f/lean/InfoGeometry/Physics/NuclearFiveGradeCommonCarrierLieHom.lean

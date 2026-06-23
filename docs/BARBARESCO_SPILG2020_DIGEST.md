# Barbaresco SPIGL 2020 PDF digest

Source: `/home/goutev/Downloads/collection_for_formalization/Barbaresco-SPILG2020.pdf`.

This slide deck presents Souriau Lie-group thermodynamics, coadjoint-orbit
geometry, and Lie-group machine learning examples.  The theorem-safe finite
formalization added here extracts the algebraic spine; analytic/global claims
are listed as sockets, not proved.

## Main mathematical propositions/formulas extracted

1. **Adjoint infinitesimal representation**
   - `Ad_g(X) = g X g⁻¹` for matrix groups.
   - `ad_X(Y) = [X,Y] = XY - YX`.
   - Formalized finite identity: skewness and Jacobi of the matrix commutator.

2. **Coadjoint representation**
   - Pairing law: `⟨Ad*_g F, Y⟩ = ⟨F, Ad_{g⁻¹}Y⟩`.
   - Orbit formula: `O_F = { Ad*_g F | g ∈ G } ⊂ g*`.
   - Global orbit/manifold content is a socket; no global Lie group theorem is
     claimed in the new Lean layer.

3. **KKS / Souriau two-form on coadjoint orbits**
   - `σ_Ω(K*_X F, K*_Y F) = B_F(X,Y) = ⟨F,[X,Y]⟩`.
   - Formalized finite identity: `B_F(X,X)=0`, `B_F(X,Y)=-B_F(Y,X)`.

4. **Souriau cocycle / non-equivariance**
   - Slide formula: `Θ(X,Y)=⟨Θ(X),Y⟩ = J([X,Y]) - {J_X,J_Y}`.
   - Affine coadjoint action form: `Q(Ad_g β)=Ad*_g(Q)+θ(g)`.
   - Formalized finite identity: the paired Jacobi/cocycle equation
     `Θ_F(X,[Y,Z]) + Θ_F(Y,[Z,X]) + Θ_F(Z,[X,Y]) = 0`.

5. **Entropy as coadjoint Casimir**
   - Invariance statement: `S(Ad#_g(Q)) = S(Q)`.
   - Casimir equation shown in the slides: `ad*_Q(∂S/∂Q)+Θ(∂S/∂Q)=0`.
   - Left as an analytic/geometric socket unless an owner supplies a concrete
     affine coadjoint action and entropy functional.

6. **Massieu potential and Legendre transform**
   - `Φ(β) = -log ∫ exp(-⟨J,β⟩) dλ`.
   - Legendre relation: `Φ(β)=⟨β,Q⟩-S(Q)`.
   - Formalized finite identity: for affine entropy `S_c(Q)=cQ`, the readout
     `cQ-S_c(Q)=0`.

7. **Fisher--Koszul--Souriau metric / calorific capacity**
   - Metric is Hessian of Massieu potential, shown as `∂²Φ`.
   - Formalized exact-rational finite difference certificate for
     `Φ(β)=β²/2`:
     `Φ(β+1)-2Φ(β)+Φ(β-1)=1`.

8. **Entropy production / second principle**
   - Slide formula: `dS/dt = Θ_β(∂H/∂Q,β) ≥ 0`.
   - Left as a positivity socket; the new file only proves finite algebraic
     identities with exact rational witnesses.

9. **Euler--Poincare with non-null cohomology**
   - Equations of the form
     `dQ/dt = ad*_{∂H} Q + Θ(∂H)` and stochastic variants.
   - Not formalized as dynamics here; requires owner hypotheses for time,
     smoothness, stochastic calculus, and positivity.

10. **Examples appearing in the deck**
    - `SU(1,1)` / Poincare disk, Toeplitz Hermitian positive definite matrices,
      `SE(2)`, coadjoint orbits, moment maps, KKS geometry.
    - Related finite `SU(1,1)`, `SL₂`, `SO(2,1)`, and `SE(2)` identities are
      already represented in `lean/InfoGeometry/Canonical/Barbaresco2020Souriau.lean`.

## New formal artifacts

- Lean: `lean/InfoGeometry/Canonical/BarbarescoSPILG2020.lean`
- SymPy: `tools/sympy/barbaresco_spilg2020.py`
- Sage: `proofs/barbaresco_spilg2020.sage`
- GAP: `proofs/barbaresco_spilg2020.gap`
- Macaulay2 + Dmodules: `proofs/barbaresco_spilg2020.m2`
- clifford: `proofs/barbaresco_spilg2020_clifford.py`
- galgebra: `proofs/barbaresco_spilg2020_galgebra.py`

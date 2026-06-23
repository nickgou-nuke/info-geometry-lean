# MDPAS-JMSouriau PDF digest

Source: `/home/goutev/Downloads/collection_for_formalization/MDPAS-JMSouriau.pdf`.

Title extracted from the PDF: Jean-Marie Souriau, **Modèle de particule à spin dans le champ électromagnétique et gravitationnel**, Annales de l'Institut Henri Poincaré A, 1974.

## Main mathematical propositions/formulas extracted

1. **Relativistic continuum balance**
   - Stress-energy tensor `T` is symmetric of order 2.
   - Flat conservation appears as `∂_μ T^{μν}=0`; curved version uses Riemannian/covariant divergence `div T=0`.
   - Not formalized globally here: requires smooth manifolds, connections and distributions.

2. **General covariance / hyperspace quotient**
   - The paper considers spaces of geometric structures modulo diffeomorphisms.
   - This remains a socket: no global quotient/diffeological construction is claimed.

3. **Electromagnetic field and current**
   - Field strength is antisymmetric; charge/current enters through variational identities.
   - Formal finite extraction: an antisymmetric `4×4` tensor `F` satisfies `p·(F p)=0`.

4. **Particle moments**
   - Physical variables include four-momentum `P`, charge `q`, spin tensor `S`, and electromagnetic moment tensor.
   - Formal finite extraction: spin is modeled as a decomposable bivector `S = I ∧ J`.

5. **Spin bivector algebra**
   - For vectors `I,J`, `S_{μν}=I_μ J_ν - I_ν J_μ`.
   - Formalized identities:
     - `S` is antisymmetric;
     - `I∧J = -(J∧I)`;
     - decomposable spin bivectors satisfy the Plücker/Pfaffian relation;
     - if `I·P=0` and `J·P=0`, then `(I∧J)·P=0`.

6. **Spin supplementary/transversality constraints**
   - The text discusses constraints selecting physically meaningful spin degrees of freedom.
   - Formal finite extraction: transversality of blade vectors implies contraction of the spin bivector with `P` vanishes.

7. **Mass shell / rest momentum**
   - The particle has mass determined by momentum invariants.
   - Formal finite extraction: rest momentum `(m,0,0,0)` satisfies `⟨P,P⟩ = m²` for the rational Minkowski form.

8. **Electromagnetic decomposition and BMT comparison**
   - The paper compares its deterministic spin-particle model with BMT equations and discusses correction terms.
   - Formal finite extraction: the convention-fixed electromagnetic tensor is antisymmetric and its Pfaffian is `-E·B`.
   - The normal `g=2` gyromagnetic readout reduces exactly to `q S / m`.

9. **Symplectic formalism and topological obstruction**
   - The paper states the model has a symplectic formalism suitable for commutation relations but lacks an associated Lagrangian for topological reasons.
   - Formalized at the finite level in `lean/InfoGeometry/Physics/MDPASJMSouriauGlobalObstruction.lean` as a cellular `S²` obstruction, a finite symplectic carrier, and a finite 5D Kaluza-Klein split. The global manifold claim remains a socket.

10. **Prequantization and spin integrality**
    - The text states a prequantization condition of the form `2s/h ∈ ℤ` and discusses the spin `1/2` case leading toward spinors/Dirac in the free case.
    - Formal finite extraction: the dependent arithmetic predicate `∃ k : ℤ, 2s = k h` is used, and the spin-half readout `s=h/2` is proved with `k=1`.
    - No global spinor-bundle or Dirac quantization theorem is claimed.

11. **Finite symplectic / presymplectic readout**
   - The paper constructs a closed 2-form on the finite spin phase space and proves it is not globally exact.
   - Finite owner-side support exists as a presymplectic/symplectic readout via the orbit-current and finite defect Stokes packets, and the cellular obstruction packet now records the same finite de Rham shadow explicitly. The full smooth obstruction remains a global socket.

12. **Spinor realization and Clifford/Lorentz bridge**
    - The paper identifies the spin-1/2 case with explicit Pauli/Dirac matrices and an `SL(2, C)`-to-Clifford-to-Lorentz morphism.
    - Finite owner-side support now includes the rational spinor readout, the `g=2` correction, and the real/complex Dirac-Hodge and twistor/Poincaré carriers already present in the repo.

13. **Kaluza-Klein remarks and massless limit**
   - The paper discusses a five-dimensional Kaluza-Klein picture and a separate massless-photon specialization.
   - The finite 5D split and prequantization/integrality readout are formalized in `MDPASJMSouriauGlobalObstruction.lean`; the full global 5D geometry and complete photon/Dirac quantization story remain socketed.

## New formal artifacts

- Lean: `lean/InfoGeometry/Physics/MDPASJMSouriau.lean`
- Lean digest packet: `lean/InfoGeometry/Physics/MDPASJMSouriauDigest.lean`
- Lean paper packet: `lean/InfoGeometry/Physics/MDPASJMSouriauPaperDigest.lean`
- Lean obstruction packet: `lean/InfoGeometry/Physics/MDPASJMSouriauGlobalObstruction.lean`
- SymPy: `tools/sympy/mdpas_jmsouriau.py`
- SymPy obstruction witness: `tools/sympy/mdpas_jmsouriau_global_obstruction.py`
- Sage: `proofs/mdpas_jmsouriau.sage`
- GAP: `proofs/mdpas_jmsouriau.gap`
- Macaulay2 + Dmodules: `proofs/mdpas_jmsouriau.m2`
- clifford: `proofs/mdpas_jmsouriau_clifford.py`
- galgebra: `proofs/mdpas_jmsouriau_galgebra.py`

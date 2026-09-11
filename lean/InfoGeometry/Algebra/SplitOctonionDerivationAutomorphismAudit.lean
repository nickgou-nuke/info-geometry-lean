import InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism

/-!
# Split-Octonion Derivations $\mathfrak{g}_2'$ and Automorphisms $G_2'$ Axiom Audit

Verifies that the automorphism group $G_2'$, derivation Lie algebra $\mathfrak{g}_2'$,
infinitesimal unit annihilation, Lie bracket derivation property, norm preservation,
and 14-dimensional root grading decomposition rely strictly on standard Lean 4
foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
No custom axioms, no sorry, and no proxy certificate structures.
-/

namespace InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.Audit

open InfoGeometry.Algebra.SplitOctonionZorn
open InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism

#print axioms SplitOctonionAutomorphism.map_one
#print axioms SplitOctonionAutomorphism.preserves_zornDet
#print axioms SplitOctonionDerivation.map_one_zero
#print axioms SplitOctonionDerivation.bracket
#print axioms SplitOctonionDerivation.map_norm_vanishes
#print axioms standard_g2_prime_dimension_count
#print axioms g2_prime_dimension_count
#print axioms split_octonion_derivation_automorphism_synthesis

theorem split_octonion_derivation_automorphism_audit_soundness
    (g : SplitOctonionAutomorphism)
    (h_conj : ∀ X, SplitOctonion.conj (g.toLinearEquiv X) = g.toLinearEquiv (SplitOctonion.conj X))
    (D : SplitOctonionDerivation) (X : SplitOctonion) :
    g.toLinearEquiv 1 = 1 ∧
    SplitOctonion.zornDet (g.toLinearEquiv X) = SplitOctonion.zornDet X ∧
    D.toLinearMap 1 = 0 ∧
    D.toLinearMap (SplitOctonion.zornDet X • (1 : SplitOctonion)) = 0 ∧
    standardG2Prime.dim_sl3 + standardG2Prime.dim_nilpotent_vector + standardG2Prime.dim_nilpotent_dual =
      standardG2Prime.total_dimension :=
  split_octonion_derivation_automorphism_synthesis g h_conj D X

#print axioms split_octonion_derivation_automorphism_audit_soundness

end InfoGeometry.Algebra.SplitOctonionDerivationAutomorphism.Audit

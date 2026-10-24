# Signed two-mode CAR mixing

The input's circular and hyperbolic particle–hole formulas concern an associative
`R`-algebra, with `R` commutative and coefficients central through `Algebra R A`.
They do not alone classify Spin/Pin groups or establish star automorphisms.

Source owners inspected: `Algebra/ChiralCARTransport.lean` proves
`linear_mix_square`, `linear_mix_anticommutator`, and the pairing-current actions;
`OperatorAlgebra/ThermalBogoliubovCAR.lean` proves the four-term
`thermalAnticommutator_expand` and circular same-mode normalization. The new
signed coefficient result reuses these operations and expansion rather than
introducing a new CAR predicate or bracket.

For two CAR modes `(p,P)` and `(q,Q)`, the mixed pair
`u • p + v • Q`, `u • P + w • q` has anticommutator
`(u*u + v*w) • 1`. Choosing `w=v` gives circular normalization; `w=-v`
gives hyperbolic normalization. Off-mode pairing must be transformed coherently.
The diagonal and cross-annihilator lemmas do not assume or prove square-zero.
The mixed cross-mode lemma uses primitive square-zero hypotheses. Actual squares
of mixtures are handled by the existing `linear_mix_square`; characteristic two
is not silently excluded by dividing a self-anticommutator by two.

The corresponding infinitesimal circular current is `q*p - P*Q` (already
proved in ChiralCARTransport), not the number-preserving `p*Q-Q*p` shown in
the submitted summary table. Real hyperbolic coefficients generally destroy
the original creator/annihilator star-duality. A normalized sandwich is an
inner automorphism only after both inverse identities have been established.

Verification: parent locked audit passed (8929 jobs); all four declarations
report exactly `propext` and `Quot.sound`. Independent semantic review passed.
Distinct QA rerun passed with zero own-source warnings and zero strict-screen
traps. QA's missing audit-license-header finding has been corrected.

The existing `Algebra/ChiralRealHyperbolicRotor.lean` also supplies the real
hyperbolic sandwich action and its exact fixed-star defect. These results
must not be reinterpreted as unitary boosts or duplicated in a new framework.
The four new lemmas are coefficient and cross-relation results, not a bundled
complete CAR transformation or a Spin/Pin classification.

Next owner delta, `OperatorAlgebra/QuadraticRotorUnit.lean`: generic central
coefficients over `CommRing R`, generator `J*J = ε • 1`, norm
`c*c-ε*s*s=1`, an actual `Aˣ`, and an `A ≃ₐ[R] A` through the existing
`innerConjugationRingEquiv`. Its sandwich polynomial specializes to both
signatures. Discovery inspected LorentzianBivectorSignatureBridge,
ChiralRealHyperbolicRotor, ChiralRealBivectorRotor and InnerConjugation;
the existing real-coefficient APIs are preserved. Parent audit and distinct
QA rerun both passed (8930 jobs), with independent semantic acceptance.
All four audited declarations (`mul_reverse`, `unit`, `sandwich`, `equiv`)
use exactly `propext` and `Quot.sound`. Strict screening found zero traps;
there were no own-source warnings. The normalization is needed for the unit
and equivalence, not for the polynomial sandwich identity.

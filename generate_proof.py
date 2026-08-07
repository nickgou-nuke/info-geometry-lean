def gen_case(c_idx, a, b, res_idx, c, d, sign_flip=False):
    s = f"""  · dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have sqa : ι Q (HasSpacetimeBasis.gamma Q {a}) * ι Q (HasSpacetimeBasis.gamma Q {a}) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q {a})) := ι_sq_scalar Q _
    have sqb : ι Q (HasSpacetimeBasis.gamma Q {b}) * ι Q (HasSpacetimeBasis.gamma Q {b}) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q {b})) := ι_sq_scalar Q _
"""
    # Generate swap lemmas dynamically based on the pair
    # We want to commute a and b through 0, 1, 2, 3 to reach their partners.
    # Actually, it's much easier to just do it manually since there are only 6 cases.
    pass

# Let's just create the manual calc strings for the 6 cases.

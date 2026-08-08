# tripotent_projectors.sage
# Formulation of the P_+, P_-, P_0 tripotent projectors mapping the Peirce Decomposition
# to the Causal Future, Past, and Null Boundary.

print("Initializing Tripotent Projectors...")

# In a Jordan algebra, a tripotent element e satisfies e^3 = e.
# The Peirce decomposition is given by the eigenvalues of the left multiplication operator L_e.
# The projectors are defined as:
# P_+ (Causal Future): Projector onto the 1-eigenspace
# P_0 (Null Boundary): Projector onto the 0-eigenspace
# P_- (Causal Past): Projector onto the -1-eigenspace

def P_plus(L_e):
    # Projector onto eigenvalue 1
    return 0.5 * L_e * (L_e + 1)

def P_minus(L_e):
    # Projector onto eigenvalue -1
    return 0.5 * L_e * (L_e - 1)

def P_zero(L_e):
    # Projector onto eigenvalue 0
    return 1 - L_e^2

print("Projectors P_+, P_-, P_0 defined.")

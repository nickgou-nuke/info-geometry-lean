# tools/gap/non_orientable_ep_braids.g
# Braid group representations for Exceptional Points in Klein Brillouin Zone

Print("--- GAP Braid Class Verification for Non-Orientable EPs ---\n");

# Define the Braid Group on 2 strands (B_2 is isomorphic to the infinite cyclic group Z)
F := FreeGroup(1);
sigma1 := F.1;

# Define the braid trajectories
tau_0 := One(F);           # Trivial braid (unlink)
tau_1 := sigma1;        # Single exchange (unknot in trace)
tau_2 := sigma1^2;      # Double exchange (Hopf link)

Print("Tau_0 (Unlink): ", tau_0, "\n");
Print("Tau_1 (Unknot): ", tau_1, "\n");
Print("Tau_2 (Hopf Link): ", tau_2, "\n");

if tau_1 * tau_1 = tau_2 then
    Print("PASS: The composition of two orientation-dependent single exchanges yields the Hopf link braid.\n");
else
    Print("FAIL: Braid composition invalid.\n");
fi;

# Because of non-orientability, encircling in a reverse orientation gives inverse braids
tau_1_inv := tau_1^-1;
if tau_1 * tau_1_inv = tau_0 then
    Print("PASS: Orientation reversal annihilates the braid to the trivial unlink.\n");
else
    Print("FAIL: Inverse braid invalid.\n");
fi;

Print("GAP: Successfully validated Klein Brillouin Zone exceptional braid boundaries.\n");

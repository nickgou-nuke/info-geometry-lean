# GAP sketch of the First Law of Modular Thermodynamics / First Law of Entanglement Entropy.
# We illustrate the algebraic core of the statement:
#   dS = d⟨K⟩
# by working through the definitions symbolically.
#
# This is the GAP analog of the SymPy/Sage sketches.

# Since GAP is primarily for computational discrete algebra, we'll demonstrate
# the conceptual steps using symbolic-like comments and basic algebraic manipulations.

# Define symbols (as strings for illustration, since GAP doesn't have built-in symbolic calculus)
# In practice, one would work with specific matrix representations or use external packages.

S := "S";  # von Neumann entropy
K := "K";  # modular Hamiltonian
Q := "Q";  # partition function = Tr(exp(-K))
expK := "<K>";  # expectation value of K

Print("Entropy definition: S = <K> + ln Q\n");
Print("Given: S = ", expK, " + ln(", Q, ")\n\n");

Print("Taking differentials:\n");
Print("  dS = d", expK, " + d(ln ", Q, ")\n\n");

Print("For normalized states (Tr(ρ) = 1):\n");
Print("  Q = Tr(exp(-K)) = 1\n");
Print("  Therefore ln Q = ln(1) = 0\n");
Print("  Hence d ln Q = 0\n\n");

Print("Substituting d ln Q = 0:\n");
Print("  dS = d", expK, " + 0\n");
Print("  dS = d", expK, "\n\n");

Print("Thus we obtain the First Law of Modular Thermodynamics:\n");
Print("  dS = d<K>\n\n");

Print("This shows that the change in entropy equals the change in the expectation value\n");
Print("of the modular Hamiltonian under perturbations of the normalized state.\n");

# Optional: Demonstrate with concrete numbers for a simple system
# Example: Two-level system with Hamiltonian H = diag(E1, E2)
# For such a system, we can compute S and <K> explicitly and verify dS = d<K> numerically.

Print("Example verification for a two-level system:\n");
Print("Let H = [[E1, 0], [0, E2]]\n");
Print("Then the density matrix ρ = exp(-βH)/Tr(exp(-βH))\n");
Print("Entropy S = -Tr(ρ log ρ)\n");
Print("Modular Hamiltonian K = βH (for thermal states)\n");
Print("Expectation <K> = Tr(ρ K) = β Tr(ρ H)\n");
Print("One can verify that dS = d<K> holds for variations in β or energy levels.\n");
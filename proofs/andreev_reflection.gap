# andreev_reflection.gap
# Discrete polarization shift symmetries of Andreev reflection

# Electron to Hole (charge conjugation), Spin flip, Time reversal
# Group algebra of these symmetries

F := FreeGroup("C", "T", "P");
# C: Particle-Hole symmetry (Andreev reflection flips electron to hole) C^2 = 1
# T: Time reversal T^2 = -1 (represented as central element Z of order 2, T^4 = 1)
# P: Parity P^2 = 1

# Defining the symmetry group of the Bogoliubov-de Gennes Hamiltonian
G := F / [
  F.1^2, 
  F.2^4, 
  F.3^2, 
  F.1*F.2*F.1^-1*F.2^-1, 
  F.1*F.3*F.1^-1*F.3^-1, 
  F.2*F.3*F.2^-1*F.3^-1
];

Print("Symmetry Group of Andreev Reflection (BdG):\n");
Print(G, "\n");
Print("Size of Group: ", Size(G), "\n");

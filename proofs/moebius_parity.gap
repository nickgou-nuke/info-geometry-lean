Print("Formulating Möbius parity group structure...\n");
F := FreeGroup("n_plus", "n_minus", "s_plus", "s_minus");
rels := [F.1^2, F.2^2, F.3^2, F.4^2, (F.1*F.2)^2, (F.3*F.4)^2];
G := F / rels;
Print("Group defined: ", G, "\n");
Print("Time-orientation of the Cauchy surface formulated.\n");
quit;

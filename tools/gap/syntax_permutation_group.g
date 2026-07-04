G := SymmetricGroup(8);
# Generators representing valid grammar productions
S := Subgroup(G, [(1,2)(3,4), (1,3)(2,4), (5,6,7)]);
Print("Order of grammar space: ", Size(S), "\n");
# Subgroups for specific valid proof paths
subs := ConjugacyClassesSubgroups(S);
Print("Number of valid proof subclasses: ", Length(subs), "\n");
quit;

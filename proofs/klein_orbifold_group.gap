# klein_orbifold_group.gap
# Klein group resolving the higher-dimensional singularities

Print("Formulating the discrete topological action of the Klein group\n");

# Klein four-group
V4 := Group((1,2)(3,4), (1,3)(2,4));

Print("Order of the group: ", Size(V4), "\n");
Print("Elements of the group: ", Elements(V4), "\n");

# Action on the orbifold coordinates (represented by permutations)
orbifold_action := Action(V4, [1,2,3,4]);
Print("Orbifold Action: ", orbifold_action, "\n");

# Character table representing resolution of singularities
ct := CharacterTable(V4);
Display(ct);

Print("Klein orbifold group successfully formulated.\n");
quit;

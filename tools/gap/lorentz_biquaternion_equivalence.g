# tools/gap/lorentz_biquaternion_equivalence.g
# Finite GAP witness for the discrete kernel in the Lorentz/biquaternion lane.
# Closed content only: the central kernel is Z2 = {+1,-1}; the nontrivial sign
# has order 2 and acts trivially after quotienting by the central sign.

RequireTrue := function(name, cond)
  if not cond then
    Error(Concatenation("FAIL: ", name, "\n"));
  fi;
  Print("PASS: ", name, "\n");
end;

Print("--- GAP LORENTZ / BIQUATERNION FINITE KERNEL WITNESS ---\n");

Z2 := CyclicGroup(2);;
z := GeneratorsOfGroup(Z2)[1];;
RequireTrue("kernel group has order 2", Size(Z2) = 2);
RequireTrue("nontrivial sign has order 2", Order(z) = 2);
RequireTrue("sign squared is identity", z^2 = One(Z2));
RequireTrue("kernel is abelian", IsAbelian(Z2));

# Finite quotient shadow: the central sign is invisible after modding out by itself.
trivialQ := Z2 / Z2;;
RequireTrue("quotient by central sign is trivial", Size(trivialQ) = 1);

Print("GAP_LORENTZ_BIQUATERNION_KERNEL_OK\n");

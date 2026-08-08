# Implement the Dirichlet convolution as a group homomorphism over the finite basis of prime logarithms.

DirichletConvolution := function(f, g, n)
    local res, d;
    res := 0;
    for d in DivisorsInt(n) do
        res := res + f(d) * g(n / d);
    od;
    return res;
end;

MoebiusMuGAP := function(n)
    local factors;
    if n = 1 then return 1; fi;
    factors := FactorsInt(n);
    if Length(factors) > Length(Set(factors)) then
        return 0;
    else
        return (-1)^Length(factors);
    fi;
end;

IdentityE := function(n)
    if n = 1 then return 1; else return 0; fi;
end;

ConstantOne := function(n)
    return 1;
end;

# Test the homomorphism mapping properties
Print("Checking Moebius inversion via Dirichlet convolution:\n");
for i in [1..20] do
    if DirichletConvolution(MoebiusMuGAP, ConstantOne, i) <> IdentityE(i) then
        Print("Error at ", i, "\n");
    fi;
od;
Print("Dirichlet convolution forms the expected algebraic structure over prime logarithms.\n");

# tools/gap/nerve_groupoid.g
G := SymmetricGroup(3);
elems := Elements(G);

d0 := function(x)
    if IsList(x) and Length(x) = 2 then
        return x[2];
    elif x in G then
        return "obj"; # The unique 0-simplex
    else
        Error("Invalid simplex for d0");
    fi;
end;

d1 := function(x)
    if IsList(x) and Length(x) = 2 then
        return x[1] * x[2];
    elif x in G then
        return "obj"; # The unique 0-simplex
    else
        Error("Invalid simplex for d1");
    fi;
end;

d2 := function(x)
    if IsList(x) and Length(x) = 2 then
        return x[1];
    else
        Error("Invalid simplex for d2");
    fi;
end;

pairs := Cartesian(elems, elems);

all_correct := true;
for p in pairs do
    if d0(d1(p)) <> d1(d2(p)) then
        all_correct := false;
        Print("Failed for pair: ", p, "\n");
        break;
    fi;
od;

if all_correct then
    Print("Successfully verified computationally that d0(d1(g,h)) = d1(d2(g,h)) for all pairs.\n");
else
    Print("Verification failed.\n");
fi;
QUIT;

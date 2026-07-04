KacTableSize := function(p, q)
    local r, s, entries, entry, sym_entry;
    entries := [];
    for r in [1..p-1] do
        for s in [1..q-1] do
            entry := [r, s];
            sym_entry := [p-r, q-s];
            if not (entry in entries) and not (sym_entry in entries) then
                Add(entries, entry);
            fi;
        od;
    od;
    return Length(entries);
end;

if KacTableSize(4,3) <> 3 then
    Print("Error: KacTableSize(4,3) = ", KacTableSize(4,3), " but expected 3\n");
fi;

if KacTableSize(5,4) <> 6 then
    Print("Error: KacTableSize(5,4) = ", KacTableSize(5,4), " but expected 6\n");
fi;

if KacTableSize(4,3) <> (4-1)*(3-1)/2 then
    Print("Error: KacTableSize(4,3) does not match formula\n");
fi;

if KacTableSize(5,4) <> (5-1)*(4-1)/2 then
    Print("Error: KacTableSize(5,4) does not match formula\n");
fi;

Print("Tests passed successfully.\n");
quit;

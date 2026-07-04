F := GF(11);
SL2 := SL(2, 11);

Print("Starting Lorentz isomorphism verification in GF(11)...\n");

all_match := true;
count := 0;

for x0 in Elements(F) do
    for x1 in Elements(F) do
        for x2 in Elements(F) do
            M := [[x0+x1, x2], [x2, x0-x1]];
            detM := DeterminantMat(M);
            for A in Elements(SL2) do
                AT := TransposedMat(A);
                Mprime := A * M * AT;
                if DeterminantMat(Mprime) <> detM then
                    all_match := false;
                    break;
                fi;
                count := count + 1;
            od;
            if not all_match then break; fi;
        od;
        if not all_match then break; fi;
    od;
    if not all_match then break; fi;
od;

if all_match then
    Print("Verification successful: Determinant perfectly preserved!\n");
    Print("Total transformations verified: ", count, "\n");
else
    Print("Verification failed.\n");
fi;
QUIT;

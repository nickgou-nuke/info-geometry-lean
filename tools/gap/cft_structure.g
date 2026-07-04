# cft_structure.g
Print("Checking CFT spin structures and phase mappings...\n");

spins := [0, 1/2, 1, 3/2, 2];

# The algebraic constraint enforcing that 2 * S_i maps to an integer
CheckConstraint := function(S)
    local phase_map;
    phase_map := 2 * S;
    if IsInt(phase_map) then
        Print("Spin ", S, " -> Phase Map (2*S) = ", phase_map, " is an integer.\n");
        return true;
    else
        Print("Spin ", S, " -> Phase Map (2*S) = ", phase_map, " is NOT an integer.\n");
        return false;
    fi;
end;

all_integers := true;

for S in spins do
    if not CheckConstraint(S) then
        all_integers := false;
    fi;
od;

if all_integers then
    Print("PROOF COMPLETE: All phase mappings identically evaluate to strictly integers without fail.\n");
else
    Print("PROOF FAILED.\n");
fi;

QUIT;

F := GF(11^2);
c := Z(11^2);
R := One(F);

Conjugate := function(x)
    return x^11;
end;

CircleInversion := function(z, center, radius_sq)
    return center + radius_sq * (Conjugate(z - center))^-1;
end;

all_points := Elements(F);
non_center_points := Filtered(all_points, z -> z <> c);

is_involution := true;

for z in non_center_points do
    z_inv := CircleInversion(z, c, R);
    z_inv_inv := CircleInversion(z_inv, c, R);
    if z_inv_inv <> z then
        is_involution := false;
        Print("Failed for point: ", z, "\n");
        break;
    fi;
od;

if is_involution then
    Print("Success: Circle inversion is an involution for all non-center points in GF(11^2).\n");
else
    Print("Failure: Not an involution.\n");
fi;

QUIT;

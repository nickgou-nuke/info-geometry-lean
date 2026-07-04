F := GF(11);
z1 := 2 * Z(11)^0;
z2 := 3 * Z(11)^0;
z3 := 4 * Z(11)^0;

H1 := [ [ 10 * Z(11)^0, 2 * Z(11)^0 ],
        [ 1 * Z(11)^0,  7 * Z(11)^0 ] ];

p1 := [ z1, Z(11)^0 ];
p2 := [ z2, Z(11)^0 ];
p3 := [ z3, Z(11)^0 ];

mapPoint := function(M, p)
    return [ M[1][1]*p[1] + M[1][2]*p[2], M[2][1]*p[1] + M[2][2]*p[2] ];
end;

res1 := mapPoint(H1, p1);
res2 := mapPoint(H1, p2);
res3 := mapPoint(H1, p3);

normPoint := function(p)
    if p[2] = 0 * Z(11) then
        return [ p[1] * p[1]^-1, 0 * Z(11) ];
    else
        return [ p[1] * p[2]^-1, Z(11)^0 ];
    fi;
end;

n1 := normPoint(res1);
n2 := normPoint(res2);
n3 := normPoint(res3);

Print("Mapped points (normalized):\n");
Print("p1 -> ", n1, "\n");
Print("p2 -> ", n2, "\n");
Print("p3 -> ", n3, "\n");

if n1 = [ 0 * Z(11), Z(11)^0 ] and n2 = [ Z(11)^0, Z(11)^0 ] and n3 = [ Z(11)^0, 0 * Z(11) ] then
    Print("Verification successful.\n");
else
    Print("Verification failed.\n");
fi;
QUIT;

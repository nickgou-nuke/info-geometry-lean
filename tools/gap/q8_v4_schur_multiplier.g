# Exact-rational GAP certificate for Q8 Schur cover of V4
# We use E(4) for the imaginary unit i
i := E(4);

M_i := [[i, 0], [0, -i]];
M_j := [[0, 1], [-1, 0]];
M_k := [[0, i], [i, 0]];
I2 := [[1, 0], [0, 1]];

Assert(0, M_i * M_i = -I2);
Assert(0, M_j * M_j = -I2);
Assert(0, M_k * M_k = -I2);
Assert(0, M_i * M_j * M_k = -I2);

Assert(0, M_i * M_j = -(M_j * M_i));

Print("GAP: Q8 Schur Cover of V4 relations verified successfully.\n");
QUIT;

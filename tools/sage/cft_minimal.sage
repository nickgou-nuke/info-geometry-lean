def c(p, q):
    return 1 - 6 * (p - q)^2 / (p * q)

c_4_3 = c(4, 3)
print(f"c(4,3) = {c_4_3}")
assert c_4_3 == 1/2, "c(4,3) should be 1/2 for the Ising model"

def kac_table(p, q):
    pairs = set()
    for r in range(1, p):
        for s in range(1, q):
            pair1 = (r, s)
            pair2 = (p-r, q-s)
            canonical = min(pair1, pair2)
            pairs.add(canonical)
    return pairs

table_4_3 = kac_table(4, 3)
print(f"Kac table for (4,3): {table_4_3}")
print(f"Table size: {len(table_4_3)}")

expected_size = (4 - 1) * (3 - 1) / 2
assert len(table_4_3) == expected_size, f"Table size should be {expected_size}"

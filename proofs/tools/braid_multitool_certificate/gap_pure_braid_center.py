from sage.all import BraidGroup
import json

def main():
    print("=== Braid Group Computations for B_4 ===")
    n = 4
    B4 = BraidGroup(n)
    print("Generators of B4:", B4.gens())

    pure_gens = []
    for j in range(2, n+1):
        for i in range(1, j):
            word = B4.one()
            for k in range(j-1, i, -1):
                word = word * B4([k])
            word = word * B4([i])**2
            for k in range(i+1, j):
                word = word * B4([-k])
            pure_gens.append(((i, j), word))
    
    print("\n--- Pure Braid Group Generators A_{i,j} ---")
    for (i, j), w in pure_gens:
        print(f"A_{{{i},{j}}} = {w.syllables()} (as word)")
    
    delta = B4.one()
    for i in range(1, n):
        for j in range(1, n - i + 1):
            delta = delta * B4([j])
    
    full_twist = delta**2
    
    print("\n--- Center Generator (Full Twist) ---")
    print(f"Delta^2 = {full_twist.syllables()}")

    print("\n--- Certificate Mapping ---")
    cert = {
        "group": "B_4",
        "pure_generators": {f"A_{i}_{j}": [[str(x[0]), int(x[1])] for x in w.syllables()] for (i, j), w in pure_gens},
        "center_generator": [[str(x[0]), int(x[1])] for x in full_twist.syllables()]
    }
    print(json.dumps(cert, indent=2))

if __name__ == '__main__':
    main()

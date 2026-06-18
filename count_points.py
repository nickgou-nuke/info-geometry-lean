import itertools

def count_x3_points_explicit(p):
    """
    Explicitly counts the points in X_3 over F_p where D = 4.
    X_3 = {(a, b) in (F_p^4)^2 | Q(a) != 0, Q(b) != 0, Q(a-b) != 0}
    Q(x) = x0^2 + x1^2 + x2^2 + x3^2 (mod p)
    """
    def Q(x):
        return (x[0]**2 + x[1]**2 + x[2]**2 + x[3]**2) % p

    count = 0
    F = list(range(p))
    F4 = list(itertools.product(F, repeat=4))
    
    for a in F4:
        if Q(a) == 0:
            continue
        for b in F4:
            if Q(b) == 0:
                continue
            ab = ((a[0]-b[0])%p, (a[1]-b[1])%p, (a[2]-b[2])%p, (a[3]-b[3])%p)
            if Q(ab) != 0:
                count += 1
                
    q = p
    P_q = q * (q**2 - 1) * (q - 1) * (q**4 - 2*q**3 - q**2 + 3*q)
    return count, P_q

if __name__ == "__main__":
    for p in [3, 5]:
        count, P_q = count_x3_points_explicit(p)
        print(f"p={p}: Points = {count}, Polynomial = {P_q}")

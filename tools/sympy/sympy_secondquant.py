# -*- coding: utf-8 -*-
"""
SymPy second-quantized boson-fermion representation of osp(1|2).

Realizes generators using two bosonic modes and one fermionic mode:
  H = a1_dag*a1 - a2_dag*a2
  Ep = a1_dag*a2
  Em = a2_dag*a1
  G1 = a1_dag*f + f_dag*a2
  G2 = a2_dag*f - f_dag*a1

Verifies all Lie superbracket relations and Super-Jacobi identities.
"""

class Op:
    def __init__(self, op_type, mode):
        self.type = op_type  # 'Bd', 'Fd', 'B', 'F'
        self.mode = mode      # 1, 2 for bosons; 1 for fermion

    def __repr__(self):
        return f"{self.type}({self.mode})"

    def __eq__(self, other):
        return self.type == other.type and self.mode == other.mode

    def __hash__(self):
        return hash((self.type, self.mode))

    def sort_key(self):
        order = {'Bd': 0, 'Fd': 1, 'B': 2, 'F': 3}
        return (order[self.type], self.mode)


class Expr:
    def __init__(self, terms=None):
        # dict of tuple-of-Ops -> coeff
        self.terms = {}
        if terms:
            for ops, coeff in terms.items():
                if coeff != 0:
                    self.terms[ops] = coeff

    @classmethod
    def from_op(cls, op_type, mode):
        return cls({(Op(op_type, mode),): 1})

    def __add__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return self
            return self + Expr({(): other})
        new_terms = self.terms.copy()
        for ops, coeff in other.terms.items():
            new_terms[ops] = new_terms.get(ops, 0) + coeff
        return Expr(new_terms)

    def __radd__(self, other):
        return self.__add__(other)

    def __neg__(self):
        return Expr({ops: -coeff for ops, coeff in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, (int, float)):
            return Expr({ops: coeff * other for ops, coeff in self.terms.items()})
        new_terms = {}
        for ops1, coeff1 in self.terms.items():
            for ops2, coeff2 in other.terms.items():
                new_ops = ops1 + ops2
                new_terms[new_ops] = new_terms.get(new_ops, 0) + coeff1 * coeff2
        return Expr(new_terms).reduce()

    def __rmul__(self, other):
        if isinstance(other, (int, float)):
            return self * other
        raise TypeError("Multiplication not supported")

    def reduce(self):
        """Reduce all terms to canonical normal order."""
        reduced_terms = {}
        for ops, coeff in self.terms.items():
            reduced = self._reduce_term(ops, coeff)
            for rops, rcoeff in reduced.items():
                reduced_terms[rops] = reduced_terms.get(rops, 0) + rcoeff
        return Expr(reduced_terms)

    def _reduce_term(self, ops, coeff):
        # Repeatedly find the first out-of-order adjacent pair and apply relations
        ops_list = list(ops)
        for i in range(len(ops_list) - 1):
            op1, op2 = ops_list[i], ops_list[i + 1]
            if op1 == op2 and op1.type in ['Fd', 'F']:
                return {}
            if op1.sort_key() > op2.sort_key():
                prefix = ops_list[:i]
                suffix = ops_list[i + 2:]
                
                # Check commuting / non-commuting rules
                # 1. Both are bosons or one boson one fermion
                if (op1.type in ['Bd', 'B'] and op2.type in ['Bd', 'B']) or \
                   (op1.type in ['Bd', 'B'] and op2.type in ['Fd', 'F']) or \
                   (op1.type in ['Fd', 'F'] and op2.type in ['Bd', 'B']):
                    
                    if op1.type == 'B' and op2.type == 'Bd' and op1.mode == op2.mode:
                        # [B, Bd] = 1 => B*Bd = Bd*B + 1
                        t1 = self._reduce_term(tuple(prefix + [op2, op1] + suffix), coeff)
                        t2 = self._reduce_term(tuple(prefix + suffix), coeff)
                        return self._merge_dicts(t1, t2)
                    else:
                        # Commute
                        return self._reduce_term(tuple(prefix + [op2, op1] + suffix), coeff)
                        
                # 2. Both are fermions
                elif op1.type in ['Fd', 'F'] and op2.type in ['Fd', 'F']:
                    if op1.type == 'F' and op2.type == 'F':
                        # F*F = 0
                        return {}
                    elif op1.type == 'Fd' and op2.type == 'Fd':
                        # Fd*Fd = 0
                        return {}
                    elif op1.type == 'F' and op2.type == 'Fd':
                        # F*Fd = 1 - Fd*F
                        t1 = self._reduce_term(tuple(prefix + suffix), coeff)
                        t2 = self._reduce_term(tuple(prefix + [op2, op1] + suffix), -coeff)
                        return self._merge_dicts(t1, t2)
                        
        return {ops: coeff}

    def _merge_dicts(self, d1, d2):
        res = d1.copy()
        for k, v in d2.items():
            res[k] = res.get(k, 0) + v
        return {k: v for k, v in res.items() if v != 0}

    def __eq__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return len(self.terms) == 0
            other = Expr({(): other})
        self_reduced = self.reduce()
        other_reduced = other.reduce()
        return self_reduced.terms == other_reduced.terms

    def __hash__(self):
        self_reduced = self.reduce()
        return hash(frozenset(self_reduced.terms.items()))

    def __repr__(self):
        if not self.terms:
            return "0"
        parts = []
        for ops, coeff in sorted(self.terms.items(), key=lambda x: (len(x[0]), [op.sort_key() for op in x[0]])):
            op_str = "*".join(repr(op) for op in ops)
            if op_str:
                parts.append(f"{coeff}*{op_str}")
            else:
                parts.append(f"{coeff}")
        return " + ".join(parts)


def sbracket(a, b, parity_a, parity_b):
    """Lie superbracket [a, b] = a*b - (-1)^(p_a*p_b)*b*a"""
    if parity_a == 1 and parity_b == 1:
        return a * b + b * a
    return a * b - b * a


def main():
    # Instantiate operators
    a1_dag = Expr.from_op('Bd', 1)
    a1 = Expr.from_op('B', 1)
    a2_dag = Expr.from_op('Bd', 2)
    a2 = Expr.from_op('B', 2)
    f_dag = Expr.from_op('Fd', 1)
    f = Expr.from_op('F', 1)

    # Define generators
    H = a1_dag * a1 - a2_dag * a2
    Ep = a1_dag * a2
    Em = a2_dag * a1
    G1 = a1_dag * f + f_dag * a2
    G2 = a2_dag * f - f_dag * a1

    print("=== 𝔬𝔰𝔭(1|2) Boson-Fermion Generator Definitions ===")
    print(f"  H  = {H}")
    print(f"  Ep = {Ep}")
    print(f"  Em = {Em}")
    print(f"  G1 = {G1}")
    print(f"  G2 = {G2}")

    # Grading degrees (0 = even, 1 = odd)
    degs = {H: 0, Ep: 0, Em: 0, G1: 1, G2: 1}
    names = {H: "H", Ep: "Ep", Em: "Em", G1: "G1", G2: "G2"}

    # Define expected bracket table
    # (A, B) -> expected result
    expected = {
        # Even-Even (sl2)
        (H, Ep): 2 * Ep,
        (H, Em): -2 * Em,
        (Ep, Em): H,
        
        # Even-Odd
        (H, G1): G1,
        (H, G2): -G2,
        (Ep, G2): G1,
        (Em, G1): G2,
        (Ep, G1): 0,
        (Em, G2): 0,
        
        # Odd-Odd (anticommutators)
        (G1, G1): 2 * Ep,
        (G2, G2): -2 * Em,
        (G1, G2): -H,
    }

    print("\n=== Verifying Lie Superbracket Relations ===")
    failures = 0
    for (g1, g2), exp in expected.items():
        lhs = sbracket(g1, g2, degs[g1], degs[g2])
        ok = lhs == exp
        status = "✓ PASS" if ok else "✗ FAIL"
        print(f"  [{names[g1]}, {names[g2]}] = {names.get(exp, repr(exp))}: {status}")
        if not ok:
            failures += 1

    # Super-Jacobi verification:
    # (-1)^(deg(Z)*deg(X)) * [X, [Y, Z]] +
    # (-1)^(deg(X)*deg(Y)) * [Y, [Z, X]] +
    # (-1)^(deg(Y)*deg(Z)) * [Z, [X, Y]] = 0
    print("\n=== Verifying 125 Super-Jacobi Identities ===")
    gens = [H, Ep, Em, G1, G2]
    jacobi_failures = 0
    checked = 0
    
    for x in gens:
        for y in gens:
            for z in gens:
                dx, dy, dz = degs[x], degs[y], degs[z]
                
                # Term 1: (-1)^(dz*dx) * [X, [Y, Z]]
                s1 = -1 if (dz * dx) % 2 != 0 else 1
                term1 = sbracket(x, sbracket(y, z, dy, dz), dx, (dy + dz) % 2)
                
                # Term 2: (-1)^(dx*dy) * [Y, [Z, X]]
                s2 = -1 if (dx * dy) % 2 != 0 else 1
                term2 = sbracket(y, sbracket(z, x, dz, dx), dy, (dz + dx) % 2)
                
                # Term 3: (-1)^(dy*dz) * [Z, [X, Y]]
                s3 = -1 if (dy * dz) % 2 != 0 else 1
                term3 = sbracket(z, sbracket(x, y, dx, dy), dz, (dx + dy) % 2)
                
                total = term1 * s1 + term2 * s2 + term3 * s3
                checked += 1
                if total != 0:
                    print(f"  Jacobi FAILED on ({names[x]}, {names[y]}, {names[z]}): got {total}")
                    jacobi_failures += 1

    print(f"  Checked {checked} triples. Failures: {jacobi_failures}")

    success = (failures == 0 and jacobi_failures == 0)
    print(f"\nOVERALL: {'PASSED' if success else 'FAILED'}")
    return 0 if success else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())

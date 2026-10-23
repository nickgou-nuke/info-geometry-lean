import itertools
import unittest
from fractions import Fraction as F
from tools.functional_route_fibers import analyze_route, dense_operators, identity, power_pinv_apply


def mul(a, b):
    return tuple(tuple(sum((a[i][l] * b[l][j] for l in range(len(b))), F(0))
                       for j in range(len(b[0]))) for i in range(len(a)))


def add(a, b):
    return tuple(tuple(x+y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))


def sub(a, b):
    return tuple(tuple(x-y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))


def transpose(a):
    return tuple(zip(*a))


class FunctionalRouteTests(unittest.TestCase):
    def check_route(self, route):
        g = analyze_route(route); n = g.n
        mats = dense_operators(g)
        A, E, D, N, C, B = (mats[x] for x in ('A','E','D','N','C','F'))
        I = identity(n); Z = tuple(tuple(F(0) for _ in range(n)) for _ in range(n))
        self.assertEqual(mul(A,D), E)
        self.assertEqual(mul(D,A), E)
        self.assertEqual(mul(mul(D,A),D), D)
        self.assertEqual(mul(E,E), E)
        self.assertEqual(mul(C,N), Z)
        self.assertEqual(mul(N,C), Z)
        self.assertEqual(add(C,N), A)
        Ap = [I]
        for _ in range(g.index + 1): Ap.append(mul(Ap[-1], A))
        self.assertEqual(mul(Ap[g.index+1],D), Ap[g.index])
        if g.index:
            self.assertNotEqual(mul(Ap[g.index],D), Ap[g.index-1])
        total = E
        for i, S in enumerate(mats['shells']):
            total = add(total,S)
            self.assertEqual(mul(S,S), S)
            self.assertEqual(mul(E,S), Z)
            self.assertEqual(mul(S,E), Z)
            self.assertEqual(sum(S[j][j] for j in range(n)), g.shell_ranks[i])
            self.assertEqual(mul(S,Ap[i+1]), Z)
            M = power_pinv_apply(g, i, I)
            self.assertEqual(mul(mul(S,Ap[i]),mul(M,B)), S)
            for j,T in enumerate(mats['shells']):
                if i != j: self.assertEqual(mul(S,T), Z)
                if j >= i: self.assertEqual(mul(mul(S,A),T), Z)
        self.assertEqual(total, I)
        Nm = I
        for m in range(g.index+2):
            M = power_pinv_apply(g,m,I)
            self.assertEqual(mul(mul(Nm,M),Nm), Nm)
            self.assertEqual(mul(mul(M,Nm),M), M)
            self.assertEqual(transpose(mul(Nm,M)),mul(Nm,M))
            self.assertEqual(transpose(mul(M,Nm)),mul(M,Nm))
            Nm = mul(Nm,N)
        self.assertEqual(sum(g.shell_ranks), n-len(g.recurrent))

    def test_all_routes_up_to_four(self):
        for n in range(1,5):
            for f in itertools.product(range(n), repeat=n):
                with self.subTest(f=f): self.check_route(f)

    def test_mixed_cycles_and_trees(self):
        for f in ([1,0,0,2,5,4,5,6], [1,2,0,2,3,4], [0,0,1,1,2,4,4,5]):
            self.check_route(f)

    def test_siblings_are_not_depth_shells(self):
        g=analyze_route([0,0,1,1]); m=dense_operators(g)
        self.assertEqual(g.entry_depth_counts,(1,2))
        self.assertEqual(g.shell_ranks,(2,1))
        contrast=((F(0),F(0),F(1),F(-1)),)
        self.assertEqual(mul(contrast,m['A']),((F(0),)*4,))
        self.assertEqual(mul(contrast,m['shells'][0]),contrast)

    def test_causal_supports_need_not_commute(self):
        g=analyze_route([0,0,1,2]); N=dense_operators(g)['N'];M=power_pinv_apply(g,1,identity(4))
        P,Q=mul(N,M),mul(M,N)
        self.assertNotEqual(mul(P,Q),mul(Q,P))
        K=sub(P,Q);K2=mul(K,K)
        self.assertNotEqual(mul(K2,K2),K2)

    def test_index_one_zero_nilpotent(self):
        g=analyze_route([0,0]);m=dense_operators(g)
        self.assertEqual(g.index,1)
        self.assertEqual(m['N'],((F(0),F(0)),(F(0),F(0))))
        self.assertNotEqual(m['F'],m['N'])
        self.assertNotEqual(m['D'],transpose(m['C']))

    def test_reject_invalid(self):
        for route in ([],[-1],[1],[0,2],[0,.5],[True]):
            with self.subTest(route=route),self.assertRaises(ValueError): analyze_route(route)


if __name__=='__main__': unittest.main()

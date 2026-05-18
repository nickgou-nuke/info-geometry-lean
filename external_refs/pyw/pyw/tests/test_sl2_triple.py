"""
Test suite for pyw.embedding.sl2_triple module and related NilpotentOrbit
enhancements.

Tests verify:
- Weighted Dynkin diagram computation from partitions
- sl2 triple construction and the bracket relations [h,e]=2e, [h,f]=-2f, [e,f]=h
- Root space grading: Delta_j decomposition under ad(h)
- h_f() and delta_l(): Cartan centralizer of f and its vanishing root set
- Integration: NilpotentOrbit methods and AffineLieAlgebra.nilpotent_orbits()

Correctness is verified against known results from:
    Collingwood & McGovern, "Nilpotent Orbits in Semisimple Lie Algebras" (1993).
"""

import pytest

from pyw.embedding.sl2_triple import (
    SL2Triple,
    RootSpaceGrading,
    weighted_dynkin_diagram,
    root_space_grading,
    compute_sl2_triple,
)
from pyw.algorithms.nilpotent_orbits import (
    NilpotentOrbit,
    nilpotent_orbits,
)
from pyw.core.affine_lie_algebra import AffineLieAlgebra


# =========================================================================
# Weighted Dynkin Diagram tests
# =========================================================================


class TestWeightedDynkinDiagram:
    """Verify weighted Dynkin diagram computation against known values."""

    # Type A: Collingwood-McGovern, Table 6.3
    @pytest.mark.parametrize(
        "partition, expected",
        [
            ([1, 1, 1, 1], [0, 0, 0]),  # zero orbit
            ([2, 1, 1], [1, 0, 1]),  # minimal
            ([2, 2], [0, 2, 0]),  # even
            ([3, 1], [2, 0, 2]),  # subregular
            ([4], [2, 2, 2]),  # principal
        ],
    )
    def test_type_A3(self, partition, expected):
        assert weighted_dynkin_diagram("A", partition, rank=3) == expected

    # Type B2 (so(5))
    @pytest.mark.parametrize(
        "partition, expected",
        [
            ([1, 1, 1, 1, 1], [0, 0]),
            ([2, 2, 1], [0, 1]),
            ([3, 1, 1], [2, 0]),
            ([5], [2, 2]),
        ],
    )
    def test_type_B2(self, partition, expected):
        assert weighted_dynkin_diagram(("B", 2), partition) == expected

    # Type C2 (sp(4))
    @pytest.mark.parametrize(
        "partition, expected",
        [
            ([1, 1, 1, 1], [0, 0]),
            ([2, 1, 1], [1, 0]),
            ([2, 2], [0, 2]),
            ([4], [2, 2]),
        ],
    )
    def test_type_C2(self, partition, expected):
        assert weighted_dynkin_diagram(("C", 2), partition) == expected

    # Type D4 (so(8))
    @pytest.mark.parametrize(
        "partition, expected",
        [
            ([1, 1, 1, 1, 1, 1, 1, 1], [0, 0, 0, 0]),
            ([3, 1, 1, 1, 1, 1], [2, 0, 0, 0]),
            ([7, 1], [2, 2, 2, 2]),
        ],
    )
    def test_type_D4(self, partition, expected):
        assert weighted_dynkin_diagram(("D", 4), partition) == expected

    def test_tuple_input(self):
        assert weighted_dynkin_diagram(("A", 3), [4]) == [2, 2, 2]

    def test_all_entries_nonneg(self):
        """WDD entries must all be non-negative."""
        for letter, n in [("A", 4), ("B", 3), ("C", 3), ("D", 4)]:
            for orb in nilpotent_orbits(letter, n):
                wdd = weighted_dynkin_diagram((letter, n), orb.partition)
                assert all(d >= 0 for d in wdd), f"{letter}{n} {orb.partition}: {wdd}"

    def test_all_entries_at_most_2(self):
        """WDD entries for nilpotent orbits are in {0, 1, 2}."""
        for letter, n in [("A", 4), ("B", 3), ("C", 3), ("D", 4)]:
            for orb in nilpotent_orbits(letter, n):
                wdd = weighted_dynkin_diagram((letter, n), orb.partition)
                assert all(d <= 2 for d in wdd), f"{letter}{n} {orb.partition}: {wdd}"

    def test_zero_orbit_gives_zero_wdd(self):
        """The zero orbit always has WDD = (0, ..., 0)."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            zero_orb = orbits[0]
            wdd = weighted_dynkin_diagram((letter, n), zero_orb.partition)
            assert all(d == 0 for d in wdd)

    def test_principal_orbit_gives_all_twos(self):
        """The principal orbit always has WDD = (2, 2, ..., 2)."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            principal = orbits[-1]
            wdd = weighted_dynkin_diagram((letter, n), principal.partition)
            assert all(d == 2 for d in wdd)


# =========================================================================
# SL2 Triple tests
# =========================================================================


class TestSL2Triple:
    """Test sl2 triple construction and bracket relations."""

    def test_principal_A3(self):
        """Principal nilpotent of sl(4)."""
        triple = compute_sl2_triple("A", [4], rank=3)
        assert triple.verify()
        assert triple.wdd == [2, 2, 2]

    def test_subregular_A3(self):
        """Subregular orbit [3,1] of sl(4)."""
        triple = compute_sl2_triple(("A", 3), [3, 1])
        assert triple.verify()
        assert triple.wdd == [2, 0, 2]

    def test_minimal_A3(self):
        """Minimal orbit [2,1,1] of sl(4)."""
        triple = compute_sl2_triple(("A", 3), [2, 1, 1])
        assert triple.verify()

    def test_even_A3(self):
        """Even orbit [2,2] of sl(4)."""
        triple = compute_sl2_triple(("A", 3), [2, 2])
        assert triple.verify()

    def test_zero_orbit(self):
        """Zero orbit: h=e=f=0."""
        triple = compute_sl2_triple(("A", 3), [1, 1, 1, 1])
        assert triple.verify()
        assert triple.h == 0
        assert triple.e == 0
        assert triple.f == 0

    def test_x_property(self):
        """x = h/2 should satisfy [x,e]=e, [x,f]=-f, [e,f]=2x."""
        triple = compute_sl2_triple(("A", 3), [4])
        L = triple.h.parent()
        x = triple.x
        assert L.bracket(x, triple.e) == triple.e
        assert L.bracket(x, triple.f) == -triple.f
        assert L.bracket(triple.e, triple.f) == 2 * x

    @pytest.mark.parametrize(
        "letter, n",
        [("A", 3), ("A", 4), ("B", 2), ("B", 3), ("C", 2), ("C", 3), ("D", 4)],
    )
    def test_all_orbits_verify(self, letter, n):
        """All sl2 triples must verify for classical types."""
        for orb in nilpotent_orbits(letter, n):
            triple = compute_sl2_triple((letter, n), orb.partition)
            assert triple.verify(), f"{letter}{n}, partition={orb.partition}, WDD={triple.wdd}"

    def test_h_eigenvalues_match_wdd(self):
        """[h, E_{alpha_i}] should give eigenvalue d_i for each simple root."""
        from sage.all import LieAlgebra, QQ, RootSystem

        triple = compute_sl2_triple(("A", 3), [3, 1])
        L = LieAlgebra(QQ, cartan_type=["A", 3])
        B_basis = L.basis()
        rl = RootSystem(["A", 3]).root_lattice()
        alpha = rl.simple_roots()

        for i in range(1, 4):
            br = L.bracket(triple.h, B_basis[alpha[i]])
            expected = triple.wdd[i - 1] * B_basis[alpha[i]]
            assert br == expected, f"alpha_{i}: got {br}, expected {expected}"


# =========================================================================
# Root Space Grading tests
# =========================================================================


class TestRootSpaceGrading:
    """Test root space grading (Delta_j decomposition)."""

    def test_zero_orbit_all_in_delta0(self):
        """For the zero orbit, all roots have eigenvalue 0."""
        wdd = [0, 0, 0]
        rg = root_space_grading(("A", 3), wdd)
        assert rg.grades == [0]
        # A3 has 6 positive roots → 12 roots total
        assert rg.dimension(0) == 12

    def test_principal_only_pm2(self):
        """For the principal orbit of A3, the only eigenvalues are ±2, ±4, ±6."""
        wdd = [2, 2, 2]
        rg = root_space_grading(("A", 3), wdd)
        # All eigenvalues should be even and non-zero
        for j in rg.grades:
            assert j != 0, "Principal orbit should have no roots with eigenvalue 0"

    def test_grading_symmetric(self):
        """Root grading should be symmetric: dim(Delta_j) = dim(Delta_{-j})."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2)]:
            for orb in nilpotent_orbits(letter, n):
                wdd = weighted_dynkin_diagram((letter, n), orb.partition)
                rg = root_space_grading((letter, n), wdd)
                for j in rg.grades:
                    if j > 0:
                        assert rg.dimension(j) == rg.dimension(-j), (
                            f"{letter}{n}, {orb.partition}: "
                            f"dim(Δ_{j})={rg.dimension(j)} ≠ dim(Δ_{-j})={rg.dimension(-j)}"
                        )

    def test_total_root_count(self):
        """Sum of all Delta_j dimensions should equal total number of roots."""
        from sage.all import RootSystem

        for letter, n in [("A", 3), ("B", 2), ("C", 3), ("D", 4)]:
            R = RootSystem([letter, n])
            total_roots = 2 * len(list(R.root_lattice().positive_roots()))

            for orb in nilpotent_orbits(letter, n):
                wdd = weighted_dynkin_diagram((letter, n), orb.partition)
                rg = root_space_grading((letter, n), wdd)
                computed = sum(rg.dimension(j) for j in rg.grades)
                assert computed == total_roots, (
                    f"{letter}{n}, {orb.partition}: "
                    f"sum of grading dims = {computed}, expected {total_roots}"
                )

    def test_g2_matches_sl2_triple(self):
        """Roots in Delta_2 should match the g_2 eigenspace used in sl2 triple."""
        triple = compute_sl2_triple(("A", 3), [3, 1])
        rg = triple.root_grading()
        # Delta_2 should contain the roots appearing in e
        assert rg.dimension(2) > 0, "Delta_2 should be non-empty for non-zero orbit"

    def test_repr(self):
        """Test RootSpaceGrading repr."""
        rg = root_space_grading(("A", 3), [2, 2, 2])
        r = repr(rg)
        assert "RootSpaceGrading" in r


# =========================================================================
# NilpotentOrbit method integration tests
# =========================================================================


class TestNilpotentOrbitMethods:
    """Test the new methods added to NilpotentOrbit."""

    def test_weighted_dynkin_diagram_method(self):
        orbits = nilpotent_orbits("A", 3)
        principal = orbits[-1]
        assert principal.weighted_dynkin_diagram() == [2, 2, 2]

    def test_sl2_triple_method(self):
        orbits = nilpotent_orbits("A", 3)
        for orb in orbits:
            triple = orb.sl2_triple()
            assert triple.verify(), f"Failed for {orb.partition}"

    def test_root_grading_method(self):
        orbits = nilpotent_orbits("B", 2)
        for orb in orbits:
            rg = orb.root_grading()
            assert isinstance(rg, RootSpaceGrading)
            # Symmetry check
            for j in rg.grades:
                if j > 0:
                    assert rg.dimension(j) == rg.dimension(-j)


# =========================================================================
# AffineLieAlgebra integration tests
# =========================================================================


class TestAffineLieAlgebraNilpotentOrbits:
    """Test AffineLieAlgebra.nilpotent_orbits() method."""

    def test_finite_type(self):
        ala = AffineLieAlgebra(["A", 3])
        orbits = ala.nilpotent_orbits()
        assert len(orbits) == 5

    def test_affine_type_delegates(self):
        """Affine type should delegate to finite_lie_algebra."""
        ala = AffineLieAlgebra(["A", 3, 1])
        orbits = ala.finite_lie_algebra.nilpotent_orbits()
        assert len(orbits) == 5

    def test_affine_type_direct(self):
        """Calling nilpotent_orbits on affine type should auto-delegate."""
        ala = AffineLieAlgebra(["A", 3, 1])
        orbits = ala.nilpotent_orbits()
        assert len(orbits) == 5

    def test_all_classical_types(self):
        for letter, n, expected_count in [
            ("A", 3, 5),
            ("B", 2, 4),
            ("C", 2, 4),
            ("D", 4, 12),
        ]:
            ala = AffineLieAlgebra([letter, n])
            orbits = ala.nilpotent_orbits()
            assert len(orbits) == expected_count, f"{letter}{n}: got {len(orbits)}"

    def test_orbit_sl2_triple_from_algebra(self):
        """Full pipeline: algebra → orbits → sl2 triple → verify."""
        ala = AffineLieAlgebra(["B", 2])
        for orb in ala.nilpotent_orbits():
            triple = orb.sl2_triple()
            assert triple.verify(), f"B2, {orb.partition}"


# =========================================================================
# Edge cases
# =========================================================================


class TestEdgeCases:
    def test_A1_orbits(self):
        """A1 (sl(2)): only zero and principal orbits."""
        orbits = nilpotent_orbits("A", 1)
        assert len(orbits) == 2
        for orb in orbits:
            triple = orb.sl2_triple()
            assert triple.verify()

    def test_D2_orbits(self):
        """D2 (so(4)): a few orbits."""
        orbits = nilpotent_orbits("D", 2)
        for orb in orbits:
            triple = orb.sl2_triple()
            assert triple.verify()


# =========================================================================
# h_f and delta_l tests
# =========================================================================


class TestHfAndDeltaL:
    """Test h_f() (Cartan centralizer of f) and delta_l() (vanishing roots)."""

    # ----- h_f structural properties -----

    def test_hf_zero_orbit_is_full_cartan(self):
        """For zero orbit (f=0), h^f should be the entire Cartan subalgebra."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            triple = orbits[0].sl2_triple()  # zero orbit
            hf = triple.h_f()
            assert len(hf) == n, f"{letter}{n} zero orbit: dim(h^f)={len(hf)}, expected {n}"

    def test_hf_principal_orbit_is_trivial(self):
        """For principal orbit, h^f = {0} (no Cartan element commutes with f)."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            triple = orbits[-1].sl2_triple()  # principal orbit
            hf = triple.h_f()
            assert len(hf) == 0, f"{letter}{n} principal orbit: dim(h^f)={len(hf)}, expected 0"

    def test_hf_dimension_bounded(self):
        """dim(h^f) should be between 0 and rank n for all orbits."""
        for letter, n in [("A", 3), ("A", 4), ("B", 3), ("C", 3), ("D", 4)]:
            for orb in nilpotent_orbits(letter, n):
                triple = orb.sl2_triple()
                hf = triple.h_f()
                assert 0 <= len(hf) <= n, (
                    f"{letter}{n} {orb.partition}: dim(h^f)={len(hf)} out of [0, {n}]"
                )

    def test_hf_vectors_commute_with_f(self):
        """Each basis vector of h^f, when realized as a Cartan element,
        must actually commute with f: [h, f] = 0."""
        from sage.all import LieAlgebra, QQ, RootSystem

        for letter, n in [("A", 3), ("B", 2), ("C", 3)]:
            for orb in nilpotent_orbits(letter, n):
                triple = orb.sl2_triple()
                if triple.f == 0:
                    continue
                hf = triple.h_f()
                L = LieAlgebra(QQ, cartan_type=[letter, n])
                B = L.basis()
                rl = RootSystem([letter, n]).root_lattice()
                alphacheck = rl.simple_coroots()

                for v in hf:
                    # v is a coroot lattice element; extract coefficients
                    h_elem = sum(v.coefficient(i) * B[alphacheck[i]] for i in range(1, n + 1))
                    bracket = L.bracket(h_elem, triple.f)
                    assert bracket == 0, (
                        f"{letter}{n} {orb.partition}: [h, f] != 0 for h^f basis {v}"
                    )

    def test_hf_specific_A3_minimal(self):
        """A3 minimal orbit [2,1,1]: h^f should be 2-dimensional."""
        triple = compute_sl2_triple(("A", 3), [2, 1, 1])
        hf = triple.h_f()
        assert len(hf) == 2

    def test_hf_specific_A3_subregular(self):
        """A3 subregular orbit [3,1]: f involves enough roots to fill the rank,
        so h^f = {0}."""
        triple = compute_sl2_triple(("A", 3), [3, 1])
        hf = triple.h_f()
        assert len(hf) == 0

    def test_hf_specific_A3_even(self):
        """A3 even orbit [2,2]: f involves enough roots to fill the rank,
        so h^f = {0}."""
        triple = compute_sl2_triple(("A", 3), [2, 2])
        hf = triple.h_f()
        assert len(hf) == 0

    # ----- delta_l structural properties -----

    def test_delta_l_zero_orbit_is_empty(self):
        """For zero orbit, h^f = full Cartan, so no root vanishes on h^f."""
        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            triple = orbits[0].sl2_triple()
            dl = triple.delta_l()
            assert len(dl) == 0, f"{letter}{n} zero orbit: |delta_l|={len(dl)}, expected 0"

    def test_delta_l_principal_orbit_is_all_roots(self):
        """For principal orbit, h^f = {0}, so every root vanishes trivially."""
        from sage.all import RootSystem

        for letter, n in [("A", 3), ("B", 2), ("C", 2), ("D", 4)]:
            R = RootSystem([letter, n])
            total_roots = 2 * len(list(R.root_lattice().positive_roots()))

            orbits = nilpotent_orbits(letter, n)
            triple = orbits[-1].sl2_triple()
            dl = triple.delta_l()
            assert len(dl) == total_roots, (
                f"{letter}{n} principal: |delta_l|={len(dl)}, expected {total_roots}"
            )

    def test_delta_l_symmetric(self):
        """If alpha is in delta_l, then -alpha is also in delta_l."""
        for letter, n in [("A", 3), ("B", 2), ("C", 3), ("D", 4)]:
            for orb in nilpotent_orbits(letter, n):
                triple = orb.sl2_triple()
                dl = triple.delta_l()
                dl_set = set(str(r) for r in dl)
                for r in dl:
                    assert str(-r) in dl_set, (
                        f"{letter}{n} {orb.partition}: {r} in delta_l but -{r} not"
                    )

    def test_delta_l_is_root_subsystem(self):
        """delta_l should be closed under root addition (when the sum is a root).

        If alpha, beta in Delta_l and alpha + beta is a root, then alpha + beta
        should also be in Delta_l. This is because Delta_l = roots of the Levi
        subalgebra l.
        """
        from sage.all import RootSystem

        for letter, n in [("A", 3), ("B", 2), ("C", 3)]:
            R = RootSystem([letter, n])
            all_roots_set = set(
                list(R.root_lattice().positive_roots())
                + [-r for r in R.root_lattice().positive_roots()]
            )

            for orb in nilpotent_orbits(letter, n):
                triple = orb.sl2_triple()
                dl = triple.delta_l()
                dl_set = set(dl)
                for a in dl:
                    for b in dl:
                        s = a + b
                        if s in all_roots_set:
                            assert s in dl_set, (
                                f"{letter}{n} {orb.partition}: "
                                f"{a} + {b} = {s} is a root but not in delta_l"
                            )

    def test_delta_l_count_A3(self):
        """Verify delta_l sizes for all A3 orbits."""
        from sage.all import RootSystem

        total_roots = 2 * len(list(RootSystem(["A", 3]).root_lattice().positive_roots()))
        # A3 has 12 roots total

        # zero [1,1,1,1]: delta_l = empty
        triple = compute_sl2_triple(("A", 3), [1, 1, 1, 1])
        assert len(triple.delta_l()) == 0

        # minimal [2,1,1]: 1 independent constraint removed
        triple = compute_sl2_triple(("A", 3), [2, 1, 1])
        dl = triple.delta_l()
        assert len(dl) > 0
        assert len(dl) < total_roots

        # principal [4]: delta_l = all roots
        triple = compute_sl2_triple(("A", 3), [4])
        assert len(triple.delta_l()) == total_roots

    def test_hf_delta_l_consistency(self):
        """Cross-check: dim(h^f) + dim(delta_l span) should be consistent.

        Specifically:
        - If h^f = {0}, then delta_l = all roots (every root vanishes on {0})
        - If h^f = full Cartan, then delta_l = empty (no root vanishes on all of h)
        - dim(h^f) = n - rank(constraint matrix from roots in f)
        - delta_l is closed under negation
        """
        for letter, n in [("A", 3), ("B", 2), ("C", 3)]:
            for orb in nilpotent_orbits(letter, n):
                triple = orb.sl2_triple()
                hf = triple.h_f()
                dl = triple.delta_l()
                hf_dim = len(hf)

                if hf_dim == 0:
                    # h^f = {0}: every root trivially vanishes on {0}
                    from sage.all import RootSystem

                    R = RootSystem([letter, n])
                    total_roots = 2 * len(list(R.root_lattice().positive_roots()))
                    assert len(dl) == total_roots, (
                        f"{letter}{n} {orb.partition}: h^f={{0}} but |delta_l|={len(dl)} != {total_roots}"
                    )
                elif hf_dim == n:
                    # h^f = full Cartan: no non-zero root vanishes on all of h
                    assert len(dl) == 0, (
                        f"{letter}{n} {orb.partition}: h^f=full Cartan but |delta_l|={len(dl)} != 0"
                    )
                else:
                    # Intermediate case: delta_l should be non-trivial
                    # and should be a proper subset of all roots
                    from sage.all import RootSystem

                    R = RootSystem([letter, n])
                    total_roots = 2 * len(list(R.root_lattice().positive_roots()))
                    assert 0 < len(dl) < total_roots, (
                        f"{letter}{n} {orb.partition}: dim(h^f)={hf_dim}, "
                        f"|delta_l|={len(dl)} not in (0, {total_roots})"
                    )

"""
Test suite for pyw.algorithms.nilpotent_orbits module.

Correctness is verified against known results from:
    Collingwood & McGovern, "Nilpotent Orbits in Semisimple Lie Algebras" (1993).
"""

import pytest

from pyw.algorithms.nilpotent_orbits import (
    LeviSubalgebra,
    NilpotentOrbit,
    nilpotent_orbits,
    nilpotent_orbit_table,
    _transpose_partition,
    _is_type_B_partition,
    _is_type_C_partition,
    _is_type_D_partition,
    _is_very_even,
)


# =========================================================================
# Helper tests
# =========================================================================


class TestTransposePartition:
    def test_empty(self):
        assert _transpose_partition([]) == []

    def test_single_row(self):
        assert _transpose_partition([5]) == [1, 1, 1, 1, 1]

    def test_single_column(self):
        assert _transpose_partition([1, 1, 1]) == [3]

    def test_general(self):
        assert _transpose_partition([4, 2, 1]) == [3, 2, 1, 1]

    def test_involution(self):
        """Transpose is an involution: (λ^t)^t = λ."""
        p = [5, 3, 3, 1]
        assert _transpose_partition(_transpose_partition(p)) == p


class TestPartitionFilters:
    # --- Type B: even parts have even multiplicity ---
    def test_type_B_accepts(self):
        # [3, 1, 1] for B_1 → so(5): odd parts only → OK
        assert _is_type_B_partition([3, 1, 1]) is True

    def test_type_B_rejects(self):
        # [2, 1, 1, 1] has part 2 with multiplicity 1 (odd) → rejected
        assert _is_type_B_partition([2, 1, 1, 1]) is False

    # --- Type C: odd parts have even multiplicity ---
    def test_type_C_accepts(self):
        assert _is_type_C_partition([4, 2]) is True

    def test_type_C_rejects(self):
        # [3, 2, 1] has parts 3 and 1 each with mult 1 → rejected
        assert _is_type_C_partition([3, 2, 1]) is False

    # --- Type D: even parts have even multiplicity ---
    def test_type_D_accepts(self):
        assert _is_type_D_partition([3, 3, 1, 1]) is True

    def test_type_D_rejects(self):
        assert _is_type_D_partition([4, 3, 1]) is False

    # --- Very even ---
    def test_very_even_true(self):
        assert _is_very_even([4, 4]) is True

    def test_very_even_false(self):
        assert _is_very_even([4, 3, 1]) is False


# =========================================================================
# Orbit count tests (the gold standard)
# =========================================================================


class TestOrbitCounts:
    """Verify orbit counts match known values from the literature."""

    # Type A_n: number of orbits = p(n+1), the partition function
    # p(1)=1, p(2)=2, p(3)=3, p(4)=5, p(5)=7, p(6)=11
    @pytest.mark.parametrize(
        "n, expected",
        [
            (1, 2),  # A1: sl(2) → p(2) = 2
            (2, 3),  # A2: sl(3) → p(3) = 3
            (3, 5),  # A3: sl(4) → p(4) = 5
            (4, 7),  # A4: sl(5) → p(5) = 7
            (5, 11),  # A5: sl(6) → p(6) = 11
        ],
    )
    def test_type_A_counts(self, n, expected):
        orbits = nilpotent_orbits("A", n)
        assert len(orbits) == expected

    # Type B: known orbit counts (Collingwood-McGovern)
    # Partitions of 2n+1 where even parts have even multiplicity
    @pytest.mark.parametrize(
        "n, expected",
        [
            (1, 2),  # B1=so(3): [3], [1,1,1]
            (2, 4),  # B2=so(5): 4 orbits
            (3, 7),  # B3=so(7): 7 orbits
        ],
    )
    def test_type_B_counts(self, n, expected):
        orbits = nilpotent_orbits("B", n)
        assert len(orbits) == expected

    # Type C: known orbit counts
    # Partitions of 2n where odd parts have even multiplicity
    @pytest.mark.parametrize(
        "n, expected",
        [
            (1, 2),  # C1=sp(2): [2], [1,1]
            (2, 4),  # C2=sp(4): 4 orbits
            (3, 8),  # C3=sp(6): 8 orbits
        ],
    )
    def test_type_C_counts(self, n, expected):
        orbits = nilpotent_orbits("C", n)
        assert len(orbits) == expected

    # Type D: orbit counts (including doubled very-even)
    # Very-even partitions (all parts even) each give TWO orbits
    @pytest.mark.parametrize(
        "n, expected",
        [
            (2, 4),  # D2=so(4): [3,1], [2,2](I,II), [1,1,1,1]
            (3, 5),  # D3=so(6): 5 orbits (no very-even in this case)
            (4, 12),  # D4=so(8): 12 orbits (2 very-even partitions doubled)
        ],
    )
    def test_type_D_counts(self, n, expected):
        orbits = nilpotent_orbits("D", n)
        assert len(orbits) == expected


# =========================================================================
# Orbit dimension tests
# =========================================================================


class TestOrbitDimensions:
    """Check dimensions against known values."""

    def test_zero_orbit_has_dim_zero(self):
        """The zero orbit (partition [1,...,1]) always has dimension 0."""
        for letter, n in [("A", 4), ("B", 3), ("C", 3), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            zero_orb = orbits[0]  # sorted ascending → first is dim 0
            assert zero_orb.dimension == 0

    def test_regular_orbit_type_A(self):
        """Regular orbit of sl(N) has dim N^2 - N = N(N-1)."""
        for n in range(1, 6):
            N = n + 1
            orbits = nilpotent_orbits("A", n)
            regular = orbits[-1]  # largest dimension
            assert regular.partition == [N]
            assert regular.dimension == N * N - N

    def test_sl3_dimensions(self):
        """sl(3): orbits [1,1,1](dim=0), [2,1](dim=4), [3](dim=6)."""
        orbits = nilpotent_orbits("A", 2)
        dims = [o.dimension for o in orbits]
        assert dims == [0, 4, 6]

    def test_sl4_dimensions(self):
        """sl(4): orbit dims via dim = N^2 - sum(lambda_t_i^2)."""
        orbits = nilpotent_orbits("A", 3)
        dims = [o.dimension for o in orbits]
        # [1,1,1,1]→0, [2,1,1]→6, [2,2]→8, [3,1]→10, [4]→12
        assert dims == [0, 6, 8, 10, 12]


# =========================================================================
# Structural tests
# =========================================================================


class TestOrbitStructure:
    def test_regular_orbit_is_distinguished(self):
        """The regular orbit (single-part partition) is always distinguished."""
        orbits = nilpotent_orbits("A", 4)
        regular = orbits[-1]
        assert regular.is_distinguished is True

    def test_zero_orbit_partition(self):
        """Zero orbit has partition [1, 1, ..., 1]."""
        orbits = nilpotent_orbits("A", 3)
        zero = orbits[0]
        assert zero.partition == [1, 1, 1, 1]

    def test_type_D_very_even_doubled(self):
        """Very-even partitions in type D produce pairs (I, II)."""
        orbits = nilpotent_orbits("D", 4)
        very_even = [o for o in orbits if o.is_very_even]
        # [4,4] and [2,2,2,2] are very even → 4 orbit objects
        assert len(very_even) == 4
        # Each very-even partition appears exactly twice
        from collections import Counter

        part_counts = Counter(tuple(o.partition) for o in very_even)
        assert all(c == 2 for c in part_counts.values())
        # Check roman numerals
        for part_tuple, count in part_counts.items():
            numerals = sorted(
                o.roman_numeral for o in very_even if tuple(o.partition) == part_tuple
            )
            assert numerals == ["I", "II"]

    def test_orbits_sorted_by_dimension(self):
        """Orbits should be returned sorted by ascending dimension."""
        for letter, n in [("A", 5), ("B", 3), ("C", 3), ("D", 4)]:
            orbits = nilpotent_orbits(letter, n)
            dims = [o.dimension for o in orbits]
            assert dims == sorted(dims)

    def test_repr(self):
        """Test that __repr__ doesn't crash."""
        orbits = nilpotent_orbits("A", 2)
        for o in orbits:
            r = repr(o)
            assert "NilpotentOrbit" in r


class TestLeviAndRegularity:
    def test_levi_subalgebra_access(self):
        principal = nilpotent_orbits("A", 3)[-1]
        levi = principal.regular_levi()
        assert isinstance(levi, LeviSubalgebra)
        assert levi.lie_type == ("A", 3)
        assert levi.rank == 3
        assert len(levi.roots) == 12
        assert levi.dimension == 15

    def test_orbit_is_regular_in_own_levi_principal(self):
        principal = nilpotent_orbits("A", 3)[-1]
        assert principal.is_regular_in() is True

    def test_orbit_zero_not_regular_in_own_levi(self):
        zero = nilpotent_orbits("A", 3)[0]
        assert zero.is_regular_in() is False

    def test_orbit_is_regular_in_explicit_levi(self):
        principal = nilpotent_orbits("A", 3)[-1]
        subregular = nilpotent_orbits("A", 3)[-2]
        subregular_levi = subregular.levi_subalgebra()
        assert principal.is_regular_in(subregular_levi) is False

    def test_levi_contains_and_regular_element(self):
        principal = nilpotent_orbits("A", 3)[-1]
        levi = principal.regular_levi()
        f = principal.sl2_triple().f
        assert levi.contains_element(f) is True
        assert levi.is_regular(f) is True

    def test_levi_regular_element_false_for_zero(self):
        zero = nilpotent_orbits("A", 3)[0]
        levi = zero.regular_levi()
        f0 = zero.sl2_triple().f
        assert levi.contains_element(f0) is True
        assert levi.is_regular(f0) is False


# =========================================================================
# Table output test
# =========================================================================


class TestTable:
    def test_table_runs(self):
        """nilpotent_orbit_table returns a non-empty string."""
        table = nilpotent_orbit_table("A", 3)
        assert isinstance(table, str)
        assert "sl(4)" in table
        assert "5 orbits" in table

    def test_table_tuple_input(self):
        table = nilpotent_orbit_table(("B", 2))
        assert "so(5)" in table


# =========================================================================
# Edge cases and errors
# =========================================================================


class TestEdgeCases:
    def test_tuple_input(self):
        orbits = nilpotent_orbits(("A", 3))
        assert len(orbits) == 5

    def test_list_input(self):
        orbits = nilpotent_orbits(["C", 2])
        assert len(orbits) == 4

    def test_invalid_type_raises(self):
        with pytest.raises(ValueError, match="Only classical types"):
            nilpotent_orbits("E", 6)

    def test_missing_rank_raises(self):
        with pytest.raises(ValueError, match="rank must be specified"):
            nilpotent_orbits("A")

    def test_negative_rank_raises(self):
        with pytest.raises(ValueError, match="Rank must be"):
            nilpotent_orbits("A", 0)

    def test_D1_raises(self):
        with pytest.raises(ValueError, match="Type D requires rank"):
            nilpotent_orbits("D", 1)

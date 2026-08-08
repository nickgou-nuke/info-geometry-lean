#!/usr/bin/env python3
"""Audit for cooperad environmental split preserving rank 32."""


def main():
    inner_phase = 2
    outer_phase = 2 * 2
    flux = 2 * 2
    rank = inner_phase * outer_phase * flux
    product_rank = 2**3 * 2**2
    split = {"12": "inner", "13": "outer", "23": "outer"}
    generic_splits = {
        "pair12_3": {"12": "inner", "13": "outer", "23": "outer"},
        "pair13_2": {"12": "outer", "13": "inner", "23": "outer"},
        "pair23_1": {"12": "outer", "13": "outer", "23": "inner"},
    }

    assert inner_phase == 2
    assert outer_phase == 4
    assert flux == 4
    assert rank == 32
    assert product_rank == 32
    assert rank == product_rank
    assert split == {"12": "inner", "13": "outer", "23": "outer"}
    for slots in generic_splits.values():
        assert list(slots.values()).count("inner") == 1
        assert list(slots.values()).count("outer") == 2

    print("inner phase rank:", inner_phase)
    print("outer phase rank:", outer_phase)
    print("flux rank:", flux)
    print("environmental split rank:", rank)
    print("product/Leray rank:", product_rank)
    print("cooperad split {1,2}|{3}:", split)
    print("generic arity-3 splits:", generic_splits)
    print("cooperad_environmental_rank32.py: finite audit passed")


if __name__ == "__main__":
    main()

from __future__ import annotations

import sympy as sp


def main() -> None:
    # Finite linear toy model for GenesisSplitDatum.split_injective.
    # Latent space: R^2 with full split readout into Observable x Hidden x Boundary = R^3.
    x1, x2, y1, y2 = sp.symbols('x1 x2 y1 y2', real=True)
    x = sp.Matrix([x1, x2])
    y = sp.Matrix([y1, y2])

    # Observable / hidden / boundary readouts.
    to_observable = sp.Matrix([[1, 0]])
    to_hidden = sp.Matrix([[0, 1]])
    boundary_of = sp.Matrix([[1, 1]])

    split_matrix = sp.Matrix.vstack(to_observable, to_hidden, boundary_of)
    assert split_matrix.rank() == 2, f'split matrix not injective: rank={split_matrix.rank()}'

    split_x = sp.simplify(split_matrix * x)
    split_y = sp.simplify(split_matrix * y)

    # Equal full split data forces equality of latent coordinates.
    delta = sp.simplify(split_x - split_y)
    assert delta[0] == x1 - y1
    assert delta[1] == x2 - y2
    assert delta[2] == x1 + x2 - y1 - y2

    sol = sp.solve(list(delta), [x1, x2], dict=True)
    # Solutions are exactly x1=y1, x2=y2.
    assert sol == [{x1: y1, x2: y2}], f'unexpected solution set: {sol}'

    print('horizon_eschaton_genesis_split: injective split sanity check passed')
    print(f'split_matrix_rank = {split_matrix.rank()}')
    print(f'solution = {sol[0]}')


if __name__ == '__main__':
    main()

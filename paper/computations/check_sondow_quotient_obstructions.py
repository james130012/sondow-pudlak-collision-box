"""Independently verify finite Sondow quotient-lattice obstructions.

Only standard-library integer arithmetic is used. Kernel construction, HNF,
LLL, rational inversion and the candidate generator are not trusted.
"""
import argparse
import json
from math import gcd, comb
from pathlib import Path
import sys

from check_sondow_n31_obstruction import source_column, primes_up_to, determinant_mod, dot

sys.set_int_max_str_digits(0)  # Exact local certificate integers can be very large.


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    assert a and b and len(a[0]) == len(b)
    bt = transpose(b)
    return [[dot(row, col) for col in bt] for row in a]


def determinant(a):
    """Fraction-free elimination with every division checked for exactness."""
    a = [row[:] for row in a]
    size = len(a)
    assert all(len(row) == size for row in a)
    if not size:
        return 1
    sign, previous = 1, 1
    for k in range(size - 1):
        pivot = next((i for i in range(k, size) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        current = a[k][k]
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                value = current * a[i][j] - a[i][k] * a[k][j]
                assert value % previous == 0
                a[i][j] = value // previous
            a[i][k] = 0
        previous = current
    return sign * a[-1][-1]


def require_matrix(a, rows, columns):
    assert len(a) == rows
    assert all(len(row) == columns and all(type(x) is int for x in row) for row in a)


def check(n, *, include_certificate=False):
    path = Path(__file__).with_name(f'sondow_quotient_obstruction_n{n}_20260905.json')
    data = json.loads(path.read_text())
    assert data['n'] == n and n >= 1
    basis = data['basis']
    dimension, m = len(basis), n + 1
    assert 2 <= dimension <= m
    require_matrix(basis, dimension, m)
    columns = [source_column(k) for k in range(n, 2 * n + 1)]
    primes = primes_up_to(4 * n)
    e = [[col[1].get(p, 0) for col in columns] for p in primes]
    assert all(dot(a, row) == 0 for a in basis for row in e)
    rank = data['rank_E']
    assert rank['order'] == m - dimension
    assert rank['prime'] == 1009 and 1009 in primes_up_to(1009)
    row_ids, col_ids = rank['rows'], rank['columns']
    assert len(row_ids) == len(set(row_ids)) == rank['order']
    assert len(col_ids) == len(set(col_ids)) == rank['order']
    assert all(0 <= i < len(e) for i in row_ids)
    assert all(0 <= j < m for j in col_ids)
    residue = determinant_mod([[e[i][j] for j in col_ids] for i in row_ids], 1009)
    assert residue == rank['determinant_mod_prime'] and residue != 0
    minor_gcd = 0
    for selected in data['saturation_minor_columns']:
        assert len(selected) == len(set(selected)) == dimension
        assert all(0 <= j < m for j in selected)
        minor_gcd = gcd(minor_gcd, determinant([[row[j] for j in selected] for row in basis]))
    assert minor_gcd == 1
    # Rank and the gcd-one minors prove that this is the full integer kernel.
    q, t = [col[2] for col in columns], [col[3] for col in columns]
    images = [[dot(a, q), dot(a, t)] for a in basis]
    u = data['image_change_rows']
    require_matrix(u, dimension, dimension)
    assert abs(determinant(u)) == 1
    h = multiply(u, images)
    assert all(row == [0, 0] for row in h[2:])
    image_index = abs(determinant(h[:2]))
    assert image_index > 0
    changed = multiply(u, basis)
    weights = [col[0] * 16 ** (n - j) for j, col in enumerate(columns)]
    weighted = [[x * w for x, w in zip(row, weights)] for row in changed]
    a, c = weighted[:2], weighted[2:]
    s = multiply(a, transpose(a))
    denominator = data['projection_denominator']
    assert type(denominator) is int and denominator > 0
    numerators = data['projection_numerators']
    require_matrix(numerators, dimension - 2, 2)
    if c:
        r = multiply(c, transpose(c))
        z = multiply(c, transpose(a))
        assert multiply(r, numerators) == [[denominator * x for x in row] for row in z]
        correction = multiply(transpose(z), numerators)
    else:
        correction = [[0, 0], [0, 0]]
    gram_numerator = [[denominator * s[i][j] - correction[i][j] for j in range(2)] for i in range(2)]
    assert gram_numerator[0][1] == gram_numerator[1][0]
    assert gram_numerator[0][0] > 0 and determinant(gram_numerator) > 0
    j = data['gauss_change_rows']
    require_matrix(j, 2, 2)
    assert abs(determinant(j)) == 1
    reduced = multiply(multiply(j, gram_numerator), transpose(j))
    first, cross, second = reduced[0][0], reduced[0][1], reduced[1][1]
    assert 0 < first <= second and 2 * abs(cross) <= first
    unit = 16 ** (2 * n)
    assert first > 2 * unit * unit * denominator
    # I_k < 1/(4*k^2*binom(2*k,k)^2). Comparing the new positive
    # weights with the old ones transfers the obstruction only if this
    # stronger exact threshold holds; failure is not an existence result.
    beta_threshold = 32 * (2 * n) ** 4 * comb(4 * n, 2 * n) ** 4
    beta_obstruction = first > beta_threshold * denominator
    result = {
        'n': n, 'rank_E': m - dimension, 'integer_kernel_dimension': dimension,
        'saturation_minor_gcd': minor_gcd, 'image_index_bits': image_index.bit_length(),
        'index_obstruction': image_index >= 2 * unit * comb(4 * n, 2 * n),
        'quotient_shortest_squared_floor_log2': (first // denominator).bit_length() - 1,
        'threshold_floor_log2': 16 * n + 1,
        'every_effective_integer_direction_has_cost_greater_than_unit': True,
        'beta_weight_obstruction_by_comparison': beta_obstruction,
    }
    print(json.dumps(result), flush=True)
    return (result, data) if include_certificate else result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='*', default=[34, 48, 64, 96])
    for n in parser.parse_args().n:
        check(n)

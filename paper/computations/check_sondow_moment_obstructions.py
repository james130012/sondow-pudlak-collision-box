"""Check exact finite Sondow obstructions with the integral moment metric.

The baseline checker certifies the full integer kernel and its (Q,T) quotient.
This checker rebuilds the rational moment matrix using binomial coefficients,
then verifies projection equations and a two-dimensional integer Gauss change.
No candidate generator, floating-point arithmetic or LLL implementation is used.
"""
import argparse
import json
from math import comb, lcm
from pathlib import Path
import sys

from check_sondow_n31_obstruction import source_column
from check_sondow_quotient_obstructions import (
    check as check_baseline, determinant, multiply, require_matrix, transpose,
)

sys.set_int_max_str_digits(0)


def floor_log_ratio(numerator, denominator):
    assert numerator > 0 and denominator > 0
    exponent = numerator.bit_length() - denominator.bit_length()
    below = (numerator < denominator * (1 << exponent) if exponent >= 0
             else numerator * (1 << -exponent) < denominator)
    return exponent - int(below)


def check(n):
    _, baseline = check_baseline(n, include_certificate=True)
    path = Path(__file__).with_name(f'sondow_moment_obstruction_n{n}_20260905.json')
    data = json.loads(path.read_text())
    assert data['n'] == n
    assert data['base_certificate'] == f'sondow_quotient_obstruction_n{n}_20260905.json'
    basis = baseline['basis']
    dimension, m = len(basis), n + 1
    ds = [source_column(k)[0] for k in range(n, 2 * n + 1)]
    beta_den = {k: 4 * k * k * comb(2 * k, k) ** 2 for k in range(n, 3 * n + 1)}
    common = lcm(*beta_den.values())
    denominator = beta_den[n] * common
    assert common == data['moment_hankel_common_denominator']
    assert denominator == data['moment_denominator']
    hankel = [[ds[i] * ds[j] * (common // beta_den[n + i + j])
               for j in range(m)] for i in range(m)]
    # The positive integral measure proves this moment matrix positive definite.
    gram = multiply(multiply(basis, hankel), transpose(basis))
    u = baseline['image_change_rows']
    changed = multiply(multiply(u, gram), transpose(u))
    s = [row[:2] for row in changed[:2]]
    r = [row[2:] for row in changed[2:]]
    z = [row[:2] for row in changed[2:]]
    projection_den = data['projection_denominator']
    assert type(projection_den) is int and projection_den > 0
    numerators = data['projection_numerators']
    require_matrix(numerators, dimension - 2, 2)
    if dimension > 2:
        assert multiply(r, numerators) == [[projection_den * x for x in row] for row in z]
        correction = multiply(transpose(z), numerators)
    else:
        correction = [[0, 0], [0, 0]]
    quotient = [[projection_den * s[i][j] - correction[i][j]
                 for j in range(2)] for i in range(2)]
    assert quotient[0][1] == quotient[1][0]
    assert quotient[0][0] > 0 and determinant(quotient) > 0
    j = data['gauss_change_rows']
    require_matrix(j, 2, 2)
    assert abs(determinant(j)) == 1
    reduced = multiply(multiply(j, quotient), transpose(j))
    first, cross, second = reduced[0][0], reduced[0][1], reduced[1][1]
    assert 0 < first <= second and 2 * abs(cross) <= first
    total_den = denominator * projection_den
    assert first > total_den  # Strict >1; equality could still exclude q=1.
    # The proven comparison U(a)^2 < (16/9)*C_beta(a)^2 for nonzero a
    # transfers this exact lower bound to the earlier sign-weight certificate.
    assert 9 * first > 16 * total_den
    result = {
        'n': n,
        'moment_shortest_squared_floor_log2': floor_log_ratio(first, total_den),
        'moment_second_squared_floor_log2': floor_log_ratio(second, total_den),
        'every_effective_integer_direction_has_moment_cost_squared_greater_than_one': True,
        'every_effective_integer_direction_has_beta_sign_cost_greater_than_one': True,
    }
    print(json.dumps(result), flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='*', default=[34, 48, 64, 96])
    for n in parser.parse_args().n:
        check(n)

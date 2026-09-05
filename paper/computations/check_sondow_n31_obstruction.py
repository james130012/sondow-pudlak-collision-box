"""Check a finite mathematical certificate; this does not prove a tail theorem.

Uses only Python's standard library. Candidate generation and floating point
LLL calculations are not trusted by this checker.
"""
from functools import lru_cache
from itertools import combinations
import json
from math import comb, gcd, isqrt, lcm
from pathlib import Path


def primes_up_to(bound):
    return [p for p in range(2, bound + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


@lru_cache(None)
def source_column(k):
    d = lcm(*range(1, 2 * k + 1))
    squares = [comb(k, i) ** 2 for i in range(k + 1)]
    exponents = {}
    # This follows the original triple sum, not the candidate generator's
    # harmonic-prefix aggregation.
    for j in range(1, k + 1):
        exponent = 0
        for i in range(min(j - 1, k - j) + 1):
            for h in range(i + 1, k - i + 1):
                assert d % h == 0
                exponent += 2 * (d // h) * squares[i]
        base = k + j
        for p in range(2, isqrt(base) + 1):
            while base % p == 0:
                exponents[p] = exponents.get(p, 0) + exponent
                base //= p
        if base > 1:
            exponents[base] = exponents.get(base, 0) + exponent
    harmonic = [0]
    for h in range(1, 2 * k + 1):
        harmonic.append(harmonic[-1] + d // h)
    q = d * comb(2 * k, k)
    t = sum(squares[i] * harmonic[k + i] for i in range(k + 1))
    return d, exponents, q, t


def determinant_mod(matrix, prime):
    a = [[entry % prime for entry in row] for row in matrix]
    size = len(a)
    assert all(len(row) == size for row in a)
    result = 1
    for col in range(size):
        pivot = next((i for i in range(col, size) if a[i][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            result = -result
        entry = a[col][col]
        result = result * entry % prime
        inverse = pow(entry, -1, prime)
        for i in range(col + 1, size):
            multiple = a[i][col] * inverse % prime
            for j in range(col, size):
                a[i][j] = (a[i][j] - multiple * a[col][j]) % prime
    return result % prime


def dot(a, b):
    assert len(a) == len(b)
    return sum(x * y for x, y in zip(a, b))


def check():
    path = Path(__file__).with_name('sondow_n31_kernel_obstruction_20260905.json')
    certificate = json.loads(path.read_text())
    n, a, b = certificate['n'], certificate['a'], certificate['b']
    assert n == 31 and len(a) == len(b) == n + 1
    assert all(type(x) is int for x in a + b)
    primes = primes_up_to(4 * n)
    assert len(primes) == 30
    columns = [source_column(k) for k in range(n, 2 * n + 1)]
    e = [[column[1].get(p, 0) for column in columns] for p in primes]
    assert all(dot(row, a) == dot(row, b) == 0 for row in e)
    assert 1009 in primes_up_to(1009)
    minor = determinant_mod([row[:30] for row in e], 1009)
    assert minor == 511
    # Rank E is 30, so the rational kernel has dimension two.
    minor_gcd = 0
    for i, j in combinations(range(n + 1), 2):
        minor_gcd = gcd(minor_gcd, a[i] * b[j] - a[j] * b[i])
    assert minor_gcd == 1
    # The gcd-one identity proves that a,b span the entire integer kernel.
    q = [column[2] for column in columns]
    t = [column[3] for column in columns]
    delta = dot(a, q) * dot(b, t) - dot(b, q) * dot(a, t)
    assert delta != 0
    weights = [column[0] * 16 ** (n - j) for j, column in enumerate(columns)]
    wa = [x * w for x, w in zip(a, weights)]
    wb = [x * w for x, w in zip(b, weights)]
    aa, bb, ab = dot(wa, wa), dot(wb, wb), dot(wa, wb)
    gram_determinant = aa * bb - ab * ab
    unit = 16 ** (2 * n)
    threshold = 2 * unit * unit
    assert aa > threshold
    assert gram_determinant > threshold * aa
    print(json.dumps({
        'n': n, 'rank_E': 30, 'minor_mod_1009': minor,
        'kernel_basis_minor_gcd': minor_gcd,
        'effective_projection_determinant_nonzero': delta != 0,
        'gram_first_floor_log2': aa.bit_length() - 1,
        'gram_second_floor_log2': (gram_determinant // aa).bit_length() - 1,
        'threshold_floor_log2': threshold.bit_length() - 1,
        'all_nonzero_integer_kernel_vectors_have_C_greater_than_unit': True,
    }, indent=2))


if __name__ == '__main__':
    check()

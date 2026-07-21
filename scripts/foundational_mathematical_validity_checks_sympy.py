#!/usr/bin/env python3
"""Exact arithmetic side checks for the foundational validity audit.

This file deliberately checks only elementary arithmetic.  It does not check
PA provability, the hypotheses of Pudlak's theorem, the identity of proof
systems/length measures, or a Sondow-certificate-to-finite-consistency bridge.

Every search below uses Python integers or SymPy exact rationals.  A bounded
search is printed as ``SAMPLE_ONLY`` and is never reported as a proof.
"""

from __future__ import annotations

from itertools import product

import sympy as sp


failures: list[str] = []


def proved(label: str, condition: bool, detail: object = "True") -> None:
    status = "PASS_EXACT" if condition else "FAIL"
    print(f"{status} | {label} | {detail}")
    if not condition:
        failures.append(label)


def sampled(label: str, counterexample: object | None, domain: str) -> None:
    if counterexample is None:
        print(f"SAMPLE_ONLY | {label} | no counterexample in {domain}")
    else:
        print(f"COUNTEREXAMPLE | {label} | {counterexample}")
        failures.append(label)


def expected_counterexample(label: str, counterexample: object | None) -> None:
    if counterexample is None:
        print(f"FAIL | {label} | expected a counterexample, found none")
        failures.append(label)
    else:
        print(f"EXPECTED_COUNTEREXAMPLE | {label} | {counterexample}")


def yellow(label: str, expression: object, reason: str) -> None:
    print(f"YELLOW_UNRESOLVED | {label} | {expression} | {reason}")


def first_counterexample(rows, claim):
    for row in rows:
        if not claim(*row):
            return row
    return None


def rho(d: int, n: int) -> int:
    return (n + 1) ** (d * n)


def carrier(n: int) -> int:
    return (n + 1) ** n


def ceil_div(c: int, a: int) -> int:
    if a <= 0:
        raise ValueError("ceil_div requires a positive divisor")
    return (c + a - 1) // a


def packed_code(bits: tuple[int, ...]) -> int:
    """Project convention: low-to-high payload bits followed by sentinel 1."""
    return (1 << len(bits)) + sum(bit << index for index, bit in enumerate(bits))


print(f"SymPy version: {sp.__version__}")
print("Arithmetic mode: exact Integer/Rational only; no Float objects constructed")

# ---------------------------------------------------------------------------
# 1. rho_d(n) = (n+1)^(d n): exponent algebra, recurrence, monotonicity.
# ---------------------------------------------------------------------------

n, d, k = sp.symbols("n d k", integer=True, nonnegative=True)
x = sp.symbols("x", positive=True)

proved(
    "rho perfect-power exponent identity d*n=n*d",
    sp.expand(d * n - n * d) == 0,
    sp.Eq(d * n, n * d),
)
proved(
    "rho_(d+1) exponent recurrence (d+1)n=dn+n",
    sp.expand((d + 1) * n - (d * n + n)) == 0,
    sp.Eq((d + 1) * n, d * n + n),
)
proved(
    "adjacent monotonicity comparison exponent d(n+1)=dn+d",
    sp.expand(d * (n + 1) - (d * n + d)) == 0,
    sp.Eq(d * (n + 1), d * n + d),
)

sampled(
    "rho_d is strictly increasing in n when d>=1",
    first_counterexample(
        ((dd, nn, mm) for dd in range(1, 9) for nn in range(0, 19)
         for mm in range(nn + 1, 21)),
        lambda dd, nn, mm: rho(dd, nn) < rho(dd, mm),
    ),
    "1<=d<=8, 0<=n<m<=20",
)
sampled(
    "rho_(d+1)(n)=rho_d(n)*carrier(n)",
    first_counterexample(
        product(range(0, 9), range(0, 21)),
        lambda dd, nn: rho(dd + 1, nn) == rho(dd, nn) * carrier(nn),
    ),
    "0<=d<=8, 0<=n<=20",
)
sampled(
    "rho_d(n+1)>=rho_d(n)*(n+1)^d",
    first_counterexample(
        product(range(1, 9), range(0, 21)),
        lambda dd, nn: rho(dd, nn + 1) >= rho(dd, nn) * (nn + 1) ** dd,
    ),
    "1<=d<=8, 0<=n<=20",
)
expected_counterexample(
    "dropping d>0 makes strict rho monotonicity false",
    first_counterexample(
        ((0, nn) for nn in range(0, 8)),
        lambda dd, nn: rho(dd, nn) < rho(dd, nn + 1),
    ),
)
yellow(
    "unbounded symbolic rho monotonicity",
    sp.Lt((n + 1) ** (d * n), (n + 2) ** (d * (n + 1))),
    "variable integer exponents are outside SymPy's complete inequality procedures; see paper proof",
)

# ---------------------------------------------------------------------------
# 2. Fixed positive power/root rescaling and explicit thresholds.
# ---------------------------------------------------------------------------

a, c = sp.symbols("a c", integer=True, positive=True)
alpha = sp.symbols("alpha", positive=True)
degree_real = sp.symbols("degree_real", real=True)
proved(
    "fixed-root perfect-power rewrite (x^(k*n))^1/k is avoided",
    sp.expand(k * n - n * k) == 0,
    "rho_k(n)=carrier(n)^k by natural-power laws",
)
sampled(
    "rho_k(n)=carrier(n)^k",
    first_counterexample(
        product(range(1, 9), range(0, 21)),
        lambda kk, nn: rho(kk, nn) == carrier(nn) ** kk,
    ),
    "1<=k<=8, 0<=n<=20",
)
sampled(
    "x^k>y^k implies x>y over naturals for k>0",
    first_counterexample(
        product(range(1, 9), range(0, 31), range(0, 31)),
        lambda kk, xx, yy: not (xx**kk > yy**kk) or xx > yy,
    ),
    "1<=k<=8, 0<=x,y<=30",
)
expected_counterexample(
    "dropping k>0 invalidates root-order reflection",
    first_counterexample(
        ((0, xx, yy) for xx in range(0, 5) for yy in range(0, 5)),
        lambda kk, xx, yy: not (xx**kk >= yy**kk) or xx >= yy,
    ),
)

sampled(
    "d=ceil(c/a) satisfies a*d>=c",
    first_counterexample(
        product(range(1, 31), range(1, 31)),
        lambda aa, cc: aa * ceil_div(cc, aa) >= cc,
    ),
    "1<=a,c<=30",
)
sampled(
    "general rational exponent comparison rho_d(n)^a>=carrier(n)^c",
    first_counterexample(
        product(range(1, 9), range(1, 9), range(0, 13)),
        lambda aa, cc, nn: rho(ceil_div(cc, aa), nn) ** aa
        >= carrier(nn) ** cc,
    ),
    "1<=a,c<=8, 0<=n<=12, d=ceil(c/a)",
)
yellow(
    "symbolic ceiling implication a*ceil(c/a)>=c",
    sp.Ge(a * sp.ceiling(sp.Rational(1, 1) * c / a), c),
    "SymPy leaves the quantified ceiling fact conditional; the finite search is not its proof",
)

proved(
    "Archimedean exponent-choice algebra alpha*d-1=alpha*(d-1/alpha)",
    sp.simplify(
        alpha * degree_real - 1
        - alpha * (degree_real - 1 / alpha)
    ) == 0,
    "with alpha>0 and d>=1/alpha the right side is nonnegative",
)

sampled(
    "conservative rescaling threshold n>=B0 implies rho_d(n)>=B0",
    first_counterexample(
        ((dd, b0, nn) for dd in range(1, 9) for b0 in range(0, 31)
         for nn in range(b0, 31)),
        lambda dd, b0, nn: rho(dd, nn) >= b0,
    ),
    "1<=d<=8, 0<=B0<=n<=30",
)
expected_counterexample(
    "a non-strict fixed-power lower bound cannot yield the strict target",
    first_counterexample(
        ((kk, yy, yy) for kk in range(1, 6) for yy in range(1, 10)),
        lambda kk, xx, yy: not (xx**kk >= yy**kk) or xx > yy,
    ),
)

# Explicit domination threshold used by the Lean arithmetic gate:
# n >= C+k+1 implies C(n+1)^k < (n+1)^n.
sampled(
    "explicit polynomial-domination threshold C+k+1",
    first_counterexample(
        ((cc, kk, nn) for cc in range(0, 21) for kk in range(0, 9)
         for nn in range(cc + kk + 1, cc + kk + 6)),
        lambda cc, kk, nn: cc * (nn + 1) ** kk < (nn + 1) ** nn,
    ),
    "0<=C<=20, 0<=k<=8, C+k+1<=n<=C+k+5",
)
expected_counterexample(
    "weakened threshold n>=C+k-1 is insufficient",
    first_counterexample(
        ((cc, kk, max(0, cc + kk - 1)) for cc in range(0, 8)
         for kk in range(0, 8)),
        lambda cc, kk, nn: cc * (nn + 1) ** kk < (nn + 1) ** nn,
    ),
)

# ---------------------------------------------------------------------------
# 3. Half-denominator threshold (all arithmetic is integer exact).
# ---------------------------------------------------------------------------

sampled(
    "ceil(q/2)=(q+1)//2 for integer q>=0",
    first_counterexample(
        ((qq,) for qq in range(0, 501)),
        lambda qq: sp.ceiling(sp.Rational(qq, 2)) == (qq + 1) // 2,
    ),
    "0<=q<=500",
)
sampled(
    "n>=max(3,ceil(q/2)) implies q<=2n",
    first_counterexample(
        ((qq, nn) for qq in range(0, 101)
         for nn in range(max(3, ceil_div(qq, 2)), 80)),
        lambda qq, nn: qq <= 2 * nn,
    ),
    "0<=q<=100, max(3,ceil(q/2))<=n<80",
)
expected_counterexample(
    "floor(q/2) cannot replace ceil(q/2)",
    first_counterexample(
        ((qq, qq // 2) for qq in range(0, 30)),
        lambda qq, nn: qq <= 2 * nn,
    ),
)

# ---------------------------------------------------------------------------
# 4. Payload-polynomial addition, multiplication, and composition.
# ---------------------------------------------------------------------------

z = sp.symbols("z", nonnegative=True)
p0, p1, p2, p3, q0, q1, q2 = sp.symbols(
    "p0 p1 p2 p3 q0 q1 q2", nonnegative=True
)
P = p0 + p1 * z + p2 * z**2 + p3 * z**3
Q = q0 + q1 * z + q2 * z**2
sum_poly = sp.Poly(sp.expand(P + Q), z, p0, p1, p2, p3, q0, q1, q2)
product_poly = sp.Poly(sp.expand(P * Q), z, p0, p1, p2, p3, q0, q1, q2)
composition_expr = sp.expand(P.subs(z, Q))
composition_poly = sp.Poly(
    composition_expr, z, p0, p1, p2, p3, q0, q1, q2
)
proved(
    "nonnegative-coefficient polynomials close under addition",
    all(coefficient >= 0 for coefficient in sum_poly.coeffs()),
    f"monomials={len(sum_poly.terms())}",
)
proved(
    "nonnegative-coefficient polynomials close under multiplication",
    all(coefficient >= 0 for coefficient in product_poly.coeffs()),
    f"monomials={len(product_poly.terms())}",
)
proved(
    "nonnegative-coefficient polynomials close under composition",
    all(coefficient >= 0 for coefficient in composition_poly.coeffs()),
    f"monomials={len(composition_poly.terms())}",
)

proof_left, proof_right, syntax, resource = sp.symbols(
    "proof_left proof_right syntax resource", nonnegative=True
)
specialization_cost = 192 + 2048 * syntax**3
modus_ponens_bound = proof_left + proof_right + 240 + 34 * syntax
conjunction_bound = proof_left + proof_right + 144 + 11 * syntax
exists_bound = proof_left + 96 + 14 * syntax
connector_bound = 1024 + 256 * (resource + syntax + 1)
node_bound = resource * (
    proof_left + connector_bound + 1
)
for label, expression in (
    ("specialization payload polynomial", specialization_cost),
    ("modus-ponens payload polynomial", modus_ponens_bound),
    ("conjunction payload polynomial", conjunction_bound),
    ("existential-introduction payload polynomial", exists_bound),
    ("bounded-formula connector envelope", connector_bound),
    ("resource times node-envelope payload polynomial", node_bound),
):
    poly = sp.Poly(sp.expand(expression), proof_left, proof_right, syntax, resource)
    proved(
        f"{label} has only nonnegative coefficients",
        all(coefficient >= 0 for coefficient in poly.coeffs()),
        sp.expand(expression),
    )

i, r = sp.symbols("i r", integer=True, nonnegative=True)
B_i = p0 + p1 * i + p2 * i**2 + p3 * i**3
cumulative = sp.summation(B_i, (i, 0, r))
proved(
    "cumulative-envelope recurrence Sum[0..r+1]-Sum[0..r]=B(r+1)",
    sp.simplify(
        cumulative.subs(r, r + 1) - cumulative
        - B_i.subs(i, r + 1)
    ) == 0,
    sp.factor(cumulative),
)

# Concrete monomial envelope for compiler composition:
# T<=A B^p, S<=D B^q gives
# C(T+S+1)^E <= C(A+D+1)^E B^(max(p,q)E), B=n+1>=1.
sampled(
    "payload compiler monomial composition envelope",
    first_counterexample(
        ((aa, dd, pp, qq, ee, nn)
         for aa in range(0, 6) for dd in range(0, 6)
         for pp in range(0, 5) for qq in range(0, 5)
         for ee in range(1, 5) for nn in range(0, 8)),
        lambda aa, dd, pp, qq, ee, nn:
        (aa * (nn + 1) ** pp + dd * (nn + 1) ** qq + 1) ** ee
        <= (aa + dd + 1) ** ee
        * (nn + 1) ** (max(pp, qq) * ee),
    ),
    "0<=A,D<=5, 0<=p,q<=4, 1<=E<=4, 0<=n<=7",
)
sampled(
    "graft sum envelope",
    first_counterexample(
        ((aa, dd, cc, pp, qq, nn)
         for aa in range(0, 8) for dd in range(0, 8)
         for cc in range(0, 8) for pp in range(0, 5)
         for qq in range(0, 5) for nn in range(0, 10)),
        lambda aa, dd, cc, pp, qq, nn:
        aa * (nn + 1) ** pp + dd * (nn + 1) ** qq + cc
        <= (aa + dd + cc) * (nn + 1) ** max(pp, qq),
    ),
    "0<=A,D,C<=7, 0<=p,q<=4, 0<=n<=9",
)

# ---------------------------------------------------------------------------
# 5. Formula-code length and packed-payload direction checks.
# ---------------------------------------------------------------------------

sampled(
    "bit_length(rho_d(n)) <= 1+d*n*bit_length(n+1)",
    first_counterexample(
        product(range(1, 9), range(0, 51)),
        lambda dd, nn: rho(dd, nn).bit_length()
        <= 1 + dd * nn * (nn + 1).bit_length(),
    ),
    "1<=d<=8, 0<=n<=50",
)
sampled(
    "for n>=1 the sharper bit_length(rho)<=d*n*bit_length(n+1)",
    first_counterexample(
        product(range(1, 9), range(1, 51)),
        lambda dd, nn: rho(dd, nn).bit_length()
        <= dd * nn * (nn + 1).bit_length(),
    ),
    "1<=d<=8, 1<=n<=50",
)
expected_counterexample(
    "the sharper bit-length bound fails at exponent zero",
    first_counterexample(
        ((dd, 0) for dd in range(1, 5)),
        lambda dd, nn: rho(dd, nn).bit_length()
        <= dd * nn * (nn + 1).bit_length(),
    ),
)

pack_counterexample = None
for length in range(0, 11):
    for bits in product((0, 1), repeat=length):
        code = packed_code(bits)
        if not (
            code.bit_length() == length + 1
            and code.bit_length() - 1 == length
            and (1 << length) <= code < (1 << (length + 1))
        ):
            pack_counterexample = (bits, code)
            break
    if pack_counterexample is not None:
        break
sampled(
    "sentinel packing: size(code)=payloadLength+1 and payloadLength=len(bits)",
    pack_counterexample,
    "all bit strings of length <=10",
)

sampled(
    "substitute rho bit-length upper into an affine formula-length bound",
    first_counterexample(
        ((dd, nn, c0, c1, c2, ylen)
         for dd in range(1, 6) for nn in range(0, 16)
         for c0 in range(0, 5) for c1 in range(0, 5)
         for c2 in range(0, 4) for ylen in range(0, 6)),
        lambda dd, nn, c0, c1, c2, ylen:
        c0 + c1 * rho(dd, nn).bit_length() + c2 * ylen
        <= c0 + c1 * (1 + dd * nn * (nn + 1).bit_length())
        + c2 * ylen,
    ),
    "finite nonnegative affine coefficients and 1<=d<=5, 0<=n<=15",
)

expected_counterexample(
    "numeric rho is not bounded by its bit length (forbidden reversed direction)",
    first_counterexample(
        product(range(1, 6), range(0, 16)),
        lambda dd, nn: rho(dd, nn) <= rho(dd, nn).bit_length(),
    ),
)
expected_counterexample(
    "base>=1 is needed for monotonicity in the exponent",
    first_counterexample(
        ((0, e1, e2) for e1 in range(0, 5) for e2 in range(e1, 6)),
        lambda base, e1, e2: base**e1 <= base**e2,
    ),
)

print("YELLOW_SCOPE | bounded searches above are pressure tests, not proofs")
print(
    "YELLOW_SCOPE | no CAS result here validates PA internal provability, "
    "Pudlak applicability, object/measure identity, or the Sondow-to-G_n bridge"
)
if failures:
    print("OVERALL: FAIL | " + ", ".join(failures))
    raise SystemExit(1)
print("OVERALL: PASS for exact identities; bounded claims remain SAMPLE_ONLY")

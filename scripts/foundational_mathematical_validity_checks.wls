#!/usr/bin/env wolframscript

(* Exact arithmetic side checks for the foundational mathematical audit.
   No N, machine reals, or approximate comparisons occur in this file.
   Bounded FindInstance calls are pressure tests, never proofs. *)

ClearAll["Global`*"];

$auditFailures = 0;
$auditUnresolved = 0;
$auditTimeoutSeconds = 60;

Print["Wolfram version: ", $Version];
Print["Arithmetic mode: exact Integers/Rationals only; bounded searches are SAMPLE_ONLY"];

SetAttributes[{exactCheck, boundedSearch, expectedCounterexample}, HoldAll];

exactCheck[label_, expression_] := Module[{value},
  value = Quiet[Check[
    TimeConstrained[expression, $auditTimeoutSeconds, $Aborted],
    $Failed
  ]];
  Which[
    TrueQ[value],
      Print["PASS_EXACT | ", label, " | ", InputForm[value]],
    value === False,
      $auditFailures++;
      Print["FAIL | ", label, " | False"],
    value === $Aborted,
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | TIMEOUT after ",
        $auditTimeoutSeconds, " seconds"],
    True,
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | ", InputForm[value]]
  ];
  value
];

boundedSearch[label_, claim_, variables_, domain_] := Module[{value},
  value = Quiet[Check[
    TimeConstrained[
      FindInstance[Not[claim], variables, Integers],
      $auditTimeoutSeconds,
      $Aborted
    ],
    $Failed
  ]];
  Which[
    value === {},
      Print["SAMPLE_ONLY | ", label, " | no counterexample in ", domain],
    value === $Aborted,
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | TIMEOUT after ",
        $auditTimeoutSeconds, " seconds"],
    value === $Failed || !FreeQ[value, FindInstance],
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | ", InputForm[value]],
    True,
      $auditFailures++;
      Print["COUNTEREXAMPLE | ", label, " | ", InputForm[value]]
  ];
  value
];

expectedCounterexample[label_, proposition_, variables_] := Module[{value},
  value = Quiet[Check[
    TimeConstrained[
      FindInstance[proposition, variables, Integers],
      $auditTimeoutSeconds,
      $Aborted
    ],
    $Failed
  ]];
  Which[
    ListQ[value] && value =!= {} &&
      AllTrue[value, MatchQ[#, {__Rule}] &],
      Print["EXPECTED_COUNTEREXAMPLE | ", label, " | ", InputForm[value]],
    value === {},
      $auditFailures++;
      Print["FAIL | ", label, " | expected a counterexample, found none"],
    value === $Aborted,
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | TIMEOUT after ",
        $auditTimeoutSeconds, " seconds"],
    True,
      $auditUnresolved++;
      Print["YELLOW_UNRESOLVED | ", label, " | ", InputForm[value]]
  ];
  value
];

rho[d_, n_] := (n + 1)^(d n);
carrier[n_] := (n + 1)^n;
ceilDiv[c_, a_] := Ceiling[c/a];

(* ---------------------------------------------------------------------- *)
(* 1. rho exponent algebra, recurrences, monotonicity, and missing cases. *)
(* ---------------------------------------------------------------------- *)

exactCheck[
  "rho perfect-power identity",
  FullSimplify[
    rho[d, n] == carrier[n]^d,
    Assumptions -> Element[{d, n}, Integers] && d >= 0 && n >= 0
  ]
];

exactCheck[
  "rho_(d+1)(n)=rho_d(n) carrier(n)",
  Refine[
    rho[d + 1, n] == rho[d, n] carrier[n],
    Element[{d, n}, Integers] && d >= 0 && n >= 0
  ]
];

exactCheck[
  "exponent rewrites d(n+1)=dn+d and (d+1)n=dn+n",
  FullSimplify[
    d (n + 1) == d n + d && (d + 1) n == d n + n,
    Assumptions -> Element[{d, n}, Integers]
  ]
];

boundedSearch[
  "rho_d strictly increases in n for d>=1",
  Implies[
    1 <= d <= 8 && 0 <= n < m <= 20,
    rho[d, n] < rho[d, m]
  ],
  {d, n, m},
  "1<=d<=8, 0<=n<m<=20"
];

boundedSearch[
  "adjacent rho lower recurrence",
  Implies[
    1 <= d <= 8 && 0 <= n <= 20,
    rho[d, n + 1] >= rho[d, n] (n + 1)^d
  ],
  {d, n},
  "1<=d<=8, 0<=n<=20"
];

expectedCounterexample[
  "dropping d>0 makes strict rho monotonicity false",
  0 <= n <= 8 && Not[rho[0, n] < rho[0, n + 1]],
  {n}
];

(* Variable integer exponents are not a complete Reduce fragment.  This call
   is kept so any future engine improvement is visible; an unevaluated result
   remains yellow. *)
exactCheck[
  "unbounded symbolic rho monotonicity",
  FullSimplify[
    rho[d, n] < rho[d, n + 1],
    Assumptions -> Element[{d, n}, Integers] && d >= 1 && n >= 0
  ]
];

(* ---------------------------------------------------------------------- *)
(* 2. Fixed positive-power rescaling and explicit thresholds.             *)
(* ---------------------------------------------------------------------- *)

exactCheck[
  "perfect-power comparison rewrite",
  FullSimplify[
    rho[k, n] == carrier[n]^k,
    Assumptions -> Element[{k, n}, Integers] && k >= 1 && n >= 0
  ]
];

boundedSearch[
  "positive natural power reflects strict order",
  Implies[
    1 <= k <= 8 && 0 <= x <= 30 && 0 <= y <= 30 && x^k > y^k,
    x > y
  ],
  {k, x, y},
  "1<=k<=8, 0<=x,y<=30"
];

expectedCounterexample[
  "dropping k>0 invalidates power-order reflection",
  0 <= x <= 5 && 0 <= y <= 5 && x^0 >= y^0 && Not[x >= y],
  {x, y}
];

exactCheck[
  "ceiling choice d=ceil(c/a) gives ad>=c",
  Resolve[
    ForAll[{a, c},
      Implies[a >= 1 && c >= 1, a Ceiling[c/a] >= c]
    ],
    Integers
  ]
];

exactCheck[
  "positive-real exponent choice d>=1/alpha gives alpha*d>=1",
  Resolve[
    ForAll[{alpha, degreeReal},
      Implies[alpha > 0 && degreeReal >= 1/alpha,
        alpha degreeReal >= 1]
    ],
    Reals
  ]
];

boundedSearch[
  "general rational-exponent scale comparison",
  Implies[
    1 <= a <= 8 && 1 <= c <= 8 && 0 <= n <= 12 &&
      d == ceilDiv[c, a],
    rho[d, n]^a >= carrier[n]^c
  ],
  {a, c, d, n},
  "1<=a,c<=8, d=ceil(c/a), 0<=n<=12"
];

boundedSearch[
  "conservative threshold n>=B0 gives rho_d(n)>=B0",
  Implies[
    1 <= d <= 8 && 0 <= b0 <= n <= 30,
    rho[d, n] >= b0
  ],
  {d, b0, n},
  "1<=d<=8, 0<=B0<=n<=30"
];

boundedSearch[
  "explicit polynomial-domination threshold C+k+1",
  Implies[
    0 <= cc <= 20 && 0 <= k <= 8 &&
      cc + k + 1 <= n <= cc + k + 5,
    cc (n + 1)^k < (n + 1)^n
  ],
  {cc, k, n},
  "0<=C<=20, 0<=k<=8, C+k+1<=n<=C+k+5"
];

expectedCounterexample[
  "weakened threshold n>=C+k-1 is insufficient",
  0 <= cc <= 8 && 0 <= k <= 8 && n == Max[0, cc + k - 1] &&
    Not[cc (n + 1)^k < (n + 1)^n],
  {cc, k, n}
];

expectedCounterexample[
  "non-strict fixed-power lower bound cannot yield strict target",
  1 <= k <= 5 && 1 <= y <= 10 && x == y &&
    x^k >= y^k && Not[x > y],
  {k, x, y}
];

(* ---------------------------------------------------------------------- *)
(* 3. Half-denominator integer threshold.                                 *)
(* ---------------------------------------------------------------------- *)

exactCheck[
  "integer half ceiling formula",
  Resolve[
    ForAll[q,
      Implies[q >= 0, Ceiling[q/2] == Quotient[q + 1, 2]]
    ],
    Integers
  ]
];

exactCheck[
  "n>=ceil(q/2) iff q<=2n for nonnegative integers",
  Resolve[
    ForAll[{q, n},
      Implies[q >= 0 && n >= 0,
        (n >= Ceiling[q/2]) == (q <= 2 n)]
    ],
    Integers
  ]
];

boundedSearch[
  "half-den threshold max(3,ceil(q/2))",
  Implies[
    0 <= q <= 100 && Max[3, Ceiling[q/2]] <= n <= 80,
    q <= 2 n
  ],
  {q, n},
  "0<=q<=100, max(3,ceil(q/2))<=n<=80"
];

expectedCounterexample[
  "Floor(q/2) cannot replace Ceiling(q/2)",
  0 <= q <= 30 && n == Floor[q/2] && Not[q <= 2 n],
  {q, n}
];

(* ---------------------------------------------------------------------- *)
(* 4. Payload polynomial combination and monotone substitutions.          *)
(* ---------------------------------------------------------------------- *)

p[z_] := p0 + p1 z + p2 z^2 + p3 z^3;
qpoly[z_] := q0 + q1 z + q2 z^2;
nonnegativeNumericCoefficients[expression_, variables_] :=
  And @@ (TrueQ[Last[#] >= 0] & /@
    CoefficientRules[Expand[expression], variables]);

exactCheck[
  "nonnegative coefficients close under addition",
  nonnegativeNumericCoefficients[p[z] + qpoly[z],
    {z, p0, p1, p2, p3, q0, q1, q2}]
];
exactCheck[
  "nonnegative coefficients close under multiplication",
  nonnegativeNumericCoefficients[p[z] qpoly[z],
    {z, p0, p1, p2, p3, q0, q1, q2}]
];
exactCheck[
  "nonnegative coefficients close under composition",
  nonnegativeNumericCoefficients[p[qpoly[z]],
    {z, p0, p1, p2, p3, q0, q1, q2}]
];

specializationCost[s_] := 192 + 2048 s^3;
modusPonensBound[left_, right_, s_] := left + right + 240 + 34 s;
conjunctionBound[left_, right_, s_] := left + right + 144 + 11 s;
existsBound[body_, s_] := body + 96 + 14 s;
connectorBound[r_, t_] := 1024 + 256 (r + t + 1);
nodePayloadBound[r_, leaf_, t_] :=
  r (leaf + connectorBound[r, t] + 1);

exactCheck[
  "named payload expressions have nonnegative coefficients",
  And @@ {
    nonnegativeNumericCoefficients[specializationCost[s], {s}],
    nonnegativeNumericCoefficients[modusPonensBound[left, right, s],
      {left, right, s}],
    nonnegativeNumericCoefficients[conjunctionBound[left, right, s],
      {left, right, s}],
    nonnegativeNumericCoefficients[existsBound[left, s], {left, s}],
    nonnegativeNumericCoefficients[connectorBound[r, s], {r, s}],
    nonnegativeNumericCoefficients[nodePayloadBound[r, left, s],
      {r, left, s}]
  }
];

exactCheck[
  "modus-ponens payload substitution direction",
  Resolve[
    ForAll[{left, right, s, leftUpper, rightUpper, sUpper},
      Implies[
        0 <= left <= leftUpper && 0 <= right <= rightUpper &&
          0 <= s <= sUpper,
        modusPonensBound[left, right, s] <=
          modusPonensBound[leftUpper, rightUpper, sUpper]
      ]
    ],
    Reals
  ]
];

exactCheck[
  "multiplicative payload substitution direction",
  Reduce[
    0 <= aa <= aaUpper && 0 <= bb <= bbUpper &&
      Not[aa bb <= aaUpper bbUpper],
    {aa, bb, aaUpper, bbUpper},
    Reals
  ] === False
];

exactCheck[
  "cumulative envelope recurrence",
  FullSimplify[
    Sum[p[i], {i, 0, r + 1}] - Sum[p[i], {i, 0, r}] == p[r + 1],
    Assumptions -> Element[r, Integers] && r >= 0
  ]
];

boundedSearch[
  "compiler monomial composition envelope",
  Implies[
    0 <= aa <= 5 && 0 <= bb <= 5 && 0 <= pp <= 4 &&
      0 <= qq <= 4 && 1 <= ee <= 4 && 0 <= n <= 7,
    (aa (n + 1)^pp + bb (n + 1)^qq + 1)^ee <=
      (aa + bb + 1)^ee (n + 1)^(Max[pp, qq] ee)
  ],
  {aa, bb, pp, qq, ee, n},
  "0<=A,B<=5, 0<=p,q<=4, 1<=E<=4, 0<=n<=7"
];

boundedSearch[
  "graft sum envelope",
  Implies[
    0 <= aa <= 7 && 0 <= bb <= 7 && 0 <= cc <= 7 &&
      0 <= pp <= 4 && 0 <= qq <= 4 && 0 <= n <= 9,
    aa (n + 1)^pp + bb (n + 1)^qq + cc <=
      (aa + bb + cc) (n + 1)^Max[pp, qq]
  ],
  {aa, bb, cc, pp, qq, n},
  "0<=A,B,C<=7, 0<=p,q<=4, 0<=n<=9"
];

(* ---------------------------------------------------------------------- *)
(* 5. Formula-code and complete packed-payload length directions.         *)
(* ---------------------------------------------------------------------- *)

bitLength[value_] := IntegerLength[value, 2];
packBits[bits_List] :=
  2^Length[bits] + Sum[bits[[index]] 2^(index - 1),
    {index, 1, Length[bits]}];

boundedSearch[
  "bitLength(rho)<=1+d n bitLength(n+1)",
  Implies[
    1 <= d <= 8 && 0 <= n <= 50,
    bitLength[rho[d, n]] <= 1 + d n bitLength[n + 1]
  ],
  {d, n},
  "1<=d<=8, 0<=n<=50"
];

boundedSearch[
  "sharper positive-exponent rho bit-length bound",
  Implies[
    1 <= d <= 8 && 1 <= n <= 50,
    bitLength[rho[d, n]] <= d n bitLength[n + 1]
  ],
  {d, n},
  "1<=d<=8, 1<=n<=50"
];

expectedCounterexample[
  "sharper bit-length bound fails at exponent zero",
  1 <= d <= 5 && n == 0 &&
    Not[bitLength[rho[d, n]] <= d n bitLength[n + 1]],
  {d, n}
];

packingClaim = And @@ Flatten@Table[
  And @@ (Function[bits,
      bitLength[packBits[bits]] == Length[bits] + 1 &&
      bitLength[packBits[bits]] - 1 == Length[bits] &&
      2^Length[bits] <= packBits[bits] < 2^(Length[bits] + 1)
    ] /@ Tuples[{0, 1}, length]),
  {length, 0, 10}
];
If[TrueQ[packingClaim],
  Print["SAMPLE_ONLY | sentinel packing exact identities | all bit strings of length <=10"],
  $auditFailures++;
  Print["FAIL | sentinel packing exact identities | counterexample present"]
];

exactCheck[
  "affine formula-length substitution direction",
  Resolve[
    ForAll[{ell, ellUpper, c0, c1, c2, fixedLength},
      Implies[
        0 <= ell <= ellUpper && c0 >= 0 && c1 >= 0 && c2 >= 0 &&
          fixedLength >= 0,
        c0 + c1 ell + c2 fixedLength <=
          c0 + c1 ellUpper + c2 fixedLength
      ]
    ],
    Reals
  ]
];

expectedCounterexample[
  "numeric rho is not bounded by its bit length",
  1 <= d <= 5 && 0 <= n <= 15 &&
    Not[rho[d, n] <= bitLength[rho[d, n]]],
  {d, n}
];

expectedCounterexample[
  "base>=1 is needed for monotonicity in the exponent",
  0 <= e1 <= e2 <= 6 && Not[0^e1 <= 0^e2],
  {e1, e2}
];

(* FindEquationalProof is used only for an equality-logic instance.  The
   ProofObject is printed in the log and saved outside the repository. *)
rhoExponentProof = Quiet[Check[
  TimeConstrained[
    FindEquationalProof[
      times[d, n] == times[n, d],
      {ForAll[{u, v}, times[u, v] == times[v, u]]}
    ],
    $auditTimeoutSeconds,
    $Aborted
  ],
  $Failed
]];
If[MatchQ[rhoExponentProof, _ProofObject],
  Put[rhoExponentProof,
    "/tmp/foundational_mathematical_validity_rho_exponent_proof.wl"];
  Print["PASS_EXACT | FindEquationalProof commutative exponent rewrite | ",
    InputForm[rhoExponentProof]];
  Print["ProofObject saved: /tmp/foundational_mathematical_validity_rho_exponent_proof.wl"],
  $auditUnresolved++;
  Print["YELLOW_UNRESOLVED | FindEquationalProof | ",
    InputForm[rhoExponentProof]]
];

Print["YELLOW_SCOPE | FindInstance domains are finite samples, not proofs"];
Print["YELLOW_SCOPE | CAS cannot validate PA provability, Pudlak applicability,"];
Print["YELLOW_SCOPE | proof-system/length identity, or the Sondow-to-G_n bridge"];

If[$auditFailures > 0,
  Print["OVERALL: FAIL | count=", $auditFailures];
  Exit[1],
  If[$auditUnresolved > 0,
    Print["OVERALL: INCOMPLETE_YELLOW | unresolved=", $auditUnresolved];
    Exit[2],
    Print["OVERALL: PASS for exact identities; bounded claims remain SAMPLE_ONLY"];
    Exit[0]
  ]
];

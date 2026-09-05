# Current Status

Date: 2026-09-05

This is an incomplete formalization and audit project. It does not currently
establish unconditional irrationality of the Euler–Mascheroni constant.

The current roadmap is [the proof dependency graph](docs/checked_minproof_theorem_dependency_graph_zh.pdf).
The detailed obligations and local validation history are in
[the proof control document](docs/short_checked_minproof_growth_proof_zh.md).

See [the bridge feasibility audit](docs/sondow_bridge_feasibility_20260905_zh.md) for the verified target and interface mismatches.

## Paper-first work order

Per the user's instruction, further Lean expansion is paused until the complete
paper argument is established. The immediate priority is the mathematical
Sondow bridge, not the M11 implementation queue.
See [the global paper argument](docs/paper_route_global_gate_20260905_zh.md)
for explicit tests of conjunction, implication, disjunction, stronger-theory
alternatives, and rescaling costs. These are conditional deductions, not a
completed bridge or a proof of impossibility.

The active paper manuscript is [the unified paper proof](paper/full_paper_proof_working_zh.md).
It now includes a finite rational interval certificate for the Sondow source,
its two-way characterization of fixed rational equality, bit-cost estimates,
a closed axiom/MP sequence-to-tree construction, and a conditional lower-bound
proof with explicit rescaling. The same-object Sondow reduction and the concrete
Pudlak hypotheses remain open. None of these paper lemmas is claimed as a new
Lean verification result.

The paper now gives a five-node MP construction with complete payload at most
29n+128 when each input payload is at most n. Its PA-internal direct-matrix
witness transport is still open.

The exact P_direct matrix also yields a fixed PA monotonicity proof on paper:
only inputWidth <= bound uses the public bound, so the same 20 witnesses transfer.
The manuscript now identifies the finite-soundness candidate's missing reflection
instance and derives a conditional lower bound on its proof length. This does
not establish the Sondow reduction or all quantitative derivability conditions.

The source side now has an explicit ground-arithmetic formula family, with
paper constructions of short PA proofs for either its true atoms or a false
atom followed by disjunction introduction. This removes a source-compilation
assumption for that chosen family only; no PA equivalence with an arbitrary
existential trace predicate is being claimed. The global logical diagnosis is
recorded at the start of the manuscript: the conditional collision rule is
valid, while the same-object number-theoretic reduction remains missing.

Further paper progress: the canonical token/offset matrix now has an explicit
PA induction argument for row extraction, prefix concatenation, and canonical
table construction, including width zero and sentinel handling. A separate
paper fuel proof now shows strict potential decrease and exactly 9 additional
MP macrosteps, followed by Finish and halted padding. The original 429-column
step matrix and its PA-internal correspondence remain open.
The source certificate is also characterized by a rational interval; single-layer
uniqueness, adjacent-layer stabilization, and a complete polynomial construction
of either an accepting rational or a whole-layer rejection certificate are proved.
Unbounded rejection is equivalent to irrationality and remains unproved; the
single-layer algorithm is not being used to claim the infinite conclusion.

The main graph and appendices 04/05 now distinguish earlier local Lean checks,
new paper-only constructions, conditional deductions, and open mathematical
obligations. M17 is an independent mathematical reduction, not an automatic
consequence of M11; M11 is paused for formalization. The lower-bound node now
states absence of short proofs to respect the minimum function's zero default.
An independent rereview of sections 6-7 found the conditional derivation sound;
the reflection-length statement now explicitly shares the required tail threshold.

A compact-code fixed point is now constructed on paper for the unchanged
P_direct. A separate deterministic substitution machine, beta remainder tables,
a fixed PA uniqueness proof, and additive short trace proofs give
D_m iff not P_direct(m,compactFormulaCode(D_m)) with complete payload polynomial
in the bit length of m. Independent review found no substantive flaw. The old
parameterized diagonal file uses a fixed Foundation open-formula code and does
not itself provide this theorem; the new auxiliary program awaits formalization.

A checked Mahler logarithm separation estimate is too weak at the actual S_n
height. The paper also constructs an explicit integer-residual family compatible
with all currently used integral numerical bounds and coarse heights. This
rules out deriving a contradiction from those weakened data alone; the exact
Sondow product, integral, or harmonic identity must supply additional information.
It does not rule out a proof using that special structure.

The exact InputSplit and initial-state equations now give a PA paper proof that
the public token count is proof-count plus certificate-count. New canonical
raw, offset and source tables have quadratic bit bounds, including empty input.
This closes the fuel parameter alignment, not successful parser transport.
The original 429-column matrix now has paper lemmas for row extraction,
reencoding, CrossEq seam concatenation and explicit accepted absorbing rows
that retain the same conclusion relation. A single task's suffix extension is
also constructed with its Gamma boundaries reencoded at the new token count.
Successful ordinary/closed syntax endpoints, sequent endpoints, all five
proof-root families and all four certificate-node branches now have explicit
PA paper append constructions, including exact fuel and common background
layout. Task-stack continuation, ReplaceHead/Drop, one/two scheduling and
the successful prefix before Finish are now proved on paper as well.
ChildResult Core/RowsEq/HeadEq and value-stack Drop/PushDrop continuation now
give complete 429-column one/two parse-success rows in the original G.
An independent source audit confirms the selected columns, shared bounds and
preservation of possibly nonempty fields in the current Parse task.
The three leaf branches now retain their complete independent rule graphs and
rebuild only the exposed interfaces. All three combine-success graphs are also
transported, including full formula-transform traces, shift tables and false
rule results; the crucial reverse implication after expanding bounds was
independently checked against the original formulas. All Parse/Combine success
branches now have complete local G rows. A PA induction now transports the
whole pre-Finish segment with the original CrossEq seams, allowing separate
internal tables at each row. The source fuel bounds also suffice for the MP
splice once its new-node rows exist. A root-combine stack-bottom invariant now
connects the final Gamma to the first parsed root; its first formula is an
actual input slice. The original canonical offset tables give
formulaWidth+4<=inputWidth and the PA implication P_direct(b,f)->ell(f)<=b+1.
New-node ordinary syntax graphs now follow from explicit PA node/Repeat
induction, exact event counts and complete original bounded-row witnesses.
The mode-3 negation graph adds the actual output rows, status validity and
exact fuel, with double negation and De Morgan equalities for the same codes.
The nine new G rows, final canonical input/conclusion interfaces and the
required short-proof instantiation costs remain.
Copying combine tasks unchanged after appending input was identified as incorrect.

The confirmation audit distinguishes an external poly(a) proof generator from
the internal poly(log a)-length implication. A fixed-matrix verification cost
lemma is proved under explicit numeric loop and bit-width budgets. The full
budget for all parser/axiom auxiliary graphs and the uniform PA compiler
correctness proof are not yet established, so conditions (1) and (2) stay open.

Using the actual Sondow prime-exponent matrix on [n,2n], the paper proves the
existence of a nonzero integer kernel vector of height exp(O(n/log n)), with
combined residual tending to zero. Nonzero coefficients do not guarantee a
nonzero residual. A finite two-vector certificate with independent (Q,T)
projections gives the strict denominator bound q > 2^n/H. Existence of an
unbounded certificate family with H/2^n tending to zero remains unproved.
This identifies a concrete arithmetic candidate, not a completed bridge.
The actual augmented matrix [E;Q;T] also has nonzero kernel vectors of the same
subexponential height, so short zero residuals are guaranteed in the real
Sondow family. Their integral polynomials must change sign. Exact finite minors
show that effective directions also occur (at n=31 and n=34); their required
small height has not been proved. A pure T projection necessarily has l1 norm
greater than 2^n and cannot directly give a nontrivial denominator bound.
The source denominator certificate is sharpened using actual D_k and separate
positive/negative weighted sums: q*C > 16^(2n). A fully specified n=31 integer
kernel certificate now proves that every nonzero kernel vector has C>16^62,
so this entire finite layer cannot give a nontrivial bound by this criterion.
The independent checker rebuilds the original triple-sum exponents, verifies a
full integer kernel basis and exact Gram inequalities; it does not trust LLL
optimality or use floating point evidence. No tail impossibility is claimed.
A general finite-layer obstruction also separates the common kernel by an
integer invertible change of basis, then checks the exact rational Gram form
of the two-dimensional projected quotient lattice. Its Gauss-reduced first
diagonal entry exceeding 2*(16^(2n))^2 excludes all low-cost effective directions
at that layer. This criterion is proved; no asymptotic application is claimed.
Four further actual layers, n=34,48,64,96, now pass that stronger obstruction
criterion. Complete integer kernels are certified by nonzero rank minors and
gcd-one maximal minors; independent standard-library checks verify every
integer change of basis, rational projection equation and exact Gauss bound.
Each layer excludes all effective directions with C<=16^(2n), including ones
the search did not return. These are finite statements only, not a tail result.
A cheaper image-index criterion is also proved: C^2 > d_img*N/(2*B_star),
where N=16^(2n) and B_star=binom(4n,2n). Thus d_img>=2*N*B_star excludes
all nontrivial two-vector certificates at that layer. The available uniform
divisibility factor 2*D_n is insufficient. Exact covolume identities show that
the small-residual estimate gives an area lower bound, not two short vectors;
the second direction and integer lifting costs remain essential open issues.

A new direct integral argument proves I_k < 1/(4*k^2*B_k^2) <= 16^(-k)/k
for every k>=1. The resulting rational sign-weight cost C_beta gives the
stronger finite certificate q*C_beta>1. Old quotient certificates transfer to
this lower cost only under a stronger threshold: it holds at n=34,48, while
the comparison does not decide n=64,96. Failure of that test gives no short
integer representatives. The needed unbounded effective family remains open.
The image index also splits exactly as g_Qimg*h_T. Five archived factorizations
and recomputed full-kernel images locate every large-prime factor at n=31 in
the pure T part; the other four indices have no prime factor above 4n.
An exact local-module criterion states what would establish eventual absence
of such factors, but its required uniform solutions are not proved.

A rational positive-definite integral moment matrix now retains all signed
cross terms and gives the strict bound |r(a)|^2<U_n(a)^2. Effective pairs yield
q^2*max(U_n(a)^2,U_n(b)^2)>1. The proven comparison U_n(a)^2<(16/9)*C_beta(a)^2
allows finite obstructions to transfer between these schemes. Four new exact
matrix certificates pass independent integer checks at n=34,48,64,96, with
quotient shortest squared norms in dyadic ranges 20,16,4,2. Thus all four layers
exclude both low moment costs and low C_beta costs, including the two layers
not decided by the older weight comparison. No unbounded conclusion follows.

## Open obligations

- M11 / A04.18: compile the default endpoint and total exact-fuel trace,
  integrate with the same P_direct, and establish a fixed polynomial bound
  in complete input payload length. A numerical resource envelope alone
  does not discharge this obligation.
- M12–M15: establish concrete conditions (1)-(3) and the remaining quantitative
  encoding bounds. Monotonicity and the compact-code efficient fixed point are
  now proved on paper. Instantiate the lower-bound argument and rescaling to
  G_n = F_{(n+1)^(d*n)} only once all hypotheses are established.
- M17–M18: independently obtain short PA proofs of that same G_n from
  rationality and the Sondow certificates. This bridge remains unproved.
- M19–M21: audit identical formula, parameter, checker and measure before
  deriving a collision or the final irrationality conclusion.

The standard logical axiom profile does not remove theorem parameters.
Previously checked local components do not establish these open obligations.
Two fresh local Lean probes on 2026-09-05 reached the 60-second limit;
these runs are inconclusive, not passes. No full build was run.

## Historical checkpoint (not current completion evidence)

The following records the July checkpoint and must be read with its inputs:

# July checkpoint

Date: 2026-07-08

## Submission Route

The current submission route is the clean Lean theorem

```lean
cleanUpperProvider_submissionRoute
```

defined at:

<https://github.com/james130012/sondow-pudlak-collision-box/blob/main/integration/SondowProjectBigNCleanSubmissionRoute.lean>

It proves that, for the clean checker input and a measured upper provider in
the same coordinate, the rationality branch computes

```lean
N = max upperN threshold
```

and the same formal package proves

```lean
¬ is_rational euler_mascheroni
```

The observed axiom output for the main theorem is:

```text
[propext, Classical.choice, Quot.sound]
```

## Public Materials

- Polished submission release:
  <https://github.com/james130012/sondow-pudlak-collision-box/releases/tag/clean-bigN-submission-polished-20260708>
- Chinese submission manuscript:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/paper/submission_bigN_formal_manuscript_zh.md>
- English submission manuscript:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/paper/submission_bigN_formal_manuscript_en.md>
- Chinese audit report:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_zh.md>
- English audit report:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/clean_submission_route_audit_20260708_en.md>
- Validation log:
  <https://github.com/james130012/sondow-pudlak-collision-box/blob/main/docs/bigN_validation_log_20260708_zh.md>

## Reproduction

```bash
lake exe cache get
lake build integration.SondowProjectBigNCleanSubmissionRoute
```

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectBigNCleanSubmissionRoute
open SondowMainCheckedCodeBridge.SondowProjectBigNCleanSubmissionRoute

#check cleanUpperProvider_submissionRoute
#check cleanComputedBigN_eq_tailGapMax
#check cleanProvider_not_rational
#print axioms cleanUpperProvider_submissionRoute
#print axioms cleanComputedBigN_eq_tailGapMax
#print axioms cleanProvider_not_rational
EOF
```

## Scope

This release is a clean formal collision result. It does not claim decimal
extraction of the threshold. Numerical extraction is deferred to later work.

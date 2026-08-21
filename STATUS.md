# Project Status

Date: 2026-07-08

## Current Release Target

`bigN-nature-paper-20260708`: a Lean-checked existential big-`N` endpoint for
the source-calibrated Sondow-Pudlak project-length route, with paper and audit
materials organized for independent reproduction.

Release commit:

```text
c26cd1d2b3abbc6c3584ab5c2afbd1e953d3cacd
```

## Current Main Result

The current release adds a publishable big-`N` endpoint:

```lean
projectLengthS21GraftProofLengthRecognitionSourceCalibratedBigN_exists_of_halfDenTailPrefixMax
```

defined in:

```text
integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean
```

In explicit input packages consisting of S21 proof-length recognition,
Sondow/partial verifier traces, a rational-branch Sondow parameter,
partial-consistency truth, source-minChecked calibration, strict
time-constructible growth, nonzero exponent, and Buss-Pudlak rescaling, Lean
proves:

```lean
∃ N : Nat,
  endpointN = N ∧
  N =
    semanticStrongNatLowerBoundClassicalMonomialSearchWitness
      sourceLength hsource (max 17 sondowPrefixCoeff + 8) 1 0 ∧
  (max 17 sondowPrefixCoeff + 8) * (N + 1)^1 < sourceLength N
```

Here `hsource` is derived from source-minChecked calibration and the
Buss-Pudlak rescaling theorem inside the main theorem; it is not a separate
abstract premise of this endpoint.

## Companion Checked Results

- Finite Sondow prefix to MiniHilbert proof-code semantics:

```lean
S21GraftProofLengthRecognition_sondowPrefixMax_eq_miniHilbertMinProofCodeSizePrefixMax
```

- Half-denominator prefix obstruction:

```lean
not_sondowCheckedHalfDenPrefix_of_rationalParameter
```

- Numerical handoff for the later C-line root route:

```lean
finalScaleSizeTailGapExactProofGapEndpointCLineRootS21PudlakPA_computed_n_eq_max_thresholdOf
```

defined in:

```text
integration/SondowProjectMonth11Month12HardResidualElimination.lean
```

## Paper and Audit Materials

- English paper: `paper/paper_new_en.md`
- Chinese paper: `paper/paper_new_zh.md`
- World-class revision plan: `paper/world_class_revision_plan_zh.md`
- big-`N` audit plan: `docs/bigN_audit_plan_zh.md`
- General axiom ledger: `AXIOM_LEDGER.md`

## Not Claimed

- No unconditional proof of `gamma` irrationality is claimed.
- No printed decimal value of the big `N` is claimed.
- No claim is made that all project-level proof-complexity residuals are
  eliminated.
- The half-denominator checked-prefix premise is not treated as automatic.

## Next Research Targets

1. Implement or derive an executable `thresholdOf upper.U upper.polynomial`, or
   an equivalent executable witness extractor, to print a decimal `N`.
2. Continue auditing the recognition theorem, verifier traces,
   source-minChecked calibration, and Buss-Pudlak rescaling inputs.
3. Run and archive targeted `#check`, source-file elaboration, and
   `#print axioms` transcripts for the release.
4. Internalize or further document remaining proof-complexity residual inputs.

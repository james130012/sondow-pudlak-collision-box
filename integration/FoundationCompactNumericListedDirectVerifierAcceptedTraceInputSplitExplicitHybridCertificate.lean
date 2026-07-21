import integration.FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition

/-!
# Explicit checked certificate for the accepted input split

The proof and certificate slices are rebuilt from their two concrete token
lists.  Their existential row counts are respectively `proofTokens.length`
and `certificateTokens.length`; no semantic truth selector or abstract matrix
field supplies either witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplitExplicitHybridCertificate

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAValuationTermCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev InputSplitHybridCertificate (formula : ArithmeticProposition) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def compactNumericVerifierAcceptedTraceInputSplitDecomposedFormula
    (inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat) :
    ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm split) ≤
      !!(shortBinaryNumeralTerm inputTokenCount)” ⋏
    (compactFixedWidthCrossTableSlicesEqAtValuationFormula
        (shortBinaryNumeralTerm inputTable)
        (shortBinaryNumeralTerm inputWidth)
        (shortBinaryNumeralTerm inputTokenCount)
        (shortBinaryNumeralTerm 0)
        (shortBinaryNumeralTerm split)
        (shortBinaryNumeralTerm sourceTable)
        (shortBinaryNumeralTerm sourceWidth)
        (shortBinaryNumeralTerm sourceTokenCount)
        ‘!!(shortBinaryNumeralTerm proofStart) + 1’
        (shortBinaryNumeralTerm proofFinish) ⋏
      compactFixedWidthCrossTableSlicesEqAtValuationFormula
        (shortBinaryNumeralTerm inputTable)
        (shortBinaryNumeralTerm inputWidth)
        (shortBinaryNumeralTerm inputTokenCount)
        (shortBinaryNumeralTerm split)
        (shortBinaryNumeralTerm inputTokenCount)
        (shortBinaryNumeralTerm sourceTable)
        (shortBinaryNumeralTerm sourceWidth)
        (shortBinaryNumeralTerm sourceTokenCount)
        ‘!!(shortBinaryNumeralTerm certificateStart) + 1’
        (shortBinaryNumeralTerm certificateFinish))

theorem compactNumericVerifierAcceptedTraceInputSplitClosedFormula_eq_decomposed
    (inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat) :
    compactNumericVerifierAcceptedTraceInputSplitClosedFormula
        inputTable inputWidth inputTokenCount
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split =
      compactNumericVerifierAcceptedTraceInputSplitDecomposedFormula
        inputTable inputWidth inputTokenCount
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split := by
  unfold compactNumericVerifierAcceptedTraceInputSplitClosedFormula
  unfold compactNumericVerifierAcceptedTraceInputSplitDecomposedFormula
  unfold compactNumericVerifierAcceptedTraceInputSplitDef
  unfold compactFixedWidthCrossTableSlicesEqAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, arithmeticZeroTerm,
          LO.FirstOrder.Semiterm.Operator.operator,
          LO.FirstOrder.Semiterm.Operator.numeral_zero,
          LO.FirstOrder.Semiterm.Operator.numeral_one,
          LO.FirstOrder.Semiterm.Operator.Zero.term_eq,
          LO.FirstOrder.Semiterm.Operator.One.term_eq,
          LO.FirstOrder.Semiterm.Operator.Add.term_eq,
          Rew.func, Matrix.fun_eq_vec_two, Matrix.empty_eq]
    · intro index
      exact Empty.elim index
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left <= right) :
    InputSplitHybridCertificate
      “!!(shortBinaryNumeralTerm left) ≤ !!(shortBinaryNumeralTerm right)” := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm left
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm right
  if hequal : left = right then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq
        ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm =
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm]
            using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![leftTerm, rightTerm])
        equality
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct
  else
    have hstrict : left < right := Nat.lt_of_le_of_ne hle hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt
        ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm <
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm]
            using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm])
        strict
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation arithmeticZeroTerm = 0 := by
  exact termValue_zero valuation ![]

private theorem fixedCountData
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hcount : sourceFinish = sourceStart + count) :
    count <= sourceTokenCount /\
      count <= targetTokenCount /\
      targetFinish = targetStart + count /\
      sourceFinish <= sourceTokenCount /\
      targetFinish <= targetTokenCount /\
      ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
        (bitIndex < sourceWidth /\
            sourceTable.testBit
              ((sourceStart + offset) * sourceWidth + bitIndex) = true) <->
          (bitIndex < targetWidth /\
            targetTable.testBit
              ((targetStart + offset) * targetWidth + bitIndex) = true) := by
  rcases heq with
    ⟨actualCount, hsourceCount, htargetCount, hsourceEndpoint,
      htargetEndpoint, hsourceFinishBound, htargetFinishBound, hbits⟩
  have hactualCount : actualCount = count := by omega
  subst actualCount
  exact ⟨hsourceCount, htargetCount, htargetEndpoint,
    hsourceFinishBound, htargetFinishBound, hbits⟩

private noncomputable def canonicalProofSliceCertificate
    (proofTokens certificateTokens : List Nat) :
    let inputTokens := proofTokens ++ certificateTokens
    let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
    let proofEncoded := compactAdditiveEncode proofTokens
    let certificateEncoded := compactAdditiveEncode certificateTokens
    let sourceTokens := proofEncoded ++ certificateEncoded
    let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
    InputSplitHybridCertificate
      (compactFixedWidthCrossTableSlicesEqAtValuationFormula
        (shortBinaryNumeralTerm
          (compactFixedWidthTableCode inputWidth inputTokens))
        (shortBinaryNumeralTerm inputWidth)
        (shortBinaryNumeralTerm inputTokens.length)
        (shortBinaryNumeralTerm 0)
        (shortBinaryNumeralTerm proofTokens.length)
        (shortBinaryNumeralTerm
          (compactFixedWidthTableCode sourceWidth sourceTokens))
        (shortBinaryNumeralTerm sourceWidth)
        (shortBinaryNumeralTerm sourceTokens.length)
        ‘!!(shortBinaryNumeralTerm 0) + 1’
        (shortBinaryNumeralTerm proofEncoded.length)) := by
  dsimp only
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  have hcanonical :=
    compactNumericVerifierAcceptedTraceInputSplit_canonical
      proofTokens certificateTokens
  change CompactNumericVerifierAcceptedTraceInputSplit
      (compactFixedWidthTableCode inputWidth inputTokens)
      inputWidth inputTokens.length
      (compactFixedWidthTableCode sourceWidth sourceTokens)
      sourceWidth sourceTokens.length
      0 proofEncoded.length proofEncoded.length sourceTokens.length
      proofTokens.length at hcanonical
  rcases hcanonical with ⟨_hsplit, hproof, _hcertificate⟩
  rcases fixedCountData hproof (count := proofTokens.length) (by simp) with
    ⟨hsourceCount, htargetCount, htargetEndpoint,
      hsourceFinishBound, htargetFinishBound, hbits⟩
  exact compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
    zeroValuation
    (shortBinaryNumeralTerm
      (compactFixedWidthTableCode inputWidth inputTokens))
    (shortBinaryNumeralTerm inputWidth)
    (shortBinaryNumeralTerm inputTokens.length)
    (shortBinaryNumeralTerm 0)
    (shortBinaryNumeralTerm proofTokens.length)
    (shortBinaryNumeralTerm
      (compactFixedWidthTableCode sourceWidth sourceTokens))
    (shortBinaryNumeralTerm sourceWidth)
    (shortBinaryNumeralTerm sourceTokens.length)
    ‘!!(shortBinaryNumeralTerm 0) + 1’
    (shortBinaryNumeralTerm proofEncoded.length)
    proofTokens.length
    (by simpa [termValue_shortBinaryNumeralTerm] using hsourceCount)
    (by simpa [termValue_shortBinaryNumeralTerm] using htargetCount)
    (by simp [termValue_shortBinaryNumeralTerm, termValue_arithmeticZero])
    (by simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne, termValue_arithmeticZero]
        using htargetEndpoint)
    (by
      change inputTokens.length <= inputTokens.length
      exact hsourceFinishBound)
    (by
      change sourceTokens.length <= sourceTokens.length
      exact htargetFinishBound)
    (by simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne, termValue_arithmeticZero] using hbits)

private noncomputable def canonicalCertificateSliceCertificate
    (proofTokens certificateTokens : List Nat) :
    let inputTokens := proofTokens ++ certificateTokens
    let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
    let proofEncoded := compactAdditiveEncode proofTokens
    let certificateEncoded := compactAdditiveEncode certificateTokens
    let sourceTokens := proofEncoded ++ certificateEncoded
    let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
    InputSplitHybridCertificate
      (compactFixedWidthCrossTableSlicesEqAtValuationFormula
        (shortBinaryNumeralTerm
          (compactFixedWidthTableCode inputWidth inputTokens))
        (shortBinaryNumeralTerm inputWidth)
        (shortBinaryNumeralTerm inputTokens.length)
        (shortBinaryNumeralTerm proofTokens.length)
        (shortBinaryNumeralTerm inputTokens.length)
        (shortBinaryNumeralTerm
          (compactFixedWidthTableCode sourceWidth sourceTokens))
        (shortBinaryNumeralTerm sourceWidth)
        (shortBinaryNumeralTerm sourceTokens.length)
        ‘!!(shortBinaryNumeralTerm proofEncoded.length) + 1’
        (shortBinaryNumeralTerm sourceTokens.length)) := by
  dsimp only
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  have hcanonical :=
    compactNumericVerifierAcceptedTraceInputSplit_canonical
      proofTokens certificateTokens
  change CompactNumericVerifierAcceptedTraceInputSplit
      (compactFixedWidthTableCode inputWidth inputTokens)
      inputWidth inputTokens.length
      (compactFixedWidthTableCode sourceWidth sourceTokens)
      sourceWidth sourceTokens.length
      0 proofEncoded.length proofEncoded.length sourceTokens.length
      proofTokens.length at hcanonical
  rcases hcanonical with ⟨_hsplit, _hproof, hcertificate⟩
  have hsourceEndpoint :
      inputTokens.length = proofTokens.length + certificateTokens.length := by
    simp [inputTokens]
  rcases fixedCountData hcertificate
      (count := certificateTokens.length) hsourceEndpoint with
    ⟨hsourceCount, htargetCount, htargetEndpoint,
      hsourceFinishBound, htargetFinishBound, hbits⟩
  exact compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
    zeroValuation
    (shortBinaryNumeralTerm
      (compactFixedWidthTableCode inputWidth inputTokens))
    (shortBinaryNumeralTerm inputWidth)
    (shortBinaryNumeralTerm inputTokens.length)
    (shortBinaryNumeralTerm proofTokens.length)
    (shortBinaryNumeralTerm inputTokens.length)
    (shortBinaryNumeralTerm
      (compactFixedWidthTableCode sourceWidth sourceTokens))
    (shortBinaryNumeralTerm sourceWidth)
    (shortBinaryNumeralTerm sourceTokens.length)
    ‘!!(shortBinaryNumeralTerm proofEncoded.length) + 1’
    (shortBinaryNumeralTerm sourceTokens.length)
    certificateTokens.length
    (by simpa [termValue_shortBinaryNumeralTerm] using hsourceCount)
    (by simpa [termValue_shortBinaryNumeralTerm] using htargetCount)
    (by simpa [termValue_shortBinaryNumeralTerm] using hsourceEndpoint)
    (by simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using htargetEndpoint)
    (by simpa [termValue_shortBinaryNumeralTerm] using hsourceFinishBound)
    (by simpa [termValue_shortBinaryNumeralTerm] using htargetFinishBound)
    (by simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hbits)

def compactNumericVerifierAcceptedTraceInputSplitCanonicalClosedFormula
    (proofTokens certificateTokens : List Nat) : ArithmeticProposition :=
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  compactNumericVerifierAcceptedTraceInputSplitClosedFormula
    (compactFixedWidthTableCode inputWidth inputTokens)
    inputWidth inputTokens.length
    (compactFixedWidthTableCode sourceWidth sourceTokens)
    sourceWidth sourceTokens.length
    0 proofEncoded.length proofEncoded.length sourceTokens.length
    proofTokens.length

/-- Explicit certificate for the canonical public/input-state split. -/
noncomputable def
    compactNumericVerifierAcceptedTraceInputSplitCanonicalExplicitHybridCertificate
    (proofTokens certificateTokens : List Nat) :
    InputSplitHybridCertificate
      (compactNumericVerifierAcceptedTraceInputSplitCanonicalClosedFormula
    proofTokens certificateTokens) := by
  let inputTokens := proofTokens ++ certificateTokens
  let inputWidth := (compactBinaryNatPayloadBits inputTokens).length
  let proofEncoded := compactAdditiveEncode proofTokens
  let certificateEncoded := compactAdditiveEncode certificateTokens
  let sourceTokens := proofEncoded ++ certificateEncoded
  let sourceWidth := (compactBinaryNatPayloadBits sourceTokens).length
  unfold compactNumericVerifierAcceptedTraceInputSplitCanonicalClosedFormula
  dsimp only
  rw [compactNumericVerifierAcceptedTraceInputSplitClosedFormula_eq_decomposed]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLeCertificate proofTokens.length inputTokens.length (by
      simp [inputTokens]))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (canonicalProofSliceCertificate proofTokens certificateTokens)
      (canonicalCertificateSliceCertificate proofTokens certificateTokens))

theorem boundedWitnessInputSplitClosedFormula_eq_canonical
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    compactNumericVerifierAcceptedTraceInputSplitClosedFormula
        bounded.witness.inputTable bounded.witness.inputWidth
        bounded.witness.inputTokenCount bounded.witness.sourceTable
        bounded.witness.sourceWidth bounded.witness.sourceTokenCount
        bounded.witness.proofStart bounded.witness.proofFinish
        bounded.witness.certificateStart bounded.witness.certificateFinish
        bounded.witness.split =
      compactNumericVerifierAcceptedTraceInputSplitCanonicalClosedFormula
        bounded.proofTokens bounded.certificateTokens := by
  unfold compactNumericVerifierAcceptedTraceInputSplitCanonicalClosedFormula
  rw [bounded.inputTokenCount_eq, bounded.inputTable_eq,
    bounded.inputWidth_eq, bounded.sourceTokenCount_eq,
    bounded.sourceTable_eq, bounded.sourceWidth_eq,
    bounded.proofStart_eq, bounded.proofFinish_eq,
    bounded.certificateStart_eq, bounded.certificateFinish_eq,
    bounded.split_eq]

/-- Exact accepted-input split certificate on a bounded direct witness. -/
noncomputable def boundedWitnessInputSplitExplicitHybridCertificate
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    InputSplitHybridCertificate
      (compactNumericVerifierAcceptedTraceInputSplitClosedFormula
        bounded.witness.inputTable bounded.witness.inputWidth
        bounded.witness.inputTokenCount bounded.witness.sourceTable
        bounded.witness.sourceWidth bounded.witness.sourceTokenCount
        bounded.witness.proofStart bounded.witness.proofFinish
        bounded.witness.certificateStart bounded.witness.certificateFinish
        bounded.witness.split) :=
  .cast (boundedWitnessInputSplitClosedFormula_eq_canonical bounded).symm
    (compactNumericVerifierAcceptedTraceInputSplitCanonicalExplicitHybridCertificate
      bounded.proofTokens bounded.certificateTokens)

/-- Context proof compiled from the exact bounded-witness split certificate. -/
noncomputable def compileBoundedWitnessInputSplitExplicitHybridContext
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CertifiedPAContextProof
      (valuationContext
        (compactNumericVerifierAcceptedTraceInputSplitClosedFormula
          bounded.witness.inputTable bounded.witness.inputWidth
          bounded.witness.inputTokenCount bounded.witness.sourceTable
          bounded.witness.sourceWidth bounded.witness.sourceTokenCount
          bounded.witness.proofStart bounded.witness.proofFinish
          bounded.witness.certificateStart
          bounded.witness.certificateFinish
          bounded.witness.split).freeVariables zeroValuation)
      (compactNumericVerifierAcceptedTraceInputSplitClosedFormula
        bounded.witness.inputTable bounded.witness.inputWidth
        bounded.witness.inputTokenCount bounded.witness.sourceTable
        bounded.witness.sourceWidth bounded.witness.sourceTokenCount
        bounded.witness.proofStart bounded.witness.proofFinish
        bounded.witness.certificateStart bounded.witness.certificateFinish
        bounded.witness.split) :=
  (boundedWitnessInputSplitExplicitHybridCertificate bounded).compile

/-- Proof-free recursive structural resource for the exact split. -/
noncomputable def boundedWitnessInputSplitExplicitHybridStructuralResource
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (boundedWitnessInputSplitExplicitHybridCertificate bounded)

theorem compileBoundedWitnessInputSplitExplicitHybridContext_payloadLength_le
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    (compileBoundedWitnessInputSplitExplicitHybridContext bounded).payloadLength <=
      boundedWitnessInputSplitExplicitHybridStructuralResource bounded := by
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (boundedWitnessInputSplitExplicitHybridCertificate bounded)

#print axioms
  compactNumericVerifierAcceptedTraceInputSplitClosedFormula_eq_decomposed
#print axioms
  compactNumericVerifierAcceptedTraceInputSplitCanonicalExplicitHybridCertificate
#print axioms boundedWitnessInputSplitExplicitHybridCertificate
#print axioms compileBoundedWitnessInputSplitExplicitHybridContext
#print axioms
  compileBoundedWitnessInputSplitExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplitExplicitHybridCertificate

import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteResources

/-!
# Mode-one and mode-two public-finite term-output envelopes

This module isolates public-finite branch envelopes so Lean can elaborate and
cache each mode group without reopening the full checked branch proof file.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendOneValuePublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeOneShiftedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let twoShiftedResource := resources.twoShiftedResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
    (termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
      next argument)
    (oneTagGuardPayloadEnvelope consumedCount tag) twoShiftedResource
  let internal := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
        next argument)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘1’ : ValuationTerm)
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) internal
  let modesResource := termRowsModeOnePathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeOneRawPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let rawResource := resources.rawResource
  let doubleFailureResource := resources.doubleFailureResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag))
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount) doubleFailureResource rawResource
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
        next argument)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘1’ : ValuationTerm)
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) internal
  let modesResource := termRowsModeOnePathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoLowerPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let witnessResource := resources.witnessResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity)
    (termRowsWitnessFormula tokenTable width tokenCount current next
      witnessStart witnessFinish witnessCount)
    (zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity)
    witnessResource
  let internal := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsWitnessFormula tokenTable width tokenCount current next
        witnessStart witnessFinish witnessCount)
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘2’ : ValuationTerm)
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsWitnessFormula tokenTable width tokenCount current next
          witnessStart witnessFinish witnessCount) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) internal
  let modesResource := termRowsModeTwoPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoRawPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let rawResource := resources.rawResource
  let tripleFailureResource := resources.tripleFailureResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
      (shortBinaryNumeralTerm binderArity))
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount) tripleFailureResource rawResource
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsWitnessFormula tokenTable width tokenCount current next
        witnessStart witnessFinish witnessCount)
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘2’ : ValuationTerm)
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsWitnessFormula tokenTable width tokenCount current next
          witnessStart witnessFinish witnessCount) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) internal
  let modesResource := termRowsModeTwoPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

theorem
    compactFormulaTransformTermOutputRowsModeOneShiftedBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1))
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm argument)
            (‘1’ : ValuationTerm)) hrows <=
        resources.twoShiftedResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeOneShifted hcount hconsumed hmode hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeOneShiftedPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeOneShiftedPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeOnePathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeOneRawBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hfailureResource :
      doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
        resources.doubleFailureResource)
    (hrowsResource :
      compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows <= resources.rawResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeOneRaw hcount hconsumed hmode failure hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeOneRawPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeOneRawPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeOnePathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hfailureResource hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeTwoLowerBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputWitnessRows tokenTable width
      tokenCount current next witnessStart witnessFinish witnessCount)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable width
          tokenCount current.parserFinish current.finish current.outputCount
          witnessStart witnessFinish witnessCount next.parserFinish next.finish
          next.outputCount hrows <= resources.witnessResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeTwoLower hcount hconsumed hmode hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeTwoLowerPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoLowerPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeTwoPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeTwoRawBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hfailureResource :
      tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity failure <= resources.tripleFailureResource)
    (hrowsResource :
      compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows <= resources.rawResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeTwoRaw hcount hconsumed hmode failure hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeTwoRawPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoRawPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeTwoPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hfailureResource hrowsResource)

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

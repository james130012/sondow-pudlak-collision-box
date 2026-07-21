import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteResources

/-!
# Mode-zero public-finite term-output envelopes

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
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroLowerPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let twoOneZeroResource := resources.twoOneZeroResource
  let guardRows := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity)
    (termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
      next)
    (zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity)
    twoOneZeroResource
  let internal := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
        next)
    ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount
            current next argument)) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) guardRows
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘0’ : ValuationTerm)
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
          next) ⋎
      ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount
              current next argument)) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current
              next consumedCount)))) internal
  let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroShiftedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let twoShiftedResource := resources.twoShiftedResource
  let tripleFailureResource := resources.tripleFailureResource
  let guardRows := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
    (termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
      next argument)
    (oneTagGuardPayloadEnvelope consumedCount tag) twoShiftedResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
      (shortBinaryNumeralTerm binderArity))
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
        next argument)
    tripleFailureResource guardRows
  let middle := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      (termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument))
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) selected
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
        next)
    ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount
            current next argument)) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) middle
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘0’ : ValuationTerm)
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
          next) ⋎
      ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount
              current next argument)) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current
              next consumedCount)))) internal
  let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroRawPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let rawResource := resources.rawResource
  let tripleFailureResource := resources.tripleFailureResource
  let doubleFailureResource := resources.doubleFailureResource
  let shiftRows := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag))
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount) doubleFailureResource rawResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
      (shortBinaryNumeralTerm binderArity))
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount)
    tripleFailureResource shiftRows
  let middle := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      (termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsAppendTwoShiftedFormula tokenTable width tokenCount current
          next argument))
    (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
        (shortBinaryNumeralTerm binderArity) ⋏
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) selected
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
      termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
        next)
    ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (termRowsGuardOneTagFormula consumedCount tag ⋏
          termRowsAppendTwoShiftedFormula tokenTable width tokenCount
            current next argument)) ⋎
      (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
          (shortBinaryNumeralTerm binderArity) ⋏
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) middle
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘0’ : ValuationTerm)
    ((termRowsGuardZeroTagFormula consumedCount tag argument binderArity ⋏
        termRowsAppendTwoOneZeroFormula tokenTable width tokenCount current
          next) ⋎
      ((tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (termRowsGuardOneTagFormula consumedCount tag ⋏
            termRowsAppendTwoShiftedFormula tokenTable width tokenCount
              current next argument)) ⋎
        (tripleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) (shortBinaryNumeralTerm argument)
            (shortBinaryNumeralTerm binderArity) ⋏
          (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
              (shortBinaryNumeralTerm tag) ⋏
            termRowsRawPrefixFormula tokenTable width tokenCount current
              next consumedCount)))) internal
  let modesResource := termRowsModeZeroPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

theorem
    compactFormulaTransformTermOutputRowsModeZeroLowerBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧ argument + 1 = binderArity)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 0)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 0 (‘1’ : ValuationTerm)
          (‘0’ : ValuationTerm) hrows <=
        resources.twoOneZeroResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeZeroLower hcount hconsumed hmode hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeZeroLowerPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroLowerPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeZeroPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeZeroShiftedBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (failure : TripleFailureCheckedData consumedCount tag argument binderArity)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1))
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hfailureResource :
      tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity failure <= resources.tripleFailureResource)
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
        (.modeZeroShifted hcount hconsumed hmode failure hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeZeroShiftedPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroShiftedPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeZeroPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        hfailureResource
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
          hrowsResource)))

theorem
    compactFormulaTransformTermOutputRowsModeZeroRawBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (lowerFailure : TripleFailureCheckedData consumedCount tag argument
      binderArity)
    (shiftFailure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hlowerResource :
      tripleFailurePayloadEnvelopeFromData consumedCount tag argument
          binderArity lowerFailure <= resources.tripleFailureResource)
    (hshiftResource :
      doubleFailurePayloadEnvelopeFromData consumedCount tag shiftFailure <=
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
        (.modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeZeroRawPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroRawPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeZeroPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        hlowerResource
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hshiftResource hrowsResource)))

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteResources

/-!
# Mode-four and mode-five public-finite term-output envelopes

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
    compactFormulaTransformTermOutputRowsPublicBranchModeFourOnePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let oneValueResource := resources.oneValueResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation (termRowsGuardOneTagFormula consumedCount tag)
    (termRowsOneValueFormula tokenTable width tokenCount current next
      argument)
    (oneTagGuardPayloadEnvelope consumedCount tag) oneValueResource
  let internal := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsOneValueFormula tokenTable width tokenCount current next
        argument)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsSameFormula tokenTable width tokenCount current next) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘4’ : ValuationTerm)
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsOneValueFormula tokenTable width tokenCount current next
          argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsSameFormula tokenTable width tokenCount current next))
    internal
  let modesResource := termRowsModeFourPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeFourSamePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let sameResource := resources.sameResource
  let doubleFailureResource := resources.doubleFailureResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm tag))
    (termRowsSameFormula tokenTable width tokenCount current next)
    doubleFailureResource sameResource
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsGuardOneTagFormula consumedCount tag ⋏
      termRowsOneValueFormula tokenTable width tokenCount current next
        argument)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsSameFormula tokenTable width tokenCount current next) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘4’ : ValuationTerm)
    ((termRowsGuardOneTagFormula consumedCount tag ⋏
        termRowsOneValueFormula tokenTable width tokenCount current next
          argument) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsSameFormula tokenTable width tokenCount current next))
    internal
  let modesResource := termRowsModeFourPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveCapturedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let capturedResource := resources.capturedResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (termRowsCapturedGuardFormula consumedCount tag argument witnessCount)
    (termRowsCapturedFormula tokenTable width tokenCount current next
      binderArity argument)
    (capturedGuardPayloadEnvelope consumedCount tag argument witnessCount)
    capturedResource
  let internal := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
      termRowsCapturedFormula tokenTable width tokenCount current next
        binderArity argument)
    ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
        compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) selected
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘5’ : ValuationTerm)
    ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) ⋎
      ((termRowsResidualGuardFormula consumedCount tag argument
            witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) internal
  let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveResidualPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let modeTerm := shortBinaryNumeralTerm mode
  let residualResource := resources.residualResource
  let selected := transparentHybridConjunctionPayloadEnvelope
    termRowsZeroValuation
    (termRowsResidualGuardFormula consumedCount tag argument witnessCount)
    (compactFormulaTransformTermResidualExistsFormula tokenTable width
      tokenCount current next argument witnessCount)
    (residualGuardPayloadEnvelope consumedCount tag argument witnessCount)
    residualResource
  let middle := transparentHybridDisjunctionLeftPayloadEnvelope
    termRowsZeroValuation
    (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
      compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
      termRowsCapturedFormula tokenTable width tokenCount current next
        binderArity argument)
    ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
        compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) middle
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘5’ : ValuationTerm)
    ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) ⋎
      ((termRowsResidualGuardFormula consumedCount tag argument
            witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) internal
  let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveRawPayloadEnvelope
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
  let middle := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
      compactFormulaTransformTermResidualExistsFormula tokenTable width
        tokenCount current next argument witnessCount)
    (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm tag) ⋏
      termRowsRawPrefixFormula tokenTable width tokenCount current next
        consumedCount) selected
  let internal := transparentHybridDisjunctionRightPayloadEnvelope
    termRowsZeroValuation
    (termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
      termRowsCapturedFormula tokenTable width tokenCount current next
        binderArity argument)
    ((termRowsResidualGuardFormula consumedCount tag argument witnessCount ⋏
        compactFormulaTransformTermResidualExistsFormula tokenTable width
          tokenCount current next argument witnessCount) ⋎
      (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm tag) ⋏
        termRowsRawPrefixFormula tokenTable width tokenCount current next
          consumedCount)) middle
  let modeResource := termRowsModeOuterPayloadEnvelope modeTerm
    (‘5’ : ValuationTerm)
    ((termRowsCapturedGuardFormula consumedCount tag argument witnessCount ⋏
        termRowsCapturedFormula tokenTable width tokenCount current next
          binderArity argument) ⋎
      ((termRowsResidualGuardFormula consumedCount tag argument
            witnessCount ⋏
          compactFormulaTransformTermResidualExistsFormula tokenTable width
            tokenCount current next argument witnessCount) ⋎
        (doubleFailureFormula (shortBinaryNumeralTerm consumedCount)
            (shortBinaryNumeralTerm tag) ⋏
          termRowsRawPrefixFormula tokenTable width tokenCount current next
            consumedCount))) internal
  let modesResource := termRowsModeFivePathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount modeResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

theorem
    compactFormulaTransformTermOutputRowsModeFourOneBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hrows : CompactFormulaTransformOutputOneValueRows tokenTable width
      tokenCount current next argument)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendOneValueGraphPayloadEnvelope tokenTable width
          tokenCount current.parserFinish current.finish current.outputCount
          next.parserFinish next.finish next.outputBoundary next.outputCount
          argument hrows <= resources.oneValueResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFourOne hcount hconsumed hmode hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeFourOnePayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeFourOnePayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeFourPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeFourSameBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 4)
    (failure : DoubleFailureCheckedData consumedCount tag)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hfailureResource :
      doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
        resources.doubleFailureResource)
    (hrowsResource :
      compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows <=
        resources.sameResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFourSame hcount hconsumed hmode failure hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeFourSamePayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeFourSamePayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeFourPathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      hfailureResource hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeFiveCapturedBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 0 (binderArity + argument))
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
          (nativeAddTerm (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm argument)) hrows <=
        resources.capturedResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFiveCaptured hcount hconsumed hmode hguard hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeFiveCapturedPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveCapturedPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeFivePathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      hrowsResource)

theorem
    compactFormulaTransformTermOutputRowsModeFiveResidualBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount residual : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount <= argument)
    (hresidual : residual <= argument)
    (hequality : argument = witnessCount + residual)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 residual)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hresidualResource :
      compactFormulaTransformTermResidualExistsPayloadEnvelope tokenTable width
          tokenCount current next argument witnessCount residual hrows <=
        resources.residualResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.modeFiveResidual hcount hconsumed hmode hguard residual hresidual
          hequality hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeFiveResidualPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveResidualPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeFivePathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        hresidualResource))

theorem
    compactFormulaTransformTermOutputRowsModeFiveRawBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
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
        (.modeFiveRaw hcount hconsumed hmode failure hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchModeFiveRawPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveRawPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsModeFivePathPayloadEnvelope_mono
  apply termRowsModeOuterPayloadEnvelope_mono
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        hfailureResource hrowsResource))

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

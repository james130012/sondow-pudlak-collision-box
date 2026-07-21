import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

/-!
# Public-finite resources for formula-transform term output rows

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

structure CompactFormulaTransformTermOutputRowsPublicResources where
  sameResource : Nat
  rawResource : Nat
  twoOneZeroResource : Nat
  twoShiftedResource : Nat
  witnessResource : Nat
  oneValueResource : Nat
  capturedResource : Nat
  residualResource : Nat
  tripleFailureResource : Nat
  doubleFailureResource : Nat


noncomputable def
    compactFormulaTransformTermOutputRowsPublicResources
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) :
    CompactFormulaTransformTermOutputRowsPublicResources :=
  let sameResource :=
    compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.outputBoundary current.outputCount next.outputBoundary
      next.outputCount
  let rawResource :=
    compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount current.start current.parserTokensFinish
      current.parserTokensCount consumedCount next.parserFinish next.finish
      next.outputCount
  let twoOneZeroResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm) (‘0’ : ValuationTerm)
  let twoShiftedResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘1’ : ValuationTerm)
      (nativeAddTerm (shortBinaryNumeralTerm argument)
        (‘1’ : ValuationTerm))
  let witnessResource :=
    compactAdditiveNatListAppendSlicesPublicFinitePayloadEnvelope tokenTable
      width tokenCount current.parserFinish current.finish current.outputCount
      witnessStart witnessFinish witnessCount next.parserFinish next.finish
      next.outputCount
  let oneValueResource :=
    compactAdditiveNatListAppendOneValuePublicFinitePayloadEnvelope tokenTable
      width tokenCount current.parserFinish current.finish current.outputCount
      next.parserFinish next.finish next.outputBoundary next.outputCount argument
  let capturedResource :=
    compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount (‘0’ : ValuationTerm)
      (nativeAddTerm (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm argument))
  let residualResource :=
    compactFormulaTransformTermResidualExistsPublicFinitePayloadEnvelope
      tokenTable width tokenCount current next argument witnessCount
  let tripleFailureResource := tripleFailurePublicFinitePayloadEnvelope
    consumedCount tag argument binderArity
  let doubleFailureResource := doubleFailurePublicFinitePayloadEnvelope
    consumedCount tag
  { sameResource := sameResource
    rawResource := rawResource
    twoOneZeroResource := twoOneZeroResource
    twoShiftedResource := twoShiftedResource
    witnessResource := witnessResource
    oneValueResource := oneValueResource
    capturedResource := capturedResource
    residualResource := residualResource
    tripleFailureResource := tripleFailureResource
    doubleFailureResource := doubleFailureResource }

noncomputable def
    compactFormulaTransformTermOutputRowsPublicBranchZeroPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let sameResource := resources.sameResource
  termRowsZeroSelectedPayloadEnvelope tokenTable width tokenCount current
    next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount sameResource

theorem
    compactFormulaTransformTermOutputRowsZeroBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : consumedCount = 0)
    (hsame : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hsameResource :
      compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hsame <=
        resources.sameResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.zero hcount hconsumed hsame) <=
      compactFormulaTransformTermOutputRowsPublicBranchZeroPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchZeroPayloadEnvelope
  exact termRowsZeroSelectedPayloadEnvelope_mono tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount hsameResource

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

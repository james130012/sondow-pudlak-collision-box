import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteModeZero
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteModeOneTwo
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteModeFourFive

/-!
# Aggregated public-finite term-output envelope

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
    compactFormulaTransformTermOutputRowsPublicBranchOtherPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources) : Nat :=
  let rawResource := resources.rawResource
  let otherResource := otherModesWithTailPayloadEnvelope mode
    (termRowsRawPrefixFormula tokenTable width tokenCount current next
      consumedCount) rawResource
  let modesResource := termRowsOtherPathPayloadEnvelope tokenTable width
    tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount otherResource
  termRowsPositiveSelectedPayloadEnvelope tokenTable width tokenCount
    current next mode binderArity tag argument consumedCount witnessStart
    witnessFinish witnessCount modesResource

noncomputable def
    compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat) : Nat :=
  let resources := compactFormulaTransformTermOutputRowsPublicResources
    tokenTable width tokenCount current next binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount
  let zeroBranch :=
    compactFormulaTransformTermOutputRowsPublicBranchZeroPayloadEnvelope
    tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount resources
  let modeZeroLower :=
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroLowerPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeZeroShifted :=
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroShiftedPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeZeroRaw :=
    compactFormulaTransformTermOutputRowsPublicBranchModeZeroRawPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeOneShifted :=
    compactFormulaTransformTermOutputRowsPublicBranchModeOneShiftedPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeOneRaw :=
    compactFormulaTransformTermOutputRowsPublicBranchModeOneRawPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeTwoLower :=
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoLowerPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeTwoRaw :=
    compactFormulaTransformTermOutputRowsPublicBranchModeTwoRawPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeFourOne :=
    compactFormulaTransformTermOutputRowsPublicBranchModeFourOnePayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeFourSame :=
    compactFormulaTransformTermOutputRowsPublicBranchModeFourSamePayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeFiveCaptured :=
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveCapturedPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeFiveResidual :=
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveResidualPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let modeFiveRaw :=
    compactFormulaTransformTermOutputRowsPublicBranchModeFiveRawPayloadEnvelope
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources
  let other := compactFormulaTransformTermOutputRowsPublicBranchOtherPayloadEnvelope
    tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount resources
  zeroBranch + modeZeroLower + modeZeroShifted + modeZeroRaw + modeOneShifted +
    modeOneRaw + modeTwoLower + modeTwoRaw + modeFourOne + modeFourSame +
    modeFiveCaptured + modeFiveResidual + modeFiveRaw + other

theorem
    compactFormulaTransformTermOutputRowsOtherBranchPayloadEnvelope_le_publicBranch
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hzero : mode ≠ 0)
    (hone : mode ≠ 1)
    (htwo : mode ≠ 2)
    (hfour : mode ≠ 4)
    (hfive : mode ≠ 5)
    (hrows : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (resources : CompactFormulaTransformTermOutputRowsPublicResources)
    (hrowsResource :
      compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
          width tokenCount current.parserFinish current.finish
          current.outputCount current.start current.parserTokensFinish
          current.parserTokensCount consumedCount next.parserFinish next.finish
          next.outputCount hrows <= resources.rawResource) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount
        (.other hcount hconsumed hzero hone htwo hfour hfive hrows) <=
      compactFormulaTransformTermOutputRowsPublicBranchOtherPayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount resources := by
  unfold compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
    compactFormulaTransformTermOutputRowsPublicBranchOtherPayloadEnvelope
  apply termRowsPositiveSelectedPayloadEnvelope_mono
  apply termRowsOtherPathPayloadEnvelope_mono
  exact otherModesWithTailPayloadEnvelope_mono mode _ hrowsResource

theorem
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount) :
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount data <=
      compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount := by
  let resources := compactFormulaTransformTermOutputRowsPublicResources
    tokenTable width tokenCount current next binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount
  cases data with
  | zero hcount hconsumed hsame =>
      have hsameResource :
          compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
              tokenCount current.outputBoundary current.outputCount
              next.outputBoundary next.outputCount hsame <=
            resources.sameResource := by
        change compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable
            width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount hsame <=
          compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable
            width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount
        exact compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hsame
      have hbranch :=
        compactFormulaTransformTermOutputRowsZeroBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hsame resources hsameResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeZeroLower hcount hconsumed hmode hguard hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount next.parserFinish next.finish
              next.outputBoundary next.outputCount 1 0
              (‘1’ : ValuationTerm) (‘0’ : ValuationTerm) hrows <=
            resources.twoOneZeroResource := by
        change _ <=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘1’ : ValuationTerm)
            (‘0’ : ValuationTerm)
        exact
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount 1 0
            (‘1’ : ValuationTerm) (‘0’ : ValuationTerm) hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeZeroLowerBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeZeroShifted hcount hconsumed hmode failure hguard hrows =>
      have hfailureResource :
          tripleFailurePayloadEnvelopeFromData consumedCount tag argument
              binderArity failure <= resources.tripleFailureResource := by
        change tripleFailurePayloadEnvelopeFromData consumedCount tag argument
            binderArity failure <=
          tripleFailurePublicFinitePayloadEnvelope consumedCount tag argument
            binderArity
        exact tripleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag argument binderArity failure
      have hrowsResource :
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount next.parserFinish next.finish
              next.outputBoundary next.outputCount 1 (argument + 1)
              (‘1’ : ValuationTerm)
              (nativeAddTerm (shortBinaryNumeralTerm argument)
                (‘1’ : ValuationTerm)) hrows <=
            resources.twoShiftedResource := by
        change _ <=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm))
        exact
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount 1 (argument + 1)
            (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm)) hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeZeroShiftedBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hguard hrows resources hfailureResource
          hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows =>
      have hlowerResource :
          tripleFailurePayloadEnvelopeFromData consumedCount tag argument
              binderArity lowerFailure <= resources.tripleFailureResource := by
        change tripleFailurePayloadEnvelopeFromData consumedCount tag argument
            binderArity lowerFailure <=
          tripleFailurePublicFinitePayloadEnvelope consumedCount tag argument
            binderArity
        exact tripleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag argument binderArity lowerFailure
      have hshiftResource :
          doubleFailurePayloadEnvelopeFromData consumedCount tag shiftFailure <=
            resources.doubleFailureResource := by
        change doubleFailurePayloadEnvelopeFromData consumedCount tag
            shiftFailure <=
          doubleFailurePublicFinitePayloadEnvelope consumedCount tag
        exact doubleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag shiftFailure
      have hrowsResource :
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputCount hrows <= resources.rawResource := by
        change _ <=
          compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount
        exact
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeZeroRawBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode lowerFailure shiftFailure hrows resources
          hlowerResource hshiftResource hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeOneShifted hcount hconsumed hmode hguard hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount next.parserFinish next.finish
              next.outputBoundary next.outputCount 1 (argument + 1)
              (‘1’ : ValuationTerm)
              (nativeAddTerm (shortBinaryNumeralTerm argument)
                (‘1’ : ValuationTerm)) hrows <=
            resources.twoShiftedResource := by
        change _ <=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm))
        exact
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount 1 (argument + 1)
            (‘1’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm argument)
              (‘1’ : ValuationTerm)) hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeOneShiftedBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeOneRaw hcount hconsumed hmode failure hrows =>
      have hfailureResource :
          doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
            resources.doubleFailureResource := by
        change doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
          doubleFailurePublicFinitePayloadEnvelope consumedCount tag
        exact doubleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag failure
      have hrowsResource :
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputCount hrows <= resources.rawResource := by
        change _ <=
          compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount
        exact
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeOneRawBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows resources hfailureResource
          hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeTwoLower hcount hconsumed hmode hguard hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendSlicesGraphPayloadEnvelope tokenTable
              width tokenCount current.parserFinish current.finish
              current.outputCount witnessStart witnessFinish witnessCount
              next.parserFinish next.finish next.outputCount hrows <=
            resources.witnessResource := by
        change _ <= compactAdditiveNatListAppendSlicesPublicFinitePayloadEnvelope
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount witnessStart witnessFinish witnessCount
          next.parserFinish next.finish next.outputCount
        exact compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount witnessStart witnessFinish witnessCount
          next.parserFinish next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeTwoLowerBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeTwoRaw hcount hconsumed hmode failure hrows =>
      have hfailureResource :
          tripleFailurePayloadEnvelopeFromData consumedCount tag argument
              binderArity failure <= resources.tripleFailureResource := by
        change tripleFailurePayloadEnvelopeFromData consumedCount tag argument
            binderArity failure <=
          tripleFailurePublicFinitePayloadEnvelope consumedCount tag argument
            binderArity
        exact tripleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag argument binderArity failure
      have hrowsResource :
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputCount hrows <= resources.rawResource := by
        change _ <=
          compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount
        exact
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeTwoRawBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows resources hfailureResource
          hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeFourOne hcount hconsumed hmode hguard hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendOneValueGraphPayloadEnvelope tokenTable
              width tokenCount current.parserFinish current.finish
              current.outputCount next.parserFinish next.finish
              next.outputBoundary next.outputCount argument hrows <=
            resources.oneValueResource := by
        change _ <=
          compactAdditiveNatListAppendOneValuePublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount argument
        exact
          compactAdditiveNatListAppendOneValueGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount argument hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeFourOneBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeFourSame hcount hconsumed hmode failure hrows =>
      have hfailureResource :
          doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
            resources.doubleFailureResource := by
        change doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
          doubleFailurePublicFinitePayloadEnvelope consumedCount tag
        exact doubleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag failure
      have hrowsResource :
          compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
              tokenCount current.outputBoundary current.outputCount
              next.outputBoundary next.outputCount hrows <=
            resources.sameResource := by
        change _ <=
          compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable
            width tokenCount current.outputBoundary current.outputCount
            next.outputBoundary next.outputCount
        exact compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeFourSameBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows resources hfailureResource
          hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeFiveCaptured hcount hconsumed hmode hguard hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount next.parserFinish next.finish
              next.outputBoundary next.outputCount 0 (binderArity + argument)
              (‘0’ : ValuationTerm)
              (nativeAddTerm (shortBinaryNumeralTerm binderArity)
                (shortBinaryNumeralTerm argument)) hrows <=
            resources.capturedResource := by
        change _ <=
          compactAdditiveNatListAppendTwoValuesAtValuationValuesPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount (‘0’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm argument))
        exact
          compactAdditiveNatListAppendTwoValuesAtValuationValuesGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount next.parserFinish next.finish
            next.outputBoundary next.outputCount 0 (binderArity + argument)
            (‘0’ : ValuationTerm)
            (nativeAddTerm (shortBinaryNumeralTerm binderArity)
              (shortBinaryNumeralTerm argument)) hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeFiveCapturedBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeFiveResidual hcount hconsumed hmode hguard residual hresidual hequality
      hrows =>
      have hresidualResource :
          compactFormulaTransformTermResidualExistsPayloadEnvelope tokenTable
              width tokenCount current next argument witnessCount residual
              hrows <= resources.residualResource := by
        change _ <=
          compactFormulaTransformTermResidualExistsPublicFinitePayloadEnvelope
            tokenTable width tokenCount current next argument witnessCount
        exact
          compactFormulaTransformTermResidualExistsPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current next argument witnessCount
            residual hresidual hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeFiveResidualBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount residual hcount
          hconsumed hmode hguard hresidual hequality hrows resources
          hresidualResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | modeFiveRaw hcount hconsumed hmode failure hrows =>
      have hfailureResource :
          doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
            resources.doubleFailureResource := by
        change doubleFailurePayloadEnvelopeFromData consumedCount tag failure <=
          doubleFailurePublicFinitePayloadEnvelope consumedCount tag
        exact doubleFailurePayloadEnvelopeFromData_le_publicFinite
          consumedCount tag failure
      have hrowsResource :
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputCount hrows <= resources.rawResource := by
        change _ <=
          compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount
        exact
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsModeFiveRawBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows resources hfailureResource
          hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega
  | other hcount hconsumed hzero hone htwo hfour hfive hrows =>
      have hrowsResource :
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
              tokenTable width tokenCount current.parserFinish current.finish
              current.outputCount current.start current.parserTokensFinish
              current.parserTokensCount consumedCount next.parserFinish
              next.finish next.outputCount hrows <= resources.rawResource := by
        change _ <=
          compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount
        exact
          compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.parserFinish current.finish
            current.outputCount current.start current.parserTokensFinish
            current.parserTokensCount consumedCount next.parserFinish
            next.finish next.outputCount hrows
      have hbranch :=
        compactFormulaTransformTermOutputRowsOtherBranchPayloadEnvelope_le_publicBranch
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hzero hone htwo hfour hfive hrows resources hrowsResource
      refine hbranch.trans ?_
      unfold compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
      dsimp only [resources]
      omega


end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

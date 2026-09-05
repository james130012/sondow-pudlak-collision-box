import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate

/-! # Public seven-leaf formula for formula-transform endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFormula
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate

def compactFormulaTransformInitialParserSourcePublicFormula
    (tokenTable width tokenCount inputBoundary inputCount binderArity : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserInitialStateRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.parserFinish,
      shortBinaryNumeralTerm coordinates.parserTokensFinish,
      shortBinaryNumeralTerm coordinates.parserTasksFinish,
      shortBinaryNumeralTerm coordinates.parserTokensBoundary,
      shortBinaryNumeralTerm coordinates.parserTokensCount,
      shortBinaryNumeralTerm coordinates.parserTasksBoundary,
      shortBinaryNumeralTerm coordinates.parserTasksCount,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      (‘1’ : ValuationTerm),
      shortBinaryNumeralTerm binderArity,
      (‘0’ : ValuationTerm)]

def compactFormulaTransformInitialFinalRowsPublicExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1” ⋏
    (compactFormulaTransformStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount 0
        witness.initialCoordinates witness.initialSizeWitness ⋏
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
          tokenCount inputBoundary inputCount binderArity
          witness.initialCoordinates ⋏
        (“!!(shortBinaryNumeralTerm witness.initialCoordinates.outputCount) =
            0” ⋏
          (compactFormulaTransformStateAtRowsClosedFormula
              tokenTable width tokenCount stateBoundary stateCount fuel
              witness.finalCoordinates witness.finalSizeWitness ⋏
            (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
                tokenCount witness.finalCoordinates.parser
                expectedSuffixBoundary expectedSuffixCount
                witness.finalParserOutputStart witness.finalParserOutputBoundary
                witness.finalParserOutputBoundarySize ⋏
              compactAdditiveNatListSameRowsClosedFormula tokenTable width
                tokenCount expectedOutputBoundary expectedOutputCount
                witness.finalCoordinates.outputBoundary
                witness.finalCoordinates.outputCount)))))

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax

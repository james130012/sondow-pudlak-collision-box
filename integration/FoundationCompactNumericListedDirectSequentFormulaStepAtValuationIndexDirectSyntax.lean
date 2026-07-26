import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment

/-! # Twenty-one direct conjuncts for an open sequent-step row index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

def compactSequentFormulaStepIndexSuccessorTermAtValuation
    (indexTerm : ValuationTerm) : ValuationTerm :=
  ‘!!indexTerm + 1’

def compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
    (indexTerm : ValuationTerm) : ValuationTerm :=
  ‘!!indexTerm + 2’

def compactSequentFormulaStepDirectPartsFormulaAtValuationIndex
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm row.current.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.current.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.current.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      indexTerm
      (shortBinaryNumeralTerm row.current.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm)
      (shortBinaryNumeralTerm row.current.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm)
      (shortBinaryNumeralTerm row.next.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation indexTerm)
      (shortBinaryNumeralTerm row.next.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      indexTerm
      (shortBinaryNumeralTerm row.value.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm)
      (shortBinaryNumeralTerm row.value.finish) ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.next.start row.next.count row.next.finish row.next.boundary
      row.next.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.value.start row.value.count row.value.finish row.value.boundary
      row.value.boundarySize ⋏
  (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
      row.parserStateBoundary row.current.boundary
      row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound ⋏
  (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count
      row.current.start row.current.finish row.current.count ⋏
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”)))))))))))))))))))

theorem compactSequentFormulaStepDirectFormulaAtValuationIndex_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        indexTerm row =
      compactSequentFormulaStepDirectPartsFormulaAtValuationIndex tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        indexTerm row := by
  simp [compactSequentFormulaStepDirectFormulaAtValuationIndex,
    compactSequentFormulaStepDirectPublicTermsAtValuationIndex,
    compactSequentFormulaStepDirectPartsFormulaAtValuationIndex,
    compactSequentFormulaStepDef,
    compactSequentFormulaStepIndexSuccessorTermAtValuation,
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation,
    compactFixedWidthEntryAtValuationFormula,
    compactAdditiveNatListWitnessRowsClosedFormula,
    compactSequentFormulaStepParserClosedFormula,
    compactSequentFormulaStepParserPublicTerms,
    compactAdditiveNatListAppendSlicesClosedFormula,
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution,
    FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuelTerm,
    FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactNativeNumeralTerm,
    Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp

#print axioms
  compactSequentFormulaStepDirectFormulaAtValuationIndex_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax

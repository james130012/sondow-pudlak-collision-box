import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSourceAlignment

/-!
# Branch formulas for verifier task-list rows

This cached syntax layer names the formula below the fourteen bounded row
witnesses and its concrete three-conjunct specialization.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-- The conjunction remaining below all fourteen row witnesses. -/
def compactNumericVerifierTaskListRowsBranchTerminal
    (tokenTable width tokenCount taskBoundary : Nat)
    (rowIndexTerm : ValuationTerm) : ArithmeticSemiformula Nat 14 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
        closedShift 14 (shortBinaryNumeralTerm tokenCount),
        closedShift 14 rowIndexTerm,
        (#13 : ArithmeticSemiterm Nat 14)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          closedShift 14 (‘!!rowIndexTerm + 1’ : ValuationTerm),
          (#12 : ArithmeticSemiterm Nat 14)]) ⋏
      ((Rewriting.emb (ξ := Nat)
          compactNumericVerifierTaskCoreGraphDef.val) ⇜
        ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
          closedShift 14 (shortBinaryNumeralTerm width),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8,
          #7, #6, #5, #4, #3, #2, #1, #0]))

/-- The three terminal conjuncts after all row witnesses are installed. -/
def compactNumericVerifierTaskListRowsTerminalPartsFormula
    (tokenTable width tokenCount taskBoundary
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm taskBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (&0 : ValuationTerm)
      (shortBinaryNumeralTerm start) ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm taskBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm finish) ⋏
      compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          start finish tag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize })

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

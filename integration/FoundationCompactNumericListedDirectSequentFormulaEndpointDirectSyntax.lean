import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

/-! # Direct closed syntax for the 27-coordinate sequent-formula endpoint -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def compactSequentFormulaEndpointDirectClosedFormula
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaEndpointGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm inputStart,
      shortBinaryNumeralTerm inputFinish,
      shortBinaryNumeralTerm valueStart,
      shortBinaryNumeralTerm valueFinish,
      shortBinaryNumeralTerm finalStart,
      shortBinaryNumeralTerm finalFinish,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.firstStart,
      shortBinaryNumeralTerm coordinates.firstFinish,
      shortBinaryNumeralTerm coordinates.firstBoundary,
      shortBinaryNumeralTerm coordinates.firstCount,
      shortBinaryNumeralTerm coordinates.firstBoundarySize,
      shortBinaryNumeralTerm coordinates.suffixBoundary,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm coordinates.valueBoundary,
      shortBinaryNumeralTerm coordinates.valueCount,
      shortBinaryNumeralTerm coordinates.valueBoundarySize,
      shortBinaryNumeralTerm coordinates.finalBoundary,
      shortBinaryNumeralTerm coordinates.finalCount,
      shortBinaryNumeralTerm coordinates.finalBoundarySize,
      shortBinaryNumeralTerm coordinates.traceTableWidth,
      shortBinaryNumeralTerm coordinates.traceValueBound]

def compactSequentFormulaEndpointDirectExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize ⋏
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        coordinates.firstStart coordinates.firstCount coordinates.firstFinish
        coordinates.firstBoundary coordinates.firstBoundarySize ⋏
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
          tokenCount finalStart coordinates.finalCount finalFinish
          coordinates.finalBoundary coordinates.finalBoundarySize ⋏
        (compactSequentFormulaTraceBoundedDirectClosedFormula tokenTable width
            tokenCount coordinates.suffixBoundary coordinates.suffixCount
            coordinates.valueBoundary coordinates.valueCount
            coordinates.traceTableWidth coordinates.traceValueBound ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm coordinates.suffixBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘0’ : ValuationTerm)
              (shortBinaryNumeralTerm coordinates.firstStart) ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm coordinates.suffixBoundary)
                (shortBinaryNumeralTerm tokenCount)
                (‘1’ : ValuationTerm)
                (shortBinaryNumeralTerm coordinates.firstFinish) ⋏
              (compactFixedWidthEntryAtValuationFormula
                  (shortBinaryNumeralTerm coordinates.suffixBoundary)
                  (shortBinaryNumeralTerm tokenCount)
                  (shortBinaryNumeralTerm coordinates.valueCount)
                  (shortBinaryNumeralTerm finalStart) ⋏
                (compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm coordinates.suffixBoundary)
                    (shortBinaryNumeralTerm tokenCount)
                    (‘!!(shortBinaryNumeralTerm coordinates.valueCount) + 1’ :
                      ValuationTerm)
                    (shortBinaryNumeralTerm finalFinish) ⋏
                  (compactAdditiveNatListConsRowsClosedFormula tokenTable width
                      tokenCount coordinates.firstBoundary
                      coordinates.firstCount coordinates.inputBoundary
                      coordinates.inputCount coordinates.valueCount ⋏
                    (compactAdditiveStructuredListLayoutClosedFormula
                        tokenTable width tokenCount valueStart
                        coordinates.valueCount valueFinish
                        coordinates.valueBoundary ⋏
                      (compactNatSizeClosedFormula
                          coordinates.valueBoundarySize
                          coordinates.valueBoundary ⋏
                        “!!(shortBinaryNumeralTerm
                              coordinates.valueBoundarySize) ≤
                          (!!(shortBinaryNumeralTerm coordinates.valueCount) +
                              1) *
                            !!(shortBinaryNumeralTerm tokenCount)”))))))))))

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

theorem compactSequentFormulaEndpointDirectClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    compactSequentFormulaEndpointDirectClosedFormula tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates =
      compactSequentFormulaEndpointDirectExplicitFormula tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates := by
  unfold compactSequentFormulaEndpointDirectClosedFormula
    compactSequentFormulaEndpointDirectExplicitFormula
    compactSequentFormulaEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
    compactSequentFormulaTraceBoundedDirectClosedFormula
    compactFixedWidthEntryAtValuationFormula
    compactAdditiveStructuredListLayoutClosedFormula
    compactNatSizeClosedFormula
  rw [compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution]
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

#print axioms compactSequentFormulaEndpointDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax

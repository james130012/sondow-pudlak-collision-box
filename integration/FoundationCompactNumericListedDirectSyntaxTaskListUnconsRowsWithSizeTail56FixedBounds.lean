import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56TransparentFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-!
# Fixed innermost tail of syntax-task-list uncons

This closes the genuine `NatSize ∧ area` certificate using the final global
syntax coordinate.  It is the first compiled layer of the original
right-associated six-leaf certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56LeafFixedBounds

private abbrev unconsTail56ZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation

theorem unconsRowsWithSizeTail56Formula_code_length_le_tight
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
        (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
          (!!(shortBinaryNumeralTerm tailCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” :
          ValuationFormula))).length <=
      compactNatSizeFixedPayloadPolynomial bitBound +
        parserAreaFixedPayloadPolynomial bitBound +
        (binaryNatCode 4).length := by
  have hsizeCode :=
    unconsRowsNatSizeFormula_code_length_le_fixed tailBoundarySize tailBoundary
      bitBound hsize htailBoundarySize
  have hareaCode :=
    unconsRowsAreaFormula_code_length_le_fixed tokenCount tailBoundary
      tailCount tailBoundarySize numericBound bitBound hsize harea
      htokenCount htailCount htailBoundarySize hnumericSize
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem unconsRowsWithSizeTail56Formula_code_length_le_global
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
        (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
          (!!(shortBinaryNumeralTerm tailCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” :
          ValuationFormula))).length <=
      unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
        bitBound := by
  have htight :=
    unconsRowsWithSizeTail56Formula_code_length_le_tight tokenCount
      tailBoundary tailCount tailBoundarySize numericBound bitBound hsize
      harea htokenCount htailCount htailBoundarySize hnumericSize
  exact htight.trans (by
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega)

theorem unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_fixed
    (tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (unconsRowsWithSizeTail56Certificate tailBoundarySize tailBoundary
          tailCount tokenCount hsize harea) <=
      hybridConjunctionGeneralPayloadEnvelope
        (unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound
          bitBound)
        (compactNatSizeFixedPayloadPolynomial bitBound)
        (parserAreaFixedPayloadPolynomial bitBound) := by
  let sizeFormula := compactNatSizeClosedFormula tailBoundarySize tailBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tailBoundarySize) ≤
      (!!(shortBinaryNumeralTerm tailCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  have hsizeClosed : sizeFormula.freeVariables = ∅ :=
    natSizeClosedFormula_freeVariables_eq_empty tailBoundarySize tailBoundary
  have hareaClosed : areaFormula.freeVariables = ∅ := by
    simpa only [areaFormula] using
      parserAreaFormula_freeVariables_eq_empty tailBoundarySize tailCount
        tokenCount
  have hsizeCode :
      (binaryFormulaCode sizeFormula).length <=
        compactNatSizeFixedPayloadPolynomial bitBound := by
    simpa only [sizeFormula] using
      unconsRowsNatSizeFormula_code_length_le_fixed tailBoundarySize
        tailBoundary bitBound hsize htailBoundarySize
  have hareaCode :
      (binaryFormulaCode areaFormula).length <=
        parserAreaFixedPayloadPolynomial bitBound := by
    simpa only [areaFormula] using
      unconsRowsAreaFormula_code_length_le_fixed tokenCount tailBoundary
        tailCount tailBoundarySize numericBound bitBound hsize harea
        htokenCount htailCount htailBoundarySize hnumericSize
  let syntaxResource :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold unconsRowsWithSizeFormulaCodePolynomial
    omega
  have hsizeCodeGlobal :
      (binaryFormulaCode sizeFormula).length <= syntaxResource := by
    exact hsizeCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have hareaCodeGlobal :
      (binaryFormulaCode areaFormula).length <= syntaxResource := by
    exact hareaCode.trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have hpairCode :
      (binaryFormulaCode (sizeFormula ⋏ areaFormula)).length <=
        syntaxResource := by
    have htagBudget :
        8 <= 5 * (binaryNatCode 4).length + 1 := by decide
    exact (binaryFormulaCode_and_length_le sizeFormula areaFormula).trans (by
      dsimp only [syntaxResource]
      unfold unconsRowsWithSizeFormulaCodePolynomial
      omega)
  have htransparent :=
    unconsRowsWithSizeTail56Certificate_structuralPayloadBound_le_transparentFixed
      tokenCount tailBoundary tailCount tailBoundarySize numericBound bitBound
      hsize harea htokenCount htailCount htailBoundarySize hnumericSize
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      unconsTail56ZeroValuation sizeFormula areaFormula
      (compactNatSizeFixedPayloadPolynomial bitBound)
      (parserAreaFixedPayloadPolynomial bitBound) syntaxResource hpositive
      hsizeClosed hareaClosed hsizeCodeGlobal hareaCodeGlobal hpairCode
  exact htransparent.trans (by
    simpa only [sizeFormula, areaFormula, syntaxResource] using henvelope)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56FixedBounds

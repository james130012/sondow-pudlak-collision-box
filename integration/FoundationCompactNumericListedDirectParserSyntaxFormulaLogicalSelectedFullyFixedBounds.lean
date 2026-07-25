import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fully fixed logical selected branch of the syntax-formula parser

This module joins the checked tag alternative `{2, 3}` to the real
syntax-term continue certificate.  Formula code, closedness, component
resources, and conjunction assembly are all paid by the shared numeric and
bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaLogicalSelectedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private def logicalSelectedZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaLogicalSelectedCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxTermContinueClosedFormulaCodePolynomial numericBound bitBound + 9

def syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaLogicalSelectedCodePolynomial numericBound bitBound)
    (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
    (syntaxTermContinueFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    syntaxFormulaLogicalSelectedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
          (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 1 hcontinue)) <=
      syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 2 ⋎ nativeEqFormula witness.tag 3
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 1
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 2 3 htag
  let continueCertificate :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 1 hcontinue
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact
      nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
        witness.tag 2 3 bitBound htag htagSize (by omega) (by omega)
  have hcontinueResource :
      hybridFormulaStructuralPayloadBound continueCertificate <=
        syntaxTermContinueFullyFixedPayloadPolynomial numericBound bitBound := by
    dsimp only [continueCertificate]
    exact
      compactUnifiedParserSyntaxTermContinueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hcontinue hwidth htokenCount
        htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
        htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 2 3
  have hcontinueClosed : continueFormula.freeVariables = ∅ := by
    dsimp only [continueFormula]
    exact
      compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 2 3
      bitBound htagSize (by omega) (by omega)
  have hcontinueCode :
      (binaryFormulaCode continueFormula).length <=
        syntaxTermContinueClosedFormulaCodePolynomial numericBound bitBound := by
    dsimp only [continueFormula]
    exact
      compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_code_length_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hcontinue hwidth htokenCount
        htailCount hcurrentValue htokenTableSize hwidthSize htokenCountSize
        hcurrentSize hnextSize htailBoundarySize hnumericSize
  have hraw := binaryFormulaCode_and_length_le tagFormula continueFormula
  have htagCodeTotal :
      (binaryFormulaCode tagFormula).length <=
        syntaxFormulaLogicalSelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaLogicalSelectedCodePolynomial
    omega
  have hcontinueCodeTotal :
      (binaryFormulaCode continueFormula).length <=
        syntaxFormulaLogicalSelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaLogicalSelectedCodePolynomial
    omega
  have hconjunctionCode :
      (binaryFormulaCode (tagFormula ⋏ continueFormula)).length <=
        syntaxFormulaLogicalSelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaLogicalSelectedCodePolynomial
    omega
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      logicalSelectedZeroValuation tagFormula continueFormula
      (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
      (syntaxTermContinueFullyFixedPayloadPolynomial numericBound bitBound)
      (syntaxFormulaLogicalSelectedCodePolynomial numericBound bitBound)
      (by
        unfold syntaxFormulaLogicalSelectedCodePolynomial
        omega)
      htagClosed hcontinueClosed htagCodeTotal hcontinueCodeTotal
      hconjunctionCode
  have hparts :=
    transparentHybridConjunctionPayloadBound_le tagCertificate
      continueCertificate _ _ htagResource hcontinueResource
  unfold syntaxFormulaLogicalSelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, continueFormula, tagCertificate,
    continueCertificate, logicalSelectedZeroValuation] using
      hparts.trans hassembly

#print axioms
  syntaxFormulaLogicalSelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaLogicalSelectedFullyFixedBounds

import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fully fixed quantified selected branch of the syntax-formula parser

The checked tag alternative `{6, 7}` is joined to the genuine quantified
syntax-formula transition.  Formula code, closedness, component resources, and
conjunction assembly all use the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierSelectedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds

private def quantifierSelectedZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaQuantifierSelectedCodePolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound +
    9

def syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaQuantifierSelectedCodePolynomial tokenCount numericBound
      bitBound)
    (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
    (syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

theorem
    syntaxFormulaQuantifierSelectedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (binderArity numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
          (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity hquantifier)) <=
      syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 6 ⋎ nativeEqFormula witness.tag 7
  let quantifierFormula :=
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 6 7 htag
  let quantifierCertificate :=
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hquantifier
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact
      nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
        witness.tag 6 7 bitBound htag htagSize (by omega) (by omega)
  have hquantifierResource :
      hybridFormulaStructuralPayloadBound quantifierCertificate <=
        syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount
          numericBound bitBound := by
    dsimp only [quantifierCertificate]
    exact
      compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity numericBound bitBound hquantifier hwidth
        htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderSize hnumericSize
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 6 7
  have hquantifierClosed : quantifierFormula.freeVariables = ∅ := by
    dsimp only [quantifierFormula]
    exact
      compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 6 7 bitBound
      htagSize (by omega) (by omega)
  have hquantifierCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      quantifierCertificate
  have hquantifierCode :
      (binaryFormulaCode quantifierFormula).length <=
        syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount
          numericBound bitBound := by
    simpa only [quantifierCertificate, quantifierFormula] using
      hquantifierCodeRaw.trans hquantifierResource
  have hraw := binaryFormulaCode_and_length_le tagFormula quantifierFormula
  have htagCodeTotal :
      (binaryFormulaCode tagFormula).length <=
        syntaxFormulaQuantifierSelectedCodePolynomial tokenCount numericBound
          bitBound := by
    unfold syntaxFormulaQuantifierSelectedCodePolynomial
    omega
  have hquantifierCodeTotal :
      (binaryFormulaCode quantifierFormula).length <=
        syntaxFormulaQuantifierSelectedCodePolynomial tokenCount numericBound
          bitBound := by
    unfold syntaxFormulaQuantifierSelectedCodePolynomial
    omega
  have hconjunctionCode :
      (binaryFormulaCode
        (tagFormula ⋏ quantifierFormula)).length <=
          syntaxFormulaQuantifierSelectedCodePolynomial tokenCount numericBound
            bitBound := by
    unfold syntaxFormulaQuantifierSelectedCodePolynomial
    omega
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      quantifierSelectedZeroValuation tagFormula quantifierFormula
      (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
      (syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      (syntaxFormulaQuantifierSelectedCodePolynomial tokenCount numericBound
        bitBound)
      (by
        unfold syntaxFormulaQuantifierSelectedCodePolynomial
        omega)
      htagClosed hquantifierClosed htagCodeTotal hquantifierCodeTotal
      hconjunctionCode
  have hparts :=
    transparentHybridConjunctionPayloadBound_le tagCertificate
      quantifierCertificate _ _ htagResource hquantifierResource
  unfold syntaxFormulaQuantifierSelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, quantifierFormula, tagCertificate,
    quantifierCertificate, quantifierSelectedZeroValuation] using
      hparts.trans hassembly

#print axioms
  syntaxFormulaQuantifierSelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierSelectedFullyFixedBounds

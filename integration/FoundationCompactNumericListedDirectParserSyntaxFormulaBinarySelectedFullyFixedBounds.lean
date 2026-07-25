import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fully fixed binary selected branch of the syntax-formula parser

The checked tag alternative `{4, 5}` is joined to the genuine binary
syntax-formula transition.  Formula code, closedness, component resources, and
conjunction assembly all use the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaBinarySelectedFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds

private def binarySelectedZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaBinarySelectedCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  parserFormulaAtomicFormulaCodePolynomial bitBound +
    syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound bitBound +
    9

def syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaBinarySelectedCodePolynomial numericBound bitBound)
    (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
    (syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound bitBound)

theorem
    syntaxFormulaBinarySelectedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (binderArity numericBound bitBound : Nat)
    (htag : NativeEqEitherCheckedData witness.tag 4 5)
    (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable
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
          (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
          (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity hbinary)) <=
      syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let tagFormula :=
    nativeEqFormula witness.tag 4 ⋎ nativeEqFormula witness.tag 5
  let binaryFormula :=
    compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity
  let tagCertificate :=
    nativeEqEitherCertificateFromData witness.tag 4 5 htag
  let binaryCertificate :=
    compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hbinary
  have htagResource :
      hybridFormulaStructuralPayloadBound tagCertificate <=
        parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
    dsimp only [tagCertificate]
    exact
      nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
        witness.tag 4 5 bitBound htag htagSize (by omega) (by omega)
  have hbinaryResource :
      hybridFormulaStructuralPayloadBound binaryCertificate <=
        syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound
          bitBound := by
    dsimp only [binaryCertificate]
    exact
      compactUnifiedParserSyntaxFormulaBinaryModularCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity numericBound bitBound hbinary hwidth
        htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderSize hnumericSize
  have htagClosed : tagFormula.freeVariables = ∅ := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_freeVariables_eq_empty_fixed witness.tag 4 5
  have hbinaryClosed : binaryFormula.freeVariables = ∅ := by
    dsimp only [binaryFormula]
    exact
      compactUnifiedParserSyntaxFormulaBinaryClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity
  have htagCode :
      (binaryFormulaCode tagFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [tagFormula]
    exact nativeEqEitherFormula_code_length_le_fixed witness.tag 4 5 bitBound
      htagSize (by omega) (by omega)
  have hbinaryCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      binaryCertificate
  have hbinaryCode :
      (binaryFormulaCode binaryFormula).length <=
        syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound
          bitBound := by
    simpa only [binaryCertificate, binaryFormula] using
      hbinaryCodeRaw.trans hbinaryResource
  have hraw := binaryFormulaCode_and_length_le tagFormula binaryFormula
  have htagCodeTotal :
      (binaryFormulaCode tagFormula).length <=
        syntaxFormulaBinarySelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaBinarySelectedCodePolynomial
    omega
  have hbinaryCodeTotal :
      (binaryFormulaCode binaryFormula).length <=
        syntaxFormulaBinarySelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaBinarySelectedCodePolynomial
    omega
  have hconjunctionCode :
      (binaryFormulaCode
        (tagFormula ⋏ binaryFormula)).length <=
          syntaxFormulaBinarySelectedCodePolynomial numericBound bitBound := by
    unfold syntaxFormulaBinarySelectedCodePolynomial
    omega
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      binarySelectedZeroValuation tagFormula binaryFormula
      (parserFormulaEqEitherFixedPayloadPolynomial bitBound)
      (syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound
        bitBound)
      (syntaxFormulaBinarySelectedCodePolynomial numericBound bitBound)
      (by
        unfold syntaxFormulaBinarySelectedCodePolynomial
        omega)
      htagClosed hbinaryClosed htagCodeTotal hbinaryCodeTotal
      hconjunctionCode
  have hparts :=
    transparentHybridConjunctionPayloadBound_le tagCertificate
      binaryCertificate _ _ htagResource hbinaryResource
  unfold syntaxFormulaBinarySelectedFullyFixedPayloadPolynomial
  simpa only [tagFormula, binaryFormula, tagCertificate,
    binaryCertificate, binarySelectedZeroValuation] using
      hparts.trans hassembly

#print axioms
  syntaxFormulaBinarySelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaBinarySelectedFullyFixedBounds

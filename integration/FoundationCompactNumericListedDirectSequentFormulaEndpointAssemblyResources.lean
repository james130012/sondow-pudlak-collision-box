import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointWitnessTraceLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointConsLeaf
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointValueLayoutLeaf
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointValueSizeLeaf
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointValueAreaLeaf

/-! # Exact formulas and proof-free resources for endpoint assembly -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 90000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaTraceBoundedDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

def endpointAssemblyFormula01
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
    coordinates.inputBoundarySize

def endpointAssemblyFormula02
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    coordinates.firstStart coordinates.firstCount coordinates.firstFinish
    coordinates.firstBoundary coordinates.firstBoundarySize

def endpointAssemblyFormula03
    (tokenTable width tokenCount finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    finalStart coordinates.finalCount finalFinish coordinates.finalBoundary
    coordinates.finalBoundarySize

def endpointAssemblyFormula04
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactSequentFormulaTraceBoundedDirectClosedFormula tokenTable width
    tokenCount coordinates.suffixBoundary coordinates.suffixCount
    coordinates.valueBoundary coordinates.valueCount coordinates.traceTableWidth
    coordinates.traceValueBound

def endpointAssemblyFormula05
    (tokenCount : Nat) (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm coordinates.suffixBoundary)
    (shortBinaryNumeralTerm tokenCount) (‘0’ : ValuationTerm)
    (shortBinaryNumeralTerm coordinates.firstStart)

def endpointAssemblyFormula06
    (tokenCount : Nat) (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm coordinates.suffixBoundary)
    (shortBinaryNumeralTerm tokenCount) (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm coordinates.firstFinish)

def endpointAssemblyFormula07
    (tokenCount finalStart : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm coordinates.suffixBoundary)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm coordinates.valueCount)
    (shortBinaryNumeralTerm finalStart)

def endpointAssemblyFormula08
    (tokenCount finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm coordinates.suffixBoundary)
    (shortBinaryNumeralTerm tokenCount)
    (endpointSuccessorIndexTerm coordinates.valueCount)
    (shortBinaryNumeralTerm finalFinish)

def endpointAssemblyFormula09
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
    coordinates.firstBoundary coordinates.firstCount coordinates.inputBoundary
    coordinates.inputCount coordinates.valueCount

def endpointAssemblyFormula10
    (tokenTable width tokenCount valueStart valueFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
    valueStart coordinates.valueCount valueFinish coordinates.valueBoundary

def endpointAssemblyFormula11
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  compactNatSizeClosedFormula coordinates.valueBoundarySize
    coordinates.valueBoundary

def endpointAssemblyFormula12
    (tokenCount : Nat) (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm coordinates.valueBoundarySize) ≤
    (!!(shortBinaryNumeralTerm coordinates.valueCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)”

def endpointAssemblyConjunctionResource
    (left right : ValuationFormula) (leftResource rightResource : Nat) : Nat :=
  leftResource + rightResource +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ left right

def endpointAssemblyTail12Formula
    (tokenCount : Nat) (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula12 tokenCount coordinates

def endpointAssemblyTail12Resource (bitBound : Nat) : Nat :=
  parserAreaFixedPayloadPolynomial bitBound

def endpointAssemblyTail11Formula
    (tokenCount : Nat) (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula11 coordinates ⋏
    endpointAssemblyTail12Formula tokenCount coordinates

def endpointAssemblyTail11Resource
    (tokenCount bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource (endpointAssemblyFormula11 coordinates)
    (endpointAssemblyTail12Formula tokenCount coordinates)
    (compactNatSizeFixedPayloadPolynomial bitBound)
    (endpointAssemblyTail12Resource bitBound)

def endpointAssemblyTail10Formula
    (tokenTable width tokenCount valueStart valueFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula10 tokenTable width tokenCount valueStart valueFinish
      coordinates ⋏
    endpointAssemblyTail11Formula tokenCount coordinates

def endpointAssemblyTail10Resource
    (tokenTable width tokenCount valueStart valueFinish numericBound bitBound :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula10 tokenTable width tokenCount valueStart valueFinish
      coordinates)
    (endpointAssemblyTail11Formula tokenCount coordinates)
    (compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (endpointAssemblyTail11Resource tokenCount bitBound coordinates)

def endpointAssemblyTail09Formula
    (tokenTable width tokenCount valueStart valueFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula09 tokenTable width tokenCount coordinates ⋏
    endpointAssemblyTail10Formula tokenTable width tokenCount valueStart
      valueFinish coordinates

def endpointAssemblyTail09Resource
    (tokenTable width tokenCount valueStart valueFinish numericBound bitBound :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula09 tokenTable width tokenCount coordinates)
    (endpointAssemblyTail10Formula tokenTable width tokenCount valueStart
      valueFinish coordinates)
    (natListConsRowsClosedFullyFixedPayloadPolynomial numericBound bitBound)
    (endpointAssemblyTail10Resource tokenTable width tokenCount valueStart
      valueFinish numericBound bitBound coordinates)

def endpointAssemblyTail08Formula
    (tokenTable width tokenCount valueStart valueFinish finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula08 tokenCount finalFinish coordinates ⋏
    endpointAssemblyTail09Formula tokenTable width tokenCount valueStart
      valueFinish coordinates

def endpointAssemblyTail08Resource
    (tokenTable width tokenCount valueStart valueFinish finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula08 tokenCount finalFinish coordinates)
    (endpointAssemblyTail09Formula tokenTable width tokenCount valueStart
      valueFinish coordinates)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount finalFinish
      (endpointSuccessorIndexTerm coordinates.valueCount))
    (endpointAssemblyTail09Resource tokenTable width tokenCount valueStart
      valueFinish numericBound bitBound coordinates)

def endpointAssemblyTail07Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula07 tokenCount finalStart coordinates ⋏
    endpointAssemblyTail08Formula tokenTable width tokenCount valueStart
      valueFinish finalFinish coordinates

def endpointAssemblyTail07Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula07 tokenCount finalStart coordinates)
    (endpointAssemblyTail08Formula tokenTable width tokenCount valueStart
      valueFinish finalFinish coordinates)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount finalStart
      (shortBinaryNumeralTerm coordinates.valueCount))
    (endpointAssemblyTail08Resource tokenTable width tokenCount valueStart
      valueFinish finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail06Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula06 tokenCount coordinates ⋏
    endpointAssemblyTail07Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail06Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula06 tokenCount coordinates)
    (endpointAssemblyTail07Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount coordinates.firstFinish
      (‘1’ : ValuationTerm))
    (endpointAssemblyTail07Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail05Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula05 tokenCount coordinates ⋏
    endpointAssemblyTail06Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail05Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula05 tokenCount coordinates)
    (endpointAssemblyTail06Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount coordinates.firstStart
      (‘0’ : ValuationTerm))
    (endpointAssemblyTail06Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail04Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula04 tokenTable width tokenCount coordinates ⋏
    endpointAssemblyTail05Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail04Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula04 tokenTable width tokenCount coordinates)
    (endpointAssemblyTail05Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (compactSequentFormulaTraceBoundedDirectPayloadEnvelope tokenTable width
      tokenCount coordinates.suffixBoundary coordinates.suffixCount
      coordinates.valueBoundary coordinates.valueCount
      coordinates.traceTableWidth coordinates.traceValueBound)
    (endpointAssemblyTail05Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail03Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula03 tokenTable width tokenCount finalStart finalFinish
      coordinates ⋏
    endpointAssemblyTail04Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail03Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula03 tokenTable width tokenCount finalStart finalFinish
      coordinates)
    (endpointAssemblyTail04Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
    (endpointAssemblyTail04Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail02Formula
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish :
      Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula02 tokenTable width tokenCount coordinates ⋏
    endpointAssemblyTail03Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail02Resource
    (tokenTable width tokenCount valueStart valueFinish finalStart finalFinish
      numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula02 tokenTable width tokenCount coordinates)
    (endpointAssemblyTail03Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
    (endpointAssemblyTail03Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

def endpointAssemblyTail01Formula
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    ValuationFormula :=
  endpointAssemblyFormula01 tokenTable width tokenCount inputStart inputFinish
      coordinates ⋏
    endpointAssemblyTail02Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates

def endpointAssemblyTail01Resource
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish numericBound bitBound : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Nat :=
  endpointAssemblyConjunctionResource
    (endpointAssemblyFormula01 tokenTable width tokenCount inputStart inputFinish
      coordinates)
    (endpointAssemblyTail02Formula tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish coordinates)
    (compactNatListWitnessRowsFullyFixedPayloadPolynomial numericBound bitBound)
    (endpointAssemblyTail02Resource tokenTable width tokenCount valueStart
      valueFinish finalStart finalFinish numericBound bitBound coordinates)

theorem endpointAssemblyTail01Formula_eq_explicit
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    endpointAssemblyTail01Formula tokenTable width tokenCount inputStart
        inputFinish valueStart valueFinish finalStart finalFinish coordinates =
      compactSequentFormulaEndpointDirectExplicitFormula tokenTable width
        tokenCount inputStart inputFinish valueStart valueFinish finalStart
        finalFinish coordinates := by
  rfl

#print axioms endpointAssemblyTail01Formula_eq_explicit

end FoundationCompactNumericListedDirectSequentFormulaEndpointAssemblyResources

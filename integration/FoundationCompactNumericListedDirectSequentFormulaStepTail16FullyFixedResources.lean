import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedRowParserLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedOfGraph
import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectTailCompiler
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Fixed resources for closed tail 16--21 of one sequent-formula step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound

def compactSequentFormulaStepTail16CurrentFormula
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    row.current.start row.current.count row.current.finish row.current.boundary
    row.current.boundarySize

def compactSequentFormulaStepTail16NextFormula
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    row.next.start row.next.count row.next.finish row.next.boundary
    row.next.boundarySize

def compactSequentFormulaStepTail16ValueFormula
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
    row.value.start row.value.count row.value.finish row.value.boundary
    row.value.boundarySize

def compactSequentFormulaStepTail16ParserFormula
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
    row.parserStateBoundary row.current.boundary row.current.count
    row.next.boundary row.next.count row.parserTableWidth row.parserValueBound

def compactSequentFormulaStepTail20Formula
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count row.next.start
      row.next.finish row.next.count row.current.start row.current.finish
      row.current.count) ⋏
    (“!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula)

def compactSequentFormulaStepTail19Formula
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount row ⋏
    compactSequentFormulaStepTail20Formula tokenTable width tokenCount suffixCount
      valueCount row

def compactSequentFormulaStepTail18Formula
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount row ⋏
    compactSequentFormulaStepTail19Formula tokenTable width tokenCount suffixCount
      valueCount row

def compactSequentFormulaStepTail17Formula
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount row ⋏
    compactSequentFormulaStepTail18Formula tokenTable width tokenCount suffixCount
      valueCount row

def compactSequentFormulaStepTail16Formula
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount row ⋏
    compactSequentFormulaStepTail17Formula tokenTable width tokenCount suffixCount
      valueCount row

theorem compactSequentFormulaStepTail16Formula_eq_direct
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepTail16Formula tokenTable width tokenCount suffixCount
        valueCount row =
      compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount row := by
  rfl

def compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  16 *
    (3 * compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
          tokenCount +
      compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable width
        tokenCount row.parserStateBoundary
        (compactParserSyntaxExactFuel row.current.count + 1)
        row.current.boundary row.current.count row.next.boundary row.next.count
        row.parserTableWidth row.parserValueBound +
      compactSequentFormulaStepTail20FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row +
      (binaryNatCode 4).length + 1)

def compactSequentFormulaStepTail19FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable width
      tokenCount row.parserStateBoundary
      (compactParserSyntaxExactFuel row.current.count + 1)
      row.current.boundary row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound +
    compactSequentFormulaStepTail20FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail18FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail19FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail17FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail18FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail16FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail17FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    (binaryNatCode 4).length

structure CompactSequentFormulaStepFixedResult
    (formula : ValuationFormula) (payloadResource codeResource : Nat) where
  bound : ClosedDirectFormulaBound formula payloadResource
  codeLength_le : (binaryFormulaCode formula).length <= codeResource

def compactSequentFormulaStepTail19FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable width
      tokenCount row.parserStateBoundary
      (compactParserSyntaxExactFuel row.current.count + 1)
      row.current.boundary row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound +
    compactSequentFormulaStepTail20FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount row)

def compactSequentFormulaStepTail18FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail19FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount row)

def compactSequentFormulaStepTail17FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail18FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount row)

def compactSequentFormulaStepTail16FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail17FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16FullyFixedSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount row)

noncomputable def compactSequentFormulaStepFixedClosedConjunction
    {left right : ValuationFormula} {leftResource rightResource : Nat}
    (leftBound : ClosedDirectFormulaBound left leftResource)
    (rightBound : ClosedDirectFormulaBound right rightResource)
    (syntaxResource : Nat)
    (hleft : (binaryFormulaCode left).length <= syntaxResource)
    (hright : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunction :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource) :
    ClosedDirectFormulaBound (left ⋏ right)
      (leftResource + rightResource +
        smallContextAssemblyEnvelope syntaxResource) := by
  let proof := CertifiedPAContextProof.conjunction leftBound.proof
    rightBound.proof
  have hcost := conjunctionFullAssemblyCost_le_small ∅ left right
    syntaxResource (by simp) (by
      intro formula hmem
      simp at hmem) hleft hright hconjunction
  have hassembly := CertifiedPAContextProof.conjunction_payloadLength_le
    leftBound.proof rightBound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  exact hassembly.trans (by
    have hleftPayload := leftBound.payloadLength_le
    have hrightPayload := rightBound.payloadLength_le
    omega)

end FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound

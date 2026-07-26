import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformRowParserLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail20UniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedResources

/-! # Row-independent resource for tail 16--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepParserUniformResourceBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformRowParserLeaves
open FoundationCompactNumericListedDirectSequentFormulaStepTail20UniformBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound

def compactSequentFormulaStepTail16UniformParserResource
    (tokenTable width tokenCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepParserUniformPayloadPolynomial tokenCount valueBound
    (compactSequentFormulaStepParserUniformNumericBound tokenTable width
      tokenCount valueBound)
    (compactSequentFormulaStepParserUniformBitBound tokenTable width tokenCount
      valueBound)

def compactSequentFormulaStepTail16UniformSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  16 *
    (3 * compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
        tokenCount +
      compactSequentFormulaStepTail16UniformParserResource tokenTable width
        tokenCount valueBound +
      compactSequentFormulaStepTail20UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount +
      (binaryNatCode 4).length + 1)

def compactSequentFormulaStepTail20UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat) : Nat :=
  compactSequentFormulaStepTail20UniformPayloadPolynomial tokenTable width
    tokenCount suffixCount valueCount

def compactSequentFormulaStepTail19UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepTail16UniformParserResource tokenTable width
      tokenCount valueBound +
    compactSequentFormulaStepTail20UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail18UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail19UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail17UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail18UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail16UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail17UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail19UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepTail16UniformParserResource tokenTable width
      tokenCount valueBound +
    compactSequentFormulaStepTail20UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16UniformSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)

def compactSequentFormulaStepTail18UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail19UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16UniformSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)

def compactSequentFormulaStepTail17UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail18UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16UniformSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)

def compactSequentFormulaStepTail16UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount +
    compactSequentFormulaStepTail17UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail16UniformSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)

noncomputable def compactSequentFormulaStepTail16UniformResultOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CompactSequentFormulaStepFixedResult
      (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
        suffixCount valueCount data.row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)
      (compactSequentFormulaStepTail16UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
  let row := data.row
  let rowParser :=
    compactSequentFormulaStepTail16UniformRowParserLeavesOfData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound data
  let tail20 := compactSequentFormulaStepTail20UniformBoundOfGraph tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    rowIndex row data.graph
  let rowResource :=
    compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount
  let parserResource := compactSequentFormulaStepTail16UniformParserResource
    tokenTable width tokenCount valueBound
  let tail20Resource :=
    compactSequentFormulaStepTail20UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount
  let syntaxResource :=
    compactSequentFormulaStepTail16UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound
  let currentFormula :=
    compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount row
  let nextFormula :=
    compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount row
  let valueFormula :=
    compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount row
  let parserFormula :=
    compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount row
  let tail20Formula := compactSequentFormulaStepTail20Formula tokenTable width
    tokenCount suffixCount valueCount row
  let tail19Formula := compactSequentFormulaStepTail19Formula tokenTable width
    tokenCount suffixCount valueCount row
  let tail18Formula := compactSequentFormulaStepTail18Formula tokenTable width
    tokenCount suffixCount valueCount row
  let tail17Formula := compactSequentFormulaStepTail17Formula tokenTable width
    tokenCount suffixCount valueCount row
  have hcurrentCode : (binaryFormulaCode currentFormula).length <=
      rowResource := by
    simpa only [currentFormula,
      compactSequentFormulaStepTail16CurrentFormula] using
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        rowParser.current.proof).trans rowParser.current.payloadLength_le
  have hnextCode : (binaryFormulaCode nextFormula).length <= rowResource := by
    simpa only [nextFormula, compactSequentFormulaStepTail16NextFormula] using
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        rowParser.next.proof).trans rowParser.next.payloadLength_le
  have hvalueCode : (binaryFormulaCode valueFormula).length <= rowResource := by
    simpa only [valueFormula, compactSequentFormulaStepTail16ValueFormula] using
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        rowParser.value.proof).trans rowParser.value.payloadLength_le
  have hparserCode : (binaryFormulaCode parserFormula).length <=
      parserResource := by
    simpa only [parserFormula, compactSequentFormulaStepTail16ParserFormula,
      parserResource,
      compactSequentFormulaStepTail16UniformParserResource] using
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        rowParser.parser.proof).trans rowParser.parser.payloadLength_le
  have htail20Code : (binaryFormulaCode tail20Formula).length <=
      tail20Resource := by
    simpa only [tail20Formula, compactSequentFormulaStepTail20Formula] using
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        tail20.proof).trans tail20.payloadLength_le
  have hparserSyntax : (binaryFormulaCode parserFormula).length <=
      syntaxResource := hparserCode.trans (by
    dsimp only [syntaxResource, parserResource, rowResource, tail20Resource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
    omega)
  have htail20Syntax : (binaryFormulaCode tail20Formula).length <=
      syntaxResource := htail20Code.trans (by
    dsimp only [syntaxResource, parserResource, rowResource, tail20Resource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
    omega)
  have htail19Code : (binaryFormulaCode tail19Formula).length <=
      compactSequentFormulaStepTail19UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound := by
    have hraw := binaryFormulaCode_and_length_le_local parserFormula
      tail20Formula
    change (binaryFormulaCode (parserFormula ⋏ tail20Formula)).length <= _
    exact hraw.trans (by
      unfold compactSequentFormulaStepTail19UniformCodePolynomial
        compactSequentFormulaStepTail20UniformCodePolynomial
      omega)
  have htail19Syntax : (binaryFormulaCode tail19Formula).length <=
      syntaxResource := htail19Code.trans (by
    dsimp only [syntaxResource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
      compactSequentFormulaStepTail19UniformCodePolynomial
      compactSequentFormulaStepTail20UniformCodePolynomial
    omega)
  let tail19 : ClosedDirectFormulaBound tail19Formula
      (compactSequentFormulaStepTail19UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
    change ClosedDirectFormulaBound (parserFormula ⋏ tail20Formula)
      (parserResource + tail20Resource +
        smallContextAssemblyEnvelope syntaxResource)
    exact compactSequentFormulaStepFixedClosedConjunction rowParser.parser
      tail20 syntaxResource hparserSyntax htail20Syntax htail19Syntax
  have hvalueSyntax : (binaryFormulaCode valueFormula).length <=
      syntaxResource := hvalueCode.trans (by
    dsimp only [syntaxResource, rowResource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
    omega)
  have htail18Code : (binaryFormulaCode tail18Formula).length <=
      compactSequentFormulaStepTail18UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound := by
    have hraw := binaryFormulaCode_and_length_le_local valueFormula tail19Formula
    change (binaryFormulaCode (valueFormula ⋏ tail19Formula)).length <= _
    exact hraw.trans (by
      unfold compactSequentFormulaStepTail18UniformCodePolynomial
      omega)
  have htail18Syntax : (binaryFormulaCode tail18Formula).length <=
      syntaxResource := htail18Code.trans (by
    dsimp only [syntaxResource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
      compactSequentFormulaStepTail18UniformCodePolynomial
      compactSequentFormulaStepTail19UniformCodePolynomial
      compactSequentFormulaStepTail20UniformCodePolynomial
    omega)
  let tail18 : ClosedDirectFormulaBound tail18Formula
      (compactSequentFormulaStepTail18UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
    change ClosedDirectFormulaBound (valueFormula ⋏ tail19Formula)
      (rowResource +
        compactSequentFormulaStepTail19UniformPayloadPolynomial tokenTable width
          tokenCount suffixCount valueCount valueBound +
        smallContextAssemblyEnvelope syntaxResource)
    exact compactSequentFormulaStepFixedClosedConjunction rowParser.value
      tail19 syntaxResource hvalueSyntax htail19Syntax htail18Syntax
  have hnextSyntax : (binaryFormulaCode nextFormula).length <= syntaxResource :=
    hnextCode.trans (by
      dsimp only [syntaxResource, rowResource]
      unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
      omega)
  have htail17Code : (binaryFormulaCode tail17Formula).length <=
      compactSequentFormulaStepTail17UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound := by
    have hraw := binaryFormulaCode_and_length_le_local nextFormula tail18Formula
    change (binaryFormulaCode (nextFormula ⋏ tail18Formula)).length <= _
    exact hraw.trans (by
      unfold compactSequentFormulaStepTail17UniformCodePolynomial
      omega)
  have htail17Syntax : (binaryFormulaCode tail17Formula).length <=
      syntaxResource := htail17Code.trans (by
    dsimp only [syntaxResource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
      compactSequentFormulaStepTail17UniformCodePolynomial
      compactSequentFormulaStepTail18UniformCodePolynomial
      compactSequentFormulaStepTail19UniformCodePolynomial
      compactSequentFormulaStepTail20UniformCodePolynomial
    omega)
  let tail17 : ClosedDirectFormulaBound tail17Formula
      (compactSequentFormulaStepTail17UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
    change ClosedDirectFormulaBound (nextFormula ⋏ tail18Formula)
      (rowResource +
        compactSequentFormulaStepTail18UniformPayloadPolynomial tokenTable width
          tokenCount suffixCount valueCount valueBound +
        smallContextAssemblyEnvelope syntaxResource)
    exact compactSequentFormulaStepFixedClosedConjunction rowParser.next
      tail18 syntaxResource hnextSyntax htail18Syntax htail17Syntax
  have hcurrentSyntax : (binaryFormulaCode currentFormula).length <=
      syntaxResource := hcurrentCode.trans (by
    dsimp only [syntaxResource, rowResource]
    unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
    omega)
  have htail16Code :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <=
      compactSequentFormulaStepTail16UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound := by
    have hraw := binaryFormulaCode_and_length_le_local currentFormula
      tail17Formula
    change (binaryFormulaCode (currentFormula ⋏ tail17Formula)).length <= _
    exact hraw.trans (by
      unfold compactSequentFormulaStepTail16UniformCodePolynomial
      omega)
  have htail16Syntax :
      (binaryFormulaCode
        (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
          suffixCount valueCount row)).length <= syntaxResource :=
    htail16Code.trans (by
      dsimp only [syntaxResource]
      unfold compactSequentFormulaStepTail16UniformSyntaxPolynomial
        compactSequentFormulaStepTail16UniformCodePolynomial
        compactSequentFormulaStepTail17UniformCodePolynomial
        compactSequentFormulaStepTail18UniformCodePolynomial
        compactSequentFormulaStepTail19UniformCodePolynomial
        compactSequentFormulaStepTail20UniformCodePolynomial
      omega)
  let tail16 : ClosedDirectFormulaBound
      (compactSequentFormulaStepTail16Formula tokenTable width tokenCount
        suffixCount valueCount row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
    change ClosedDirectFormulaBound (currentFormula ⋏ tail17Formula)
      (rowResource +
        compactSequentFormulaStepTail17UniformPayloadPolynomial tokenTable width
          tokenCount suffixCount valueCount valueBound +
        smallContextAssemblyEnvelope syntaxResource)
    exact compactSequentFormulaStepFixedClosedConjunction rowParser.current
      tail17 syntaxResource hcurrentSyntax htail17Syntax htail16Syntax
  exact { bound := tail16, codeLength_le := htail16Code }

noncomputable def compactSequentFormulaStepTail16UniformEmptyBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    ClosedDirectFormulaBound
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
  rw [← compactSequentFormulaStepTail16Formula_eq_direct]
  exact (compactSequentFormulaStepTail16UniformResultOfData tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    valueBound data).bound

#print axioms compactSequentFormulaStepTail16UniformEmptyBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformBound

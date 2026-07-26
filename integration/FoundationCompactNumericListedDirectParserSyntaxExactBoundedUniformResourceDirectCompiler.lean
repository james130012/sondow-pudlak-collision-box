import integration.FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelUniformResourceBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectGraph
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-!
# Exact bounded parser compiler with one public resource bound

The original exact parser formula is unchanged.  Actual endpoint and row
witnesses remain in the proof, but the complete payload bound depends only on
the public token count and external numeric, bit, and witness-value bounds.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxExactBoundedUniformResourceDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelUniformResourceBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectGraph
open FoundationCompactNumericListedDirectAdditiveCodecGraph

def compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound +
    compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound + 16

def compactParserSyntaxExactBoundedUniformPayloadPolynomial
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  let count :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let initialFinal :=
    compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound
  let adjacent :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound
  count + initialFinal + adjacent +
    2 * smallContextAssemblyEnvelope
      (compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
        tokenCount uniformValueBound numericBound bitBound)

noncomputable def
    compactParserSyntaxExactBoundedUniformClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth formulaValueBound uniformValueBound
      numericBound bitBound : Nat)
    (htableWidth : tableWidth <= uniformValueBound)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      formulaValueBound)
    (htokenTable : tokenTable <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateBoundary : stateBoundary <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hinputBoundary : inputBoundary <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedBoundary : expectedBoundary <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (htaskKind : taskKind <= numericBound)
    (htaskBinderArity : taskBinderArity <= numericBound)
    (htaskRepeatCount : taskRepeatCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (huniformValueSucc : uniformValueBound + 1 <= numericBound)
    (hnumericBit : numericBound <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth formulaValueBound)
      (compactParserSyntaxExactBoundedUniformPayloadPolynomial tokenCount
        uniformValueBound numericBound bitBound) := by
  have htrace : CompactParserSyntaxTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth formulaValueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactParserSyntaxExactFuel] using hgraph
  have hformulaValueNumeric : formulaValueBound <= numericBound :=
    hformulaValue.trans (by omega)
  have hformulaValueSucc : formulaValueBound + 1 <= numericBound := by
    omega
  have hwidthBit : width <= bitBound := hwidth.trans hnumericBit
  have hareaBit : (tokenCount + 1) * tokenCount <= bitBound :=
    hareaNumeric.trans hnumericBit
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (natSize_le_of_le htokenTable).trans hnumericBit
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound :=
    (natSize_le_of_le hstateBoundary).trans hnumericBit
  have hinputBoundarySize : Nat.size inputBoundary <= bitBound :=
    (natSize_le_of_le hinputBoundary).trans hnumericBit
  have hexpectedBoundarySize : Nat.size expectedBoundary <= bitBound :=
    (natSize_le_of_le hexpectedBoundary).trans hnumericBit
  have htaskKindSize : Nat.size taskKind <= bitBound :=
    (natSize_le_of_le htaskKind).trans hnumericBit
  have htaskBinderAritySize : Nat.size taskBinderArity <= bitBound :=
    (natSize_le_of_le htaskBinderArity).trans hnumericBit
  have htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound :=
    (natSize_le_of_le htaskRepeatCount).trans hnumericBit
  let countBound :=
    parserInitialFinalExactFuelCountClosedDirectBound stateCount inputCount
      htrace.1
  let initialFinalBound :=
    compactParserInitialFinalBoundedExactFuelUniformClosedDirectBoundOfBounded
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount formulaValueBound uniformValueBound numericBound bitBound
      hformulaValue htrace.2.1 hwidth htokenCount hstateCount hinputCount
      hexpectedCount hformulaValueSucc htokenTableSize hstateBoundarySize
      hinputBoundarySize hexpectedBoundarySize htaskKindSize
      htaskBinderAritySize htaskRepeatCountSize hnumericSize hbitPositive
  let adjacentProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      htrace.2.2 hfuel hformulaValueNumeric hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let initialFinalFormula :=
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      formulaValueBound
  let adjacentFormula :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound
  let countResource :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let initialFinalResource :=
    compactParserInitialFinalBoundedExactFuelUniformPayloadPolynomial tokenCount
      uniformValueBound numericBound bitBound
  let adjacentResource :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound
  let formulaResource :=
    compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial tokenCount
      uniformValueBound numericBound bitBound
  have hcount : countBound.proof.payloadLength <= countResource :=
    countBound.payloadLength_le.trans
      (compactParserInitialFinalExactFuelCountResource_le_fixed inputCount
        numericBound hinputCount)
  have hinitialFinal : initialFinalBound.proof.payloadLength <=
      initialFinalResource := initialFinalBound.payloadLength_le
  have hadjacent : adjacentProof.payloadLength <= adjacentResource :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound uniformValueBound numericBound bitBound htableWidth
      hformulaValue htrace.2.2 hinputCount hfuel hformulaValueNumeric hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive
  have hcountCode : (binaryFormulaCode countFormula).length <= countResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      countBound.proof).trans hcount
  have hinitialFinalCode :
      (binaryFormulaCode initialFinalFormula).length <= initialFinalResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      initialFinalBound.proof).trans hinitialFinal
  have hadjacentCode :
      (binaryFormulaCode adjacentFormula).length <= adjacentResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      adjacentProof).trans hadjacent
  have hinnerCodeTight :
      (binaryFormulaCode (initialFinalFormula ⋏ adjacentFormula)).length <=
        initialFinalResource + adjacentResource + 8 := by
    have hraw := binaryFormulaCode_and_length_le initialFinalFormula
      adjacentFormula
    omega
  have hinnerCode :
      (binaryFormulaCode (initialFinalFormula ⋏ adjacentFormula)).length <=
        formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    omega
  have houterCode :
      (binaryFormulaCode
        (countFormula ⋏ (initialFinalFormula ⋏ adjacentFormula))).length <=
        formulaResource := by
    have hraw := binaryFormulaCode_and_length_le countFormula
      (initialFinalFormula ⋏ adjacentFormula)
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    omega
  have hformulaContext : FormulaCodeBound ∅ formulaResource := by
    intro formula hmem
    simp at hmem
  have hcountFormulaFixed :
      (binaryFormulaCode countFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    omega
  have hinitialFinalFormulaFixed :
      (binaryFormulaCode initialFinalFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    omega
  have hadjacentFormulaFixed :
      (binaryFormulaCode adjacentFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedUniformAssemblyFormulaPolynomial
    omega
  have hinnerAssembly := conjunctionFullAssemblyCost_le_small ∅
    initialFinalFormula adjacentFormula formulaResource (by simp)
    hformulaContext hinitialFinalFormulaFixed hadjacentFormulaFixed hinnerCode
  have houterAssembly := conjunctionFullAssemblyCost_le_small ∅ countFormula
    (initialFinalFormula ⋏ adjacentFormula) formulaResource (by simp)
    hformulaContext hcountFormulaFixed hinnerCode houterCode
  let innerProof := CertifiedPAContextProof.conjunction
    initialFinalBound.proof adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction countBound.proof
    innerProof
  let traceProof := CertifiedPAContextProof.cast
    (compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth formulaValueBound).symm outerProof
  let proof := CertifiedPAContextProof.cast
    (compactParserSyntaxExactBoundedDirectClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth formulaValueBound).symm traceProof
  refine { proof := proof, payloadLength_le := ?_ }
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    initialFinalBound.proof adjacentProof
  have hinnerBound : innerProof.payloadLength <= initialFinalResource +
      adjacentResource + smallContextAssemblyEnvelope formulaResource := by
    calc
      innerProof.payloadLength <= initialFinalBound.proof.payloadLength +
          adjacentProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
              initialFinalFormula adjacentFormula := by
        simpa only [innerProof, initialFinalFormula, adjacentFormula] using
          hinner
      _ <= initialFinalResource + adjacentResource +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            initialFinalFormula adjacentFormula :=
        Nat.add_le_add_right (Nat.add_le_add hinitialFinal hadjacent) _
      _ <= initialFinalResource + adjacentResource +
          smallContextAssemblyEnvelope formulaResource :=
        Nat.add_le_add_left hinnerAssembly _
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le
    countBound.proof innerProof
  have houterBound : outerProof.payloadLength <= countResource +
      initialFinalResource + adjacentResource +
        2 * smallContextAssemblyEnvelope formulaResource := by
    calc
      outerProof.payloadLength <= countBound.proof.payloadLength +
          innerProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
              (initialFinalFormula ⋏ adjacentFormula) := by
        simpa only [outerProof, countFormula, innerProof, initialFinalFormula,
          adjacentFormula] using houter
      _ <= countResource +
          (initialFinalResource + adjacentResource +
            smallContextAssemblyEnvelope formulaResource) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
            (initialFinalFormula ⋏ adjacentFormula) :=
        Nat.add_le_add (Nat.add_le_add hcount hinnerBound) (Nat.le_refl _)
      _ <= countResource + initialFinalResource + adjacentResource +
          2 * smallContextAssemblyEnvelope formulaResource := by
        omega
  change (CertifiedPAContextProof.cast _
    (CertifiedPAContextProof.cast _ outerProof)).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  unfold compactParserSyntaxExactBoundedUniformPayloadPolynomial
  dsimp only [countResource, initialFinalResource, adjacentResource,
    formulaResource]
  exact houterBound

#print axioms
  compactParserSyntaxExactBoundedUniformClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxExactBoundedUniformResourceDirectCompiler

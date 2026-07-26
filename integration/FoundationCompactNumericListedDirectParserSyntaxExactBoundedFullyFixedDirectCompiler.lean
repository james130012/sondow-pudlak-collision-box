import integration.FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Fully fixed direct compiler for the exact bounded parser graph -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxExactBoundedFullyFixedDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph
open FoundationCompactNumericListedDirectAdditiveCodecGraph

def compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    (tokenCount inputCount tableWidth valueBound numericBound bitBound : Nat) :
    Nat :=
  compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound +
    compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount valueBound numericBound bitBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount inputCount tableWidth valueBound numericBound bitBound + 16

def compactParserSyntaxExactBoundedFullyFixedAssemblyPayloadPolynomial
    (tokenCount inputCount tableWidth valueBound numericBound bitBound : Nat) :
    Nat :=
  let count :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let initialFinal :=
    compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount valueBound numericBound bitBound
  let adjacent :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount inputCount tableWidth valueBound numericBound bitBound
  count + initialFinal + adjacent +
    2 * smallContextAssemblyEnvelope
      (compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
        tokenCount inputCount tableWidth valueBound numericBound bitBound)

def compactParserSyntaxExactBoundedFullyFixedPayloadPolynomial
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) : Nat :=
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxExactBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  compactParserSyntaxExactBoundedFullyFixedAssemblyPayloadPolynomial tokenCount
    inputCount tableWidth valueBound numericBound bitBound

noncomputable def
    compactParserSyntaxExactBoundedFullyFixedClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound)
      (compactParserSyntaxExactBoundedFullyFixedPayloadPolynomial tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound) := by
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxExactBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  have htrace : CompactParserSyntaxTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactParserSyntaxExactFuel] using hgraph
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hstateCount : stateCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hfuel : compactParserSyntaxExactFuel inputCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hinputBoundary : inputBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hinputCount : inputCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hexpectedBoundary : expectedBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hexpectedCount : expectedCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htaskKind : taskKind <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htaskBinderArity : taskBinderArity <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htaskRepeatCount : taskRepeatCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hvalueBoundSucc : valueBound + 1 <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have harea : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
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
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  let countBound :=
    parserInitialFinalExactFuelCountClosedDirectBound stateCount inputCount
      htrace.1
  let initialFinalBound :=
    compactParserInitialFinalBoundedExactFuelFullyFixedClosedDirectBoundOfBounded
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound htrace.2.1 hwidth
      htokenCount hstateCount hinputCount hexpectedCount hvalueBoundSucc
      htokenTableSize hstateBoundarySize hinputBoundarySize
      hexpectedBoundarySize htaskKindSize htaskBinderAritySize
      htaskRepeatCountSize hnumericSize hbitPositive
  let adjacentProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound htrace.2.2 hfuel hvalueBound hwidth
      (hwidth.trans hnumericBit) htokenCount hstateCount htokenTableSize
      hstateBoundarySize harea (harea.trans hnumericBit) hnumericSize
      hbitPositive
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let initialFinalFormula :=
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound
  let adjacentFormula :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputCount tableWidth valueBound
  let countResource :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let initialFinalResource :=
    compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount valueBound numericBound bitBound
  let adjacentResource :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
      tokenCount inputCount tableWidth valueBound numericBound bitBound
  let formulaResource :=
    compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
      tokenCount inputCount tableWidth valueBound numericBound bitBound
  have hcount : countBound.proof.payloadLength <= countResource :=
    countBound.payloadLength_le.trans
      (compactParserInitialFinalExactFuelCountResource_le_fixed inputCount
        numericBound hinputCount)
  have hinitialFinal : initialFinalBound.proof.payloadLength <=
      initialFinalResource := initialFinalBound.payloadLength_le
  have hadjacent : adjacentProof.payloadLength <= adjacentResource :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound htrace.2.2 hinputCount hfuel hvalueBound
      hwidth (hwidth.trans hnumericBit) htokenCount hstateCount
      htokenTableSize hstateBoundarySize harea (harea.trans hnumericBit)
      hnumericSize hbitPositive
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
    unfold compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    omega
  have houterCode :
      (binaryFormulaCode
        (countFormula ⋏ (initialFinalFormula ⋏ adjacentFormula))).length <=
        formulaResource := by
    have hraw := binaryFormulaCode_and_length_le countFormula
      (initialFinalFormula ⋏ adjacentFormula)
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    omega
  have hformulaContext : FormulaCodeBound ∅ formulaResource := by
    intro formula hmem
    simp at hmem
  have hcountFormulaFixed :
      (binaryFormulaCode countFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    omega
  have hinitialFinalFormulaFixed :
      (binaryFormulaCode initialFinalFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    omega
  have hadjacentFormulaFixed :
      (binaryFormulaCode adjacentFormula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactBoundedFullyFixedAssemblyFormulaPolynomial
    omega
  have hinnerAssembly := conjunctionFullAssemblyCost_le_small ∅
    initialFinalFormula adjacentFormula formulaResource (by simp)
    hformulaContext hinitialFinalFormulaFixed hadjacentFormulaFixed hinnerCode
  have houterAssembly := conjunctionFullAssemblyCost_le_small ∅ countFormula
    (initialFinalFormula ⋏ adjacentFormula) formulaResource (by simp)
    hformulaContext hcountFormulaFixed hinnerCode houterCode
  let innerProof := CertifiedPAContextProof.conjunction
    initialFinalBound.proof adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction
    countBound.proof innerProof
  let traceProof := CertifiedPAContextProof.cast
    (compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound).symm outerProof
  let proof := CertifiedPAContextProof.cast
    (compactParserSyntaxExactBoundedDirectClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound).symm traceProof
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
        Nat.add_le_add
          (Nat.add_le_add hcount hinnerBound)
          (Nat.le_refl _)
      _ <= countResource + initialFinalResource + adjacentResource +
          2 * smallContextAssemblyEnvelope formulaResource := by
        omega
  change (CertifiedPAContextProof.cast _
    (CertifiedPAContextProof.cast _ outerProof)).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  unfold compactParserSyntaxExactBoundedFullyFixedPayloadPolynomial
  dsimp only [numericBound, bitBound]
  unfold compactParserSyntaxExactBoundedFullyFixedAssemblyPayloadPolynomial
  dsimp only [countResource, initialFinalResource, adjacentResource,
    formulaResource]
  exact houterBound

#print axioms
  compactParserSyntaxExactBoundedFullyFixedClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxExactBoundedFullyFixedDirectCompiler

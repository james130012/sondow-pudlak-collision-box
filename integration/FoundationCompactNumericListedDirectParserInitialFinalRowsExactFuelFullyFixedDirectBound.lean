import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelAlignment

/-!
# Fully assembled parser endpoints at the exact composite fuel term

The five checked endpoint leaves are joined in the order of the original
thirty-six-coordinate graph.  The output formula contains the composite fuel
term in both the state-count equation and final row index.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFullyFixedDirectBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelAlignment

def compactUnifiedParserInitialFinalRowsExactFuelDirectResource
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) : Nat :=
  let formula1 :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let formula2 :=
    compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount 0 witness.initialCoordinates
      witness.initialSizeWitness
  let formula3 :=
    compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
      tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
      taskBinderArity taskRepeatCount
  let formula4 :=
    compactParserInitialFinalExactFuelFinalAtFormula tokenTable width tokenCount
      stateBoundary stateCount inputCount witness.finalCoordinates
      witness.finalSizeWitness
  let formula5 :=
    compactUnifiedParserFinalStateRowsClosedFormula tokenTable width tokenCount
      witness.finalCoordinates expectedBoundary expectedCount
      witness.outputStart witness.outputBoundary witness.outputBoundarySize
  let resource1 := compactParserInitialFinalExactFuelCountResource inputCount
  let resource2 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound
  let resource3 :=
    parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound
  let resource4 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (compactParserSyntaxExactFuelTerm inputCount) numericBound bitBound
  let resource5 :=
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound bitBound
  let resource45 := resource4 + resource5 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula4 formula5
  let resource345 := resource3 + resource45 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula3
      (formula4 ⋏ formula5)
  let resource2345 := resource2 + resource345 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula2
      (formula3 ⋏ (formula4 ⋏ formula5))
  resource1 + resource2345 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula1
      (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))

noncomputable def
    compactUnifiedParserInitialFinalRowsExactFuelExplicitDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount numericBound witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialFinalRowsExactFuelExplicitFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness)
      (compactUnifiedParserInitialFinalRowsExactFuelDirectResource tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount numericBound bitBound witness) := by
  let leaves := parserInitialFinalExactFuelFiveLeafBoundsOfGraph tokenTable
    width tokenCount stateBoundary stateCount inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    numericBound bitBound witness hgraph hvalue hsize hnumericSize hbitPositive
  let formula1 :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let formula2 :=
    compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount 0 witness.initialCoordinates
      witness.initialSizeWitness
  let formula3 :=
    compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
      tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
      taskBinderArity taskRepeatCount
  let formula4 :=
    compactParserInitialFinalExactFuelFinalAtFormula tokenTable width tokenCount
      stateBoundary stateCount inputCount witness.finalCoordinates
      witness.finalSizeWitness
  let formula5 :=
    compactUnifiedParserFinalStateRowsClosedFormula tokenTable width tokenCount
      witness.finalCoordinates expectedBoundary expectedCount
      witness.outputStart witness.outputBoundary witness.outputBoundarySize
  let resource1 := compactParserInitialFinalExactFuelCountResource inputCount
  let resource2 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound
  let resource3 :=
    parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound
  let resource4 :=
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (compactParserSyntaxExactFuelTerm inputCount) numericBound bitBound
  let resource5 :=
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound bitBound
  let resource45 := resource4 + resource5 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula4 formula5
  let resource345 := resource3 + resource45 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula3
      (formula4 ⋏ formula5)
  let resource2345 := resource2 + resource345 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula2
      (formula3 ⋏ (formula4 ⋏ formula5))
  let totalResource := resource1 + resource2345 +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula1
      (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))
  let proof45 := CertifiedPAContextProof.conjunction
    leaves.finalAt.proof leaves.final.proof
  let proof345 := CertifiedPAContextProof.conjunction
    leaves.initial.proof proof45
  let proof2345 := CertifiedPAContextProof.conjunction
    leaves.initialAt.proof proof345
  let assembled := CertifiedPAContextProof.conjunction
    leaves.count.proof proof2345
  refine { proof := assembled, payloadLength_le := ?_ }
  have h45 := CertifiedPAContextProof.conjunction_payloadLength_le
    leaves.finalAt.proof leaves.final.proof
  have h345 := CertifiedPAContextProof.conjunction_payloadLength_le
    leaves.initial.proof proof45
  have h2345 := CertifiedPAContextProof.conjunction_payloadLength_le
    leaves.initialAt.proof proof345
  have hassembled := CertifiedPAContextProof.conjunction_payloadLength_le
    leaves.count.proof proof2345
  have h1 := leaves.count.payloadLength_le
  have h2 := leaves.initialAt.payloadLength_le
  have h3 := leaves.initial.payloadLength_le
  have h4 := leaves.finalAt.payloadLength_le
  have h5 := leaves.final.payloadLength_le
  have hproof45 : proof45.payloadLength <= resource45 := by
    calc
      proof45.payloadLength <=
          leaves.finalAt.proof.payloadLength +
            leaves.final.proof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
              formula4 formula5 := by
        simpa only [proof45, formula4, formula5] using h45
      _ <= resource45 := by
        dsimp only [resource45, resource4, resource5]
        omega
  have hproof345 : proof345.payloadLength <= resource345 := by
    calc
      proof345.payloadLength <=
          leaves.initial.proof.payloadLength + proof45.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula3
              (formula4 ⋏ formula5) := by
        simpa only [proof345, formula3, formula4, formula5] using h345
      _ <= resource345 := by
        dsimp only [resource345, resource3]
        omega
  have hproof2345 : proof2345.payloadLength <= resource2345 := by
    calc
      proof2345.payloadLength <=
          leaves.initialAt.proof.payloadLength + proof345.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula2
              (formula3 ⋏ (formula4 ⋏ formula5)) := by
        simpa only [proof2345, formula2, formula3, formula4, formula5] using
          h2345
      _ <= resource2345 := by
        dsimp only [resource2345, resource2]
        omega
  have htotal : assembled.payloadLength <= totalResource := by
    calc
      assembled.payloadLength <=
          leaves.count.proof.payloadLength + proof2345.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula1
              (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))) := by
        simpa only [assembled, formula1, formula2, formula3, formula4,
          formula5] using hassembled
      _ <= totalResource := by
        dsimp only [totalResource, resource1]
        omega
  change assembled.payloadLength <=
    compactUnifiedParserInitialFinalRowsExactFuelDirectResource tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      numericBound bitBound witness
  simpa only [
    compactUnifiedParserInitialFinalRowsExactFuelDirectResource,
    formula1, formula2, formula3, formula4, formula5,
    resource1, resource2, resource3, resource4, resource5,
    resource45, resource345, resource2345, totalResource] using htotal

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuelExplicitDirectBoundOfGraph

noncomputable def
    compactUnifiedParserInitialFinalRowsExactFuelClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount numericBound witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness)
      (compactUnifiedParserInitialFinalRowsExactFuelDirectResource tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount numericBound bitBound witness) := by
  let explicit :=
    compactUnifiedParserInitialFinalRowsExactFuelExplicitDirectBoundOfGraph
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound witness hgraph hvalue hsize
      hnumericSize hbitPositive
  let proof :=
    CertifiedPAContextProof.cast
      (compactUnifiedParserInitialFinalRowsExactFuel_alignment tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness).symm explicit.proof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.cast _ explicit.proof).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  exact explicit.payloadLength_le

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuelClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFullyFixedDirectBound

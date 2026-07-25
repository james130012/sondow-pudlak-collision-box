import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds

/-! # Fully fixed valid and invalid Term tag-two decision endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionFullyFixedBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermTwoValidChoiceFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoInvalidChoiceFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

def syntaxTermTwoValidDecisionFullyFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxTermTwoDecisionPathFixedPayloadEnvelope
    (syntaxTermTwoSelectedFixedPayloadEnvelope
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
        numericBound bitBound)
      (syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermValidBranchFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        bitBound)
      bitBound)
    bitBound

def syntaxTermTwoInvalidDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  syntaxTermTwoDecisionPathFixedPayloadEnvelope
    (syntaxTermTwoSelectedFixedPayloadEnvelope
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
        numericBound bitBound)
      (syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermInvalidBranchFixedPayloadEnvelope numericBound bitBound)
        bitBound)
      bitBound)
    bitBound

noncomputable def syntaxTermTwoValidFullyFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) :
    CheckedHybridValuationBoundedFormulaCertificate termZeroValuation
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) :=
  syntaxTermTwoFixedDecisionPathCertificate tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermTwoFixedSelectedCertificate tokenTable width tokenCount current
      next binderArity witness htag hthree hatFunction
      (syntaxTermTwoValidFixedChoiceCertificate tokenTable width tokenCount
        current next binderArity witness hvalid hfunction))

noncomputable def syntaxTermTwoInvalidFullyFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    CheckedHybridValuationBoundedFormulaCertificate termZeroValuation
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) :=
  syntaxTermTwoFixedDecisionPathCertificate tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermTwoFixedSelectedCertificate tokenTable width tokenCount current
      next binderArity witness htag hthree hatFunction
      (syntaxTermTwoInvalidFixedChoiceCertificate tokenTable width tokenCount
        current next binderArity witness hinvalid hfailure))

theorem
    syntaxTermTwoValidFullyFixedDecisionCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument)
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
    (htagSize : Nat.size witness.tag <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoValidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hvalid hfunction) <=
      syntaxTermTwoValidDecisionFullyFixedPayloadEnvelope tokenCount
        numericBound bitBound := by
  let choice :=
    syntaxTermTwoValidFixedChoiceCertificate tokenTable width tokenCount current
      next binderArity witness hvalid hfunction
  let selected :=
    syntaxTermTwoFixedSelectedCertificate tokenTable width tokenCount current
      next binderArity witness htag hthree hatFunction choice
  have hchoice :=
    syntaxTermTwoValidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hvalid hfunction hwidth htokenCount hcurrentValue
      hnextValue htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderSize hargumentSize hfunctionCodeSize hnumericSize hsize
  have hselected :=
    syntaxTermTwoFixedSelectedCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness htag hthree hatFunction choice
      (syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermValidBranchFixedPayloadEnvelope tokenCount numericBound
          bitBound)
        bitBound)
      hchoice hwidth htokenCount hcurrentValue htokenTableSize hcurrentSize
      htagSize hfunctionCodeSize hnumericSize hsize
  have hpath :=
    syntaxTermTwoFixedDecisionPathCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity bitBound witness
      selected
      (syntaxTermTwoSelectedFixedPayloadEnvelope
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
          numericBound bitBound)
        (syntaxTermValidityChoiceFixedPayloadEnvelope
          (syntaxTermValidBranchFixedPayloadEnvelope tokenCount numericBound
            bitBound)
          bitBound)
        bitBound)
      hselected hsize
  simpa only [syntaxTermTwoValidFullyFixedDecisionCertificate, choice, selected,
    syntaxTermTwoValidDecisionFullyFixedPayloadEnvelope] using hpath

theorem
    syntaxTermTwoInvalidFullyFixedDecisionCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
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
    (htagSize : Nat.size witness.tag <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoInvalidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hinvalid hfailure) <=
      syntaxTermTwoInvalidDecisionFullyFixedPayloadEnvelope numericBound
        bitBound := by
  let choice :=
    syntaxTermTwoInvalidFixedChoiceCertificate tokenTable width tokenCount
      current next binderArity witness hinvalid hfailure
  let selected :=
    syntaxTermTwoFixedSelectedCertificate tokenTable width tokenCount current
      next binderArity witness htag hthree hatFunction choice
  have hchoice :=
    syntaxTermTwoInvalidFixedChoiceCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness hinvalid hfailure hwidth htokenCount htailCount
      hcurrentValue hnextValue htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize hargumentSize hfunctionCodeSize
      hnumericSize hbitPositive hsize
  have hselected :=
    syntaxTermTwoFixedSelectedCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity numericBound
      bitBound witness htag hthree hatFunction choice
      (syntaxTermValidityChoiceFixedPayloadEnvelope
        (syntaxTermInvalidBranchFixedPayloadEnvelope numericBound bitBound)
        bitBound)
      hchoice hwidth htokenCount hcurrentValue htokenTableSize hcurrentSize
      htagSize hfunctionCodeSize hnumericSize hsize
  have hpath :=
    syntaxTermTwoFixedDecisionPathCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity bitBound witness
      selected
      (syntaxTermTwoSelectedFixedPayloadEnvelope
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
          numericBound bitBound)
        (syntaxTermValidityChoiceFixedPayloadEnvelope
          (syntaxTermInvalidBranchFixedPayloadEnvelope numericBound bitBound)
          bitBound)
        bitBound)
      hselected hsize
  simpa only [syntaxTermTwoInvalidFullyFixedDecisionCertificate, choice,
    selected, syntaxTermTwoInvalidDecisionFullyFixedPayloadEnvelope] using
      hpath

#print axioms
  syntaxTermTwoValidFullyFixedDecisionCertificate_structuralPayloadBound_le
#print axioms
  syntaxTermTwoInvalidFullyFixedDecisionCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionFullyFixedBounds

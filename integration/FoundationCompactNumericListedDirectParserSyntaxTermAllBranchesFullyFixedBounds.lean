import integration.FoundationCompactNumericListedDirectParserSyntaxTermShortBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermEnoughBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermZeroSuccessDecisionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermZeroFailureDecisionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermOneDecisionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoShortDecisionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermInvalidTagDecisionFullyFixedBounds

/-! # Fully fixed certificate for all eight Term branch cases -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermShortBranchFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermEnoughBranchFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermZeroSuccessDecisionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermZeroFailureDecisionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermOneDecisionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoShortDecisionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermInvalidTagDecisionFullyFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

def syntaxTermAllBranchesFullyFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  syntaxTermShortBranchFullyFixedPayloadEnvelope numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermZeroSuccessDecisionFullyFixedPayloadEnvelope numericBound
      bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermZeroFailureDecisionFullyFixedPayloadEnvelope numericBound
      bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermOneDecisionFullyFixedPayloadEnvelope numericBound bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermTwoShortDecisionFullyFixedPayloadEnvelope numericBound bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermTwoValidDecisionFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermTwoInvalidDecisionFullyFixedPayloadEnvelope numericBound
      bitBound)
    numericBound bitBound +
  syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (syntaxTermInvalidTagDecisionFullyFixedPayloadEnvelope numericBound
      bitBound)
    numericBound bitBound

noncomputable def syntaxTermFullyFixedBranchCertificateFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  cases data with
  | short hcount hfailure =>
      exact syntaxTermShortFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hfailure
  | zeroSuccess hcount hatTag hatArgument htag hargument hcontinue =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (compactSyntaxTermZeroSuccessDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hcontinue)
  | zeroFailure hcount hatTag hatArgument htag hargument hfailure =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (compactSyntaxTermZeroFailureDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hfailure)
  | one hcount hatTag hatArgument htag hcontinue =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (compactSyntaxTermOneDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hcontinue)
  | twoShort hcount hatTag hatArgument htag htooShort hfailure =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (syntaxTermTwoShortFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag htooShort hfailure)
  | twoValid hcount hatTag hatArgument htag hthree hatFunction hvalid
      hfunction =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (syntaxTermTwoValidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hvalid hfunction)
  | twoInvalid hcount hatTag hatArgument htag hthree hatFunction hinvalid
      hfailure =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (syntaxTermTwoInvalidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hinvalid hfailure)
  | invalidTag hcount hatTag hatArgument hne0 hne1 hne2 hfailure =>
      exact syntaxTermEnoughFullyFixedBranchCertificate tokenTable width
        tokenCount current next binderArity witness hcount hatTag hatArgument
        (syntaxTermInvalidTagFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness hne0 hne1 hne2 hfailure)

theorem
    syntaxTermFullyFixedBranchCertificateFromData_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
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
    (htagSize : Nat.size witness.tag <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFullyFixedBranchCertificateFromData tokenTable width
          tokenCount current next binderArity witness data) <=
      syntaxTermAllBranchesFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  cases data with
  | short hcount hfailure =>
      have hbranch :=
        syntaxTermShortFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hfailure hwidth htokenCount htailCount
          hcurrentValue hnextValue htokenTableSize hcurrentSize hnextSize
          htailBoundarySize hnumericSize hbitPositive hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      exact hbranch.trans (by omega)
  | zeroSuccess hcount hatTag hatArgument htag hargument hcontinue =>
      let decision :=
        compactSyntaxTermZeroSuccessDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hcontinue
      have hdecision :=
        compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag hargument hcontinue hwidth htokenCount
          htailCount hcurrentValue hnextValue htokenTableSize hcurrentSize
          hnextSize htailBoundarySize htagSize hargumentSize hbinderSize
          hnumericSize hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermZeroSuccessDecisionFullyFixedPayloadEnvelope numericBound
            bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | zeroFailure hcount hatTag hatArgument htag hargument hfailure =>
      let decision :=
        compactSyntaxTermZeroFailureDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hfailure
      have hdecision :=
        compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag hargument hfailure hwidth htokenCount
          htailCount hcurrentValue hnextValue htokenTableSize hcurrentSize
          hnextSize htailBoundarySize htagSize hargumentSize hbinderSize
          hnumericSize hbitPositive hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermZeroFailureDecisionFullyFixedPayloadEnvelope numericBound
            bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | one hcount hatTag hatArgument htag hcontinue =>
      let decision :=
        compactSyntaxTermOneDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hcontinue
      have hdecision :=
        compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag hcontinue hwidth htokenCount htailCount
          hcurrentValue hnextValue htokenTableSize hcurrentSize hnextSize
          htailBoundarySize htagSize hnumericSize hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermOneDecisionFullyFixedPayloadEnvelope numericBound bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | twoShort hcount hatTag hatArgument htag htooShort hfailure =>
      let decision :=
        syntaxTermTwoShortFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag htooShort hfailure
      have hdecision :=
        syntaxTermTwoShortFullyFixedDecisionCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag htooShort hfailure hwidth htokenCount
          htailCount hcurrentValue hnextValue htokenTableSize hcurrentSize
          hnextSize htailBoundarySize htagSize hnumericSize hbitPositive hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermTwoShortDecisionFullyFixedPayloadEnvelope numericBound
            bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | twoValid hcount hatTag hatArgument htag hthree hatFunction hvalid
      hfunction =>
      let decision :=
        syntaxTermTwoValidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hvalid hfunction
      have hdecision :=
        syntaxTermTwoValidFullyFixedDecisionCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag hthree hatFunction hvalid hfunction hwidth
          htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
          hnextSize htagSize htailBoundarySize hbinderSize hargumentSize
          hfunctionCodeSize hnumericSize hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermTwoValidDecisionFullyFixedPayloadEnvelope tokenCount
            numericBound bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | twoInvalid hcount hatTag hatArgument htag hthree hatFunction hinvalid
      hfailure =>
      let decision :=
        syntaxTermTwoInvalidFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hinvalid hfailure
      have hdecision :=
        syntaxTermTwoInvalidFullyFixedDecisionCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness htag hthree hatFunction hinvalid hfailure hwidth
          htokenCount htailCount hcurrentValue hnextValue htokenTableSize
          ((Nat.size_le_size hwidth).trans hnumericSize)
          ((Nat.size_le_size htokenCount).trans hnumericSize)
          hcurrentSize hnextSize htagSize htailBoundarySize hargumentSize
          hfunctionCodeSize hnumericSize hbitPositive hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermTwoInvalidDecisionFullyFixedPayloadEnvelope numericBound
            bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)
  | invalidTag hcount hatTag hatArgument hne0 hne1 hne2 hfailure =>
      let decision :=
        syntaxTermInvalidTagFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness hne0 hne1 hne2 hfailure
      have hdecision :=
        syntaxTermInvalidTagFullyFixedDecisionCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hne0 hne1 hne2 hfailure hwidth htokenCount
          htailCount hcurrentValue hnextValue htokenTableSize hcurrentSize
          hnextSize htailBoundarySize htagSize hnumericSize hbitPositive hsize
      have hbranch :=
        syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
          tokenTable width tokenCount current next binderArity numericBound
          bitBound witness hcount hatTag hatArgument decision
          (syntaxTermInvalidTagDecisionFullyFixedPayloadEnvelope numericBound
            bitBound)
          hdecision hwidth htokenCount hcurrentValue htokenTableSize
          hcurrentSize htagSize hargumentSize hnumericSize hsize
      unfold syntaxTermFullyFixedBranchCertificateFromData
        syntaxTermAllBranchesFullyFixedPayloadEnvelope
      dsimp only [decision] at hbranch
      exact hbranch.trans (by omega)

#print axioms
  syntaxTermFullyFixedBranchCertificateFromData_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermAllBranchesFullyFixedBounds

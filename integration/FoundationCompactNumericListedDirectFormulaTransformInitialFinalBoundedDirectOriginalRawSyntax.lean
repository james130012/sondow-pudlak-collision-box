import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate

/-! # Public copy of the original thirty-one-witness raw matrix -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalRawSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate

def compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerms
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    Fin 44 -> ArithmeticSemiterm Nat 31 :=
  ![sourceSubstitutionLift 31 (shortBinaryNumeralTerm tokenTable),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm width),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm tokenCount),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm stateBoundary),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm stateCount),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm fuel),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm inputBoundary),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm inputCount),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedOutputBoundary),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedOutputCount),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedSuffixBoundary),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm expectedSuffixCount),
    sourceSubstitutionLift 31 (shortBinaryNumeralTerm binderArity),
    (#30 : ArithmeticSemiterm Nat 31), #29, #28, #27, #26, #25, #24,
    #23, #22, #21, #20, #19, #18, #17, #16, #15, #14, #13, #12,
    #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

def compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    ArithmeticSemiformula Nat 31 :=
  (Rewriting.emb (ξ := Nat)
      compactFormulaTransformInitialFinalRowsDef.val) ⇜
    compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerms
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity

theorem compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_originalRaw
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 31
        (compactFormulaTransformInitialFinalBoundedDirectOriginalRawTerminal
          tokenTable width tokenCount stateBoundary stateCount fuel
          inputBoundary inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity) := by
  rw [compactFormulaTransformInitialFinalBoundedClosedFormula_alignment]
  congr 1

#print axioms
  compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_originalRaw

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalRawSyntax

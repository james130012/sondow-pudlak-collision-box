import integration.FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-! # Fixed syntax bounds for the exact parser final-state formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def parserFinalZeroValuation : Nat -> Nat := fun _ => 0

def parserFinalPrefixFormula
    (tokenTable width tokenCount tasksFinish outputStart : Nat) :
    ValuationFormula :=
  compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width tokenCount
    tasksFinish outputStart

def parserFinalLayoutFormula
    (tokenTable width tokenCount outputStart sourceCount finish
      outputBoundary : Nat) : ValuationFormula :=
  compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
    outputStart sourceCount finish outputBoundary

def parserFinalSameFormula
    (tokenTable width tokenCount sourceBoundary sourceCount outputBoundary :
      Nat) : ValuationFormula :=
  compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
    sourceBoundary sourceCount outputBoundary sourceCount

def parserFinalSizeFormula
    (outputBoundarySize outputBoundary : Nat) : ValuationFormula :=
  compactNatSizeClosedFormula outputBoundarySize outputBoundary

def parserFinalAreaFormula
    (outputBoundarySize sourceCount tokenCount : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
    (!!(shortBinaryNumeralTerm sourceCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)”

def parserFinalStateClosedTerms
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) : Fin 16 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm coordinates.start,
    shortBinaryNumeralTerm coordinates.finish,
    shortBinaryNumeralTerm coordinates.tokensFinish,
    shortBinaryNumeralTerm coordinates.tasksFinish,
    shortBinaryNumeralTerm coordinates.tokensBoundary,
    shortBinaryNumeralTerm coordinates.tokensCount,
    shortBinaryNumeralTerm coordinates.tasksBoundary,
    shortBinaryNumeralTerm coordinates.tasksCount,
    shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm outputStart,
    shortBinaryNumeralTerm outputBoundary,
    shortBinaryNumeralTerm outputBoundarySize]

def parserFinalStateFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactUnifiedParserFinalStateRowsDef.val)).length

def parserFinalStateSyntaxResource (bitBound : Nat) : Nat :=
  parserFinalStateFormulaCodeEnvelope bitBound + 1

theorem compactUnifiedParserFinalStateRowsClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize
      bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size coordinates.start <= bitBound)
    (hfinishSize : Nat.size coordinates.finish <= bitBound)
    (htokensFinishSize : Nat.size coordinates.tokensFinish <= bitBound)
    (htasksFinishSize : Nat.size coordinates.tasksFinish <= bitBound)
    (htokensBoundarySize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htokensCountSize : Nat.size coordinates.tokensCount <= bitBound)
    (htasksBoundarySize : Nat.size coordinates.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size coordinates.tasksCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (houtputBoundarySize : Nat.size outputBoundary <= bitBound)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount coordinates sourceBoundary sourceCount outputStart
          outputBoundary outputBoundarySize)).length <=
      parserFinalStateSyntaxResource bitBound := by
  let terms := parserFinalStateClosedTerms tokenTable width tokenCount
    coordinates sourceBoundary sourceCount outputStart outputBoundary
    outputBoundarySize
  let source : ArithmeticSemiformula Nat 16 :=
    Rewriting.emb (ξ := Nat) compactUnifiedParserFinalStateRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <=
        binaryNumeralTermCodeEnvelope bitBound := by
    intro coordinate
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
        htokenTableSize
    · exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
        htokenCountSize
    · exact binaryNumeralTerm_code_length_le_envelope coordinates.start bitBound
        hstartSize
    · exact binaryNumeralTerm_code_length_le_envelope coordinates.finish bitBound
        hfinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensFinish bitBound htokensFinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksFinish bitBound htasksFinishSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensBoundary bitBound htokensBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tokensCount bitBound htokensCountSize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksBoundary bitBound htasksBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope
        coordinates.tasksCount bitBound htasksCountSize
    · exact binaryNumeralTerm_code_length_le_envelope sourceBoundary bitBound
        hsourceBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
        hsourceCountSize
    · exact binaryNumeralTerm_code_length_le_envelope outputStart bitBound
        houtputStartSize
    · exact binaryNumeralTerm_code_length_le_envelope outputBoundary bitBound
        houtputBoundarySize
    · exact binaryNumeralTerm_code_length_le_envelope outputBoundarySize bitBound
        houtputBoundarySizeSize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode source).length terms source hterms le_rfl
  have hraw' := hraw.trans (Nat.le_succ _)
  unfold compactUnifiedParserFinalStateRowsClosedFormula
    parserFinalStateSyntaxResource parserFinalStateFormulaCodeEnvelope
  simpa only [sourceSubstitutionQpow, terms, source,
    parserFinalStateClosedTerms] using hraw'

theorem compactUnifiedParserFinalStateRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) :
    (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
      tokenCount coordinates sourceBoundary sourceCount outputStart
        outputBoundary outputBoundarySize).freeVariables = ∅ := by
  unfold compactUnifiedParserFinalStateRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactUnifiedParserFinalStateRowsClosedFormula_code_length_le_fixed
#print axioms
  compactUnifiedParserFinalStateRowsClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserFinalStateSyntaxFixedBounds

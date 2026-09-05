import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds

/-! # Fixed entry resources for natural-list cons tail rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate

def natListConsRowsTailOpenIndexTermCodeBound : Nat :=
  (binaryTermCode consRowsTailIndexTerm).length +
    (binaryTermCode consRowsTailSuccessorTerm).length +
    (binaryTermCode consRowsTailSecondSuccessorTerm).length + 1

def natListConsRowsTailEntryFixedScale
    (numericBound bitBound : Nat) : Nat :=
  fixedWidthOpenIndexAtomicUniformCoordinateCeiling
    (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
      natListConsRowsTailOpenIndexTermCodeBound)

def natListConsRowsTailEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (natListConsRowsTailEntryFixedScale numericBound bitBound)

theorem consRowsTailIndexTerm_code_length_le :
    (binaryTermCode consRowsTailIndexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound := by
  unfold natListConsRowsTailOpenIndexTermCodeBound
  omega

theorem consRowsTailSuccessorTerm_code_length_le :
    (binaryTermCode consRowsTailSuccessorTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound := by
  unfold natListConsRowsTailOpenIndexTermCodeBound
  omega

theorem consRowsTailSecondSuccessorTerm_code_length_le :
    (binaryTermCode consRowsTailSecondSuccessorTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound := by
  unfold natListConsRowsTailOpenIndexTermCodeBound
  omega

#print axioms consRowsTailIndexTerm_code_length_le
#print axioms consRowsTailSuccessorTerm_code_length_le
#print axioms consRowsTailSecondSuccessorTerm_code_length_le

end FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

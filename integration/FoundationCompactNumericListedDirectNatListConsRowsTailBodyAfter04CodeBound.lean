import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
import integration.FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity

/-! # Syntax bound after closing the first cons-tail witness -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter04CodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalSyntaxUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources

theorem natListConsRowsTailBodyAfter04_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (natListConsRowsTailBodyAfter04 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBodyAfter04FormulaCodePolynomial numericBound
        bitBound := by
  have hterminal :=
    compactAdditiveNatListConsRowsTailSourceTerminal_code_length_le_uniform
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have hraw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    tokenCount
    (natListConsRowsTailSourceTerminalFormulaCodePolynomial bitBound)
    (compactAdditiveNatListConsRowsTailTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) hterminal
  have hmono := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono 4
    htokenCount
    (Nat.le_refl
      (natListConsRowsTailSourceTerminalFormulaCodePolynomial bitBound))
  unfold natListConsRowsTailBodyAfter04
    natListConsRowsTailBodyAfter04FormulaCodePolynomial
  exact hraw.trans hmono

#print axioms natListConsRowsTailBodyAfter04_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter04CodeBound

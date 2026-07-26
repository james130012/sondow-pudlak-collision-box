import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationContextRewriting

/-! # Exact-context leaves for the open-index sequent-step compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax

/-- A proof together with an explicit payload bound in its exact valuation
context. -/
structure ExactContextBoundedProof
    (valuation : Nat -> Nat) (formula : ValuationFormula) where
  resource : Nat
  proof : CertifiedPAContextProof
    (valuationContext formula.freeVariables valuation) formula
  payloadLength_le : proof.payloadLength <= resource

namespace ExactContextBoundedProof

def emptyContextTransportEnvelope
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (resource : Nat) : Nat :=
  resource +
    weakeningFullAssemblyCost
      (insert formula (valuationContext formula.freeVariables valuation))

/-- Transport an empty-context proof to the formula's exact valuation
context. -/
noncomputable def ofEmpty
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (bound : EmptyContextBoundedProof formula) :
    ExactContextBoundedProof valuation formula := by
  let target := valuationContext formula.freeVariables valuation
  let proof := CertifiedPAContextProof.weakenContext bound.proof
    (Finset.empty_subset target)
  let resource :=
    emptyContextTransportEnvelope valuation formula bound.resource
  refine
    { resource := resource
      proof := proof
      payloadLength_le := ?_ }
  have hweak :=
    CertifiedPAContextProof.weakenContext_payloadLength_le bound.proof
      (Finset.empty_subset target)
  have hbound := bound.payloadLength_le
  calc
    proof.payloadLength <=
        bound.proof.payloadLength +
          weakeningFullAssemblyCost (insert formula target) := by
      simpa only [proof] using hweak
    _ <= bound.resource +
        weakeningFullAssemblyCost (insert formula target) :=
      Nat.add_le_add_right hbound _
    _ = resource := by
      simp only [resource, emptyContextTransportEnvelope, target]

/-- Assemble two exact-context proofs with transparent resource accounting. -/
noncomputable def conjunction
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftBound : ExactContextBoundedProof valuation left)
    (rightBound : ExactContextBoundedProof valuation right) :
    ExactContextBoundedProof valuation (left ⋏ right) := by
  let proof := compileDirectConjunction
    leftBound.proof rightBound.proof
  let resource :=
    transparentHybridConjunctionPayloadEnvelope valuation left right
      leftBound.resource rightBound.resource
  refine
    { resource := resource
      proof := proof
      payloadLength_le := ?_ }
  have hbound :=
    compileDirectConjunction_payloadLength_le leftBound.proof rightBound.proof
      leftBound.resource rightBound.resource leftBound.payloadLength_le
      rightBound.payloadLength_le
  simpa only [proof, resource] using hbound

end ExactContextBoundedProof

private theorem arithmeticTwoTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem
    compactSequentFormulaStepIndexTerm_freeVariables_subset_singleton :
    (&0 : ValuationTerm).freeVariables ⊆ {0} := by
  simp

theorem
    compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton :
    (compactSequentFormulaStepIndexSuccessorTermAtValuation
      (&0 : ValuationTerm)).freeVariables ⊆ {0} := by
  simp [compactSequentFormulaStepIndexSuccessorTermAtValuation,
    arithmeticAddTerm_freeVariables_eq_union]

theorem
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton :
    (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
      (&0 : ValuationTerm)).freeVariables ⊆ {0} := by
  rw [compactSequentFormulaStepIndexSecondSuccessorTermAtValuation,
    arithmeticAddTerm_freeVariables_eq_union,
    arithmeticTwoTerm_freeVariables_eq_empty]
  simp

theorem
    termValue_compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
    (index : Nat) :
    termValue (extendValuation index zeroValuation)
        (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
          (&0 : ValuationTerm)) =
      index + 2 := by
  simp [compactSequentFormulaStepIndexSecondSuccessorTermAtValuation,
    termValue]

noncomputable def
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    (valuation : Nat -> Nat)
    (table width value : Nat) (indexTerm : ValuationTerm)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    ExactContextBoundedProof valuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value)) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  have hentryAtTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  let proof :=
    compileCompactFixedWidthEntryAtValuationExplicitHybridContext valuation
      tableTerm widthTerm indexTerm valueTerm hentryAtTerms
  let resource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
  refine
    { resource := resource
      proof := proof
      payloadLength_le := ?_ }
  have hcompile :=
    compileCompactFixedWidthEntryAtValuationExplicitHybridContext_payloadLength_le
      valuation tableTerm widthTerm indexTerm valueTerm hentryAtTerms
  have hopen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty table)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      hindex
      (shortBinaryNumeralTerm_freeVariables_eq_empty value)
      hentryAtTerms
  change proof.payloadLength <= resource
  simpa only [proof, resource,
    compactFixedWidthEntryAtValuationExplicitHybridFormulaStructuralPayloadBound]
    using hcompile.trans hopen

#print axioms
  compactSequentFormulaStepIndexTerm_freeVariables_subset_singleton
#print axioms
  compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
#print axioms
  compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton
#print axioms
  termValue_compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
#print axioms
  compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

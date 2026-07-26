import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompilerCore
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Proof projection for eighteen open-index row witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProofOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm valueBound) 18
          (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount)).freeVariables
        (extendValuation rowIndex
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation))
      (explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount)) := by
  let certified :=
    compactSequentFormulaStepRowBoundedAtValuationIndexWitnessCompilationOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let target :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount)
  exact castDirectCompilationProof certified.compilation target
    certified.formula_eq

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

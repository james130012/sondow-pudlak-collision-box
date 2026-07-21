import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition

/-!
# Explicit outer assembly for an accepted trace table

The exponential and positive-fuel conjuncts are closed here.  The three
remaining table components are accepted as checked certificates so that their
independent explicit constructions can be connected without semantic truth
selection.  This assembly is not the final closure endpoint until those
component certificates are supplied by their canonical constructors.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceTableExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAValuationTermCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev AcceptedTraceHybridCertificate
    (formula : ArithmeticProposition) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private noncomputable def acceptedTraceExponentialCertificate
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    AcceptedTraceHybridCertificate
      (compactNumericVerifierAcceptedTraceExponentialClosedFormula
        tableWidth valueBound) := by
  change AcceptedTraceHybridCertificate
    (exponentialAtValuationFormula
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

private noncomputable def acceptedTraceFuelGuardCertificate
    (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm) :
    AcceptedTraceHybridCertificate “0 < !!fuelTerm” := by
  let zeroTerm : ValuationTerm := ‘0’
  have hzero : termValue zeroValuation zeroTerm = 0 := by
    unfold zeroTerm
    change termValue zeroValuation
      (LO.FirstOrder.Semiterm.func Language.Zero.zero ![]) = 0
    exact termValue_zero zeroValuation ![]
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![zeroTerm, fuelTerm] (by
        change termValue zeroValuation zeroTerm <
          termValue zeroValuation fuelTerm
        rw [hzero]
        exact hfuel)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

/-- Exact conjunction assembly after all three middle table components have
been independently certified. -/
noncomputable def
    compactNumericVerifierAcceptedTraceTableExplicitHybridCertificateOfComponents
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (fuelTerm : ValuationTerm)
    (hvalueBound : valueBound = 2 ^ tableWidth)
    (hfuel : 0 < termValue zeroValuation fuelTerm)
    (hboundedGraph : AcceptedTraceHybridCertificate
      (compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
        tableWidth table valueBound fuelTerm))
    (hrowsAdjacent : AcceptedTraceHybridCertificate
      (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
        tableWidth table valueBound fuelTerm))
    (hinitialRow : AcceptedTraceHybridCertificate
      (compactNumericVerifierInitialWitnessTableRowClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish))
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) :
    AcceptedTraceHybridCertificate
      (compactNumericVerifierAcceptedTraceTableClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish fuelTerm) := by
  rw [compactNumericVerifierAcceptedTraceTableClosedFormula_eq_decomposed]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (acceptedTraceExponentialCertificate tableWidth valueBound hvalueBound)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (acceptedTraceFuelGuardCertificate fuelTerm hfuel)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        hboundedGraph
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          hrowsAdjacent
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            hinitialRow
            (compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
              tableWidth table fuelTerm hfuel haccepted)))))

#print axioms
  compactNumericVerifierAcceptedTraceTableExplicitHybridCertificateOfComponents

end FoundationCompactNumericListedDirectVerifierAcceptedTraceTableExplicitHybridCertificate

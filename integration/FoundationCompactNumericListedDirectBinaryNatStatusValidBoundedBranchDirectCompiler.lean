import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler

/-!
# Branch-sensitive direct compiler for bounded binary-Nat status validity

The public-finite status envelope sums over every four-tuple below
`valueBound`.  That is useful for removing proof dependence, but it cannot be
used for a bit-length polynomial when `valueBound = 2 ^ tableWidth`.

This compiler instead retains the real running/failed/completed branch selected
by the checked graph.  Its terminal resource contains no generated proof
payload and does not enumerate the numerical witness range.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity04
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler

local notation "statusZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate.zeroValuation

noncomputable def
    compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  compactBinaryNatStatusValidBoundedTerminalPartsStructuralPayloadEnvelopeOfData
    tokenTable width tokenCount start finish valueBound
    (compactBinaryNatStatusValidBoundedDataOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4
    (compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish)
    valueBound
    (compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
      tokenTable width tokenCount start finish)
    (compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph)

noncomputable def compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    ExplicitDirectFormulaBound statusZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph) := by
  let data := compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal
    tokenTable width tokenCount start finish
  let contextCodeBound :=
    compactBinaryNatStatusValidBoundedRawTerminalPublicContextCodeBound
      tokenTable width tokenCount start finish
  let bodyCodeBound := compactBinaryNatStatusValidBoundedRawTerminalPublicCodeBound
    tokenTable width tokenCount start finish
  let terminalResource :=
    compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph
      tokenTable width tokenCount start finish valueBound hgraph
  have hterminalStructural :
      hybridFormulaStructuralPayloadBound data.terminal <= terminalResource := by
    simpa only [terminalResource,
      compactBinaryNatStatusValidBoundedDirectTerminalBranchResourceOfGraph]
      using
        compactBinaryNatStatusValidBoundedExplicitHybridTerminalOfGraph_terminal_structuralPayloadBound_le_transparent
          tokenTable width tokenCount start finish valueBound hgraph
  have hterminal : data.terminal.compile.payloadLength <= terminalResource :=
    (compile_payloadLength_le_structuralPayloadBound data.terminal).trans
      hterminalStructural
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    Nat.le_refl _
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables statusZeroValuation) <=
        contextCodeBound :=
    Nat.le_refl _
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 4 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody data.values data.values_le
      hbody hcontext terminalResource data.terminal.compile hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity04
      contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal.compile
      hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound :=
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment
      tokenTable width tokenCount start finish valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  exact hcoordinates.2

noncomputable def
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula
          tokenTable width tokenCount start finish valueBound).freeVariables
        valuation)
      (compactBinaryNatStatusValidBoundedClosedFormula
        tokenTable width tokenCount start finish valueBound) := by
  let direct := compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext direct.proof

theorem
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound : Nat)
    (hgraph : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount start finish valueBound) :
    (compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
        hgraph).payloadLength <=
      compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
        tokenTable width tokenCount start finish valueBound hgraph := by
  let direct := compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
    tokenTable width tokenCount start finish valueBound hgraph
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          statusZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula
            tokenTable width tokenCount start finish valueBound).freeVariables
          valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  change (CertifiedPAContextProof.castContext hcontext direct.proof).payloadLength
    <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact direct.payloadLength_le

#print axioms
  compactBinaryNatStatusValidBoundedBranchDirectBoundOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler

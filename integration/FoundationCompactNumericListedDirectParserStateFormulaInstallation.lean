import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectTraceParserStateLayouts

/-!
# Installation of the parser-state core formula into parser traces

Every row in each of the proof, certificate, and formula parser components is
given explicit numeric coordinates and size witnesses that satisfy the actual
thirteen-variable Delta-zero state-core formula.  The typed status layout is
retained only as the bridge for the subsequent parser-step case formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateFormulaInstallation

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectTraceParserStateLayouts
open FoundationCompactNumericListedDirectParserStateFormula

def CompactUnifiedParserStateListCoreFormulaRows
    (tokenTable width tokenCount stateBoundary : Nat)
    (states : List CompactUnifiedParserState) : Prop :=
  ∀ index < states.length,
    ∃ left, left ≤ tokenCount ∧
    ∃ right, right ≤ tokenCount ∧
      CompactFixedWidthEntry stateBoundary tokenCount index left ∧
      CompactFixedWidthEntry stateBoundary tokenCount (index + 1) right ∧
      ∃ coordinates sizeWitness,
        coordinates.start = left ∧
        coordinates.finish = right ∧
        compactUnifiedParserStateCoreGraphDef.val.Evalb
          (compactUnifiedParserStateCoreFormulaEnvironmentOf
            tokenTable width tokenCount coordinates sizeWitness) ∧
        CompactBinaryNatStreamStatusDirectLayout
          tokenTable width tokenCount coordinates.tasksFinish
            coordinates.finish (states.getI index).2.2

theorem compactUnifiedParserStateListCoreFormulaRows_of_layouts
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states) :
    CompactUnifiedParserStateListCoreFormulaRows
      tokenTable width tokenCount stateBoundary states := by
  intro index hindex
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases CompactUnifiedParserStateDirectLayout.toCoreGraph hlayout with
    ⟨coordinates, sizeWitness, hstart, hfinish, hgraph, hstatus⟩
  refine ⟨left, hleft, right, hright,
    hleftEntry, hrightEntry,
    coordinates, sizeWitness, hstart, hfinish, ?_, hstatus⟩
  exact
    (compactUnifiedParserStateCoreGraphDef_environmentOf_iff
      tokenTable width tokenCount coordinates sizeWitness).2 hgraph

theorem compactNumericListedDirectTrace_parser_state_core_formulas
    (trace : CompactNumericListedDirectTrace) :
    let components := compactNumericListedDirectTraceComponentTokens trace
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let boundaries := compactAdditiveComponentBoundaries components
    ∃ proofBoundaryTable certificateBoundaryTable formulaBoundaryTable,
      CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 4) (boundaries.getI 5)
          proofBoundaryTable
          (compactNumericDirectTraceProofParserTrace trace) ∧
        CompactUnifiedParserStateListCoreFormulaRows
          (compactFixedWidthTableCode width tokens)
          width tokens.length proofBoundaryTable
          (compactNumericDirectTraceProofParserTrace trace) ∧
        CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 5) (boundaries.getI 6)
          certificateBoundaryTable
          (compactNumericDirectTraceCertificateParserTrace trace) ∧
        CompactUnifiedParserStateListCoreFormulaRows
          (compactFixedWidthTableCode width tokens)
          width tokens.length certificateBoundaryTable
          (compactNumericDirectTraceCertificateParserTrace trace) ∧
        CompactUnifiedParserStateListComponentLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length (boundaries.getI 6) (boundaries.getI 7)
          formulaBoundaryTable
          (compactNumericDirectTraceFormulaParserTrace trace) ∧
        CompactUnifiedParserStateListCoreFormulaRows
          (compactFixedWidthTableCode width tokens)
          width tokens.length formulaBoundaryTable
          (compactNumericDirectTraceFormulaParserTrace trace) := by
  let components := compactNumericListedDirectTraceComponentTokens trace
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let boundaries := compactAdditiveComponentBoundaries components
  rcases compactNumericListedDirectTrace_parser_state_layouts trace with
    ⟨proofBoundaryTable, certificateBoundaryTable, formulaBoundaryTable,
      hproof, hcertificate, hformula⟩
  have hproofCore :=
    compactUnifiedParserStateListCoreFormulaRows_of_layouts hproof.2.1
  have hcertificateCore :=
    compactUnifiedParserStateListCoreFormulaRows_of_layouts
      hcertificate.2.1
  have hformulaCore :=
    compactUnifiedParserStateListCoreFormulaRows_of_layouts hformula.2.1
  exact ⟨proofBoundaryTable, certificateBoundaryTable,
    formulaBoundaryTable,
    hproof, hproofCore,
    hcertificate, hcertificateCore,
    hformula, hformulaCore⟩

#print axioms compactUnifiedParserStateListCoreFormulaRows_of_layouts
#print axioms compactNumericListedDirectTrace_parser_state_core_formulas

end FoundationCompactNumericListedDirectParserStateFormulaInstallation

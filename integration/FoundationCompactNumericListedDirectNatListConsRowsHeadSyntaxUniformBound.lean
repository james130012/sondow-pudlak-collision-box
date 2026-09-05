import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-! # Uniform syntax bound for the natural-list cons head terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadTerminalUniformBound

def natListConsHeadTermCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (consHeadNumeralTerm 0)).length +
    (binaryTermCode (consHeadNumeralTerm 1)).length + 1

def natListConsHeadTerminalImageCodeEnvelope (termCodeBound : Nat) : Nat :=
  5 * termCodeBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length + 1

def natListConsHeadTerminalBodyCodeEnvelope (bitBound : Nat) : Nat :=
  let imageBound := natListConsHeadTerminalImageCodeEnvelope
    (natListConsHeadTermCodeEnvelope bitBound)
  let entryCode := uniformRewritingFormulaCodeEnvelope imageBound
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length
  let cellCode := uniformRewritingFormulaCodeEnvelope imageBound
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)).length
  2 * entryCode + cellCode + 2 * (binaryNatCode 4).length + 1

private theorem shortNumeralTerm_code_le_consHeadEnvelope
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      natListConsHeadTermCodeEnvelope bitBound := by
  exact (binaryNumeralTerm_code_length_le_envelope value bitBound hsize).trans
    (by
      unfold natListConsHeadTermCodeEnvelope
      omega)

private theorem zeroTerm_code_le_consHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (consHeadNumeralTerm 0)).length <=
      natListConsHeadTermCodeEnvelope bitBound := by
  unfold natListConsHeadTermCodeEnvelope
  omega

private theorem oneTerm_code_le_consHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (consHeadNumeralTerm 1)).length <=
      natListConsHeadTermCodeEnvelope bitBound := by
  unfold natListConsHeadTermCodeEnvelope
  omega

private theorem closedShift_two_code_length_le_consHead
    (term : ValuationTerm) (termCodeBound : Nat)
    (hterm : (binaryTermCode term).length <= termCodeBound) :
    (binaryTermCode (closedShift 2 term)).length <= 5 * termCodeBound := by
  have hsymbols : termSymbolCount term <= termCodeBound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst :
      (binaryTermCode (Rew.bShift term)).length <= 3 * termCodeBound := by
    omega
  have hshiftedSymbols :
      termSymbolCount (Rew.bShift term) <= termCodeBound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  change
    (binaryTermCode (Rew.bShift (Rew.bShift term))).length <=
      5 * termCodeBound
  omega

theorem compactAdditiveNatListConsRowsHeadTerminal_code_length_le_uniform
    (tokenTable width tokenCount targetBoundary head bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadSize : Nat.size head <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
        targetBoundary head)).length <=
      natListConsHeadTerminalBodyCodeEnvelope bitBound := by
  let termCodeBound := natListConsHeadTermCodeEnvelope bitBound
  let imageBound := natListConsHeadTerminalImageCodeEnvelope termCodeBound
  have htable := shortNumeralTerm_code_le_consHeadEnvelope tokenTable bitBound
    htableSize
  have hwidth := shortNumeralTerm_code_le_consHeadEnvelope width bitBound
    hwidthSize
  have htokenCount := shortNumeralTerm_code_le_consHeadEnvelope tokenCount
    bitBound htokenCountSize
  have htargetBoundary := shortNumeralTerm_code_le_consHeadEnvelope
    targetBoundary bitBound htargetBoundarySize
  have hhead := shortNumeralTerm_code_le_consHeadEnvelope head bitBound hheadSize
  have hzero := zeroTerm_code_le_consHeadEnvelope bitBound
  have hone := oneTerm_code_le_consHeadEnvelope bitBound
  have himageShift (term : ValuationTerm)
      (hterm : (binaryTermCode term).length <= termCodeBound) :
      (binaryTermCode (closedShift 2 term)).length <= imageBound := by
    exact (closedShift_two_code_length_le_consHead term termCodeBound hterm).trans
      (by
        unfold imageBound natListConsHeadTerminalImageCodeEnvelope
        omega)
  have himageBvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length <=
        imageBound := by
    unfold imageBound natListConsHeadTerminalImageCodeEnvelope
    omega
  have himageBvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length <=
        imageBound := by
    unfold imageBound natListConsHeadTerminalImageCodeEnvelope
    omega
  let formula1 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 0),
        (#1 : ArithmeticSemiterm Nat 2)]
  let formula2 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 1),
        (#0 : ArithmeticSemiterm Nat 2)]
  let formula3 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2),
        closedShift 2 (shortBinaryNumeralTerm head),
        (#0 : ArithmeticSemiterm Nat 2)]
  have hformula1 :
      (binaryFormulaCode formula1).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactFixedWidthEntryDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 4 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 0),
        (#1 : ArithmeticSemiterm Nat 2)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htargetBoundary
        · exact himageShift _ htokenCount
        · exact himageShift _ hzero
        · exact himageBvar1
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
    simpa only [formula1, rewriting] using hraw
  have hformula2 :
      (binaryFormulaCode formula2).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactFixedWidthEntryDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 4 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 1),
        (#0 : ArithmeticSemiterm Nat 2)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htargetBoundary
        · exact himageShift _ htokenCount
        · exact himageShift _ hone
        · exact himageBvar0
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
    simpa only [formula2, rewriting] using hraw
  have hformula3 :
      (binaryFormulaCode formula3).length <=
        uniformRewritingFormulaCodeEnvelope imageBound
          (binaryFormulaCode
            (Rewriting.emb (ξ := Nat)
              compactAdditiveTokenCellDef.val)).length := by
    let rewriting : Rew ℒₒᵣ Nat 6 Nat 2 := Rew.subst
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2),
        closedShift 2 (shortBinaryNumeralTerm head),
        (#0 : ArithmeticSemiterm Nat 2)]
    have hrewriting : RewritingImageCodeBound rewriting imageBound := by
      constructor
      · intro coordinate
        dsimp only [rewriting]
        rw [Rew.subst_bvar]
        fin_cases coordinate
        · exact himageShift _ htable
        · exact himageShift _ hwidth
        · exact himageShift _ htokenCount
        · exact himageBvar1
        · exact himageShift _ hhead
        · exact himageBvar0
      · intro coordinate
        dsimp only [rewriting]
        simp
    have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
      imageBound hrewriting
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)
    simpa only [formula3, rewriting] using hraw
  have hinner :
      (binaryFormulaCode (formula2 ⋏ formula3)).length <=
        (binaryFormulaCode formula2).length +
          (binaryFormulaCode formula3).length +
          (binaryNatCode 4).length := by
    simp [binaryFormulaCode]
    omega
  have houter :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        (binaryFormulaCode formula1).length +
          (binaryFormulaCode (formula2 ⋏ formula3)).length +
          (binaryNatCode 4).length := by
    simp [binaryFormulaCode]
    omega
  change
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <= _
  dsimp only [imageBound, termCodeBound] at hformula1 hformula2 hformula3
  simp only [natListConsHeadTerminalBodyCodeEnvelope]
  omega

theorem compactAdditiveNatListConsRowsHeadTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary head : Nat) :
    (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
      targetBoundary head).freeVariables = ∅ := by
  have hshift (term : ValuationTerm)
      (hterm : term.freeVariables = ∅) :
      (closedShift 2 term).freeVariables = ∅ := by
    unfold closedShift
    exact bShift_freeVariables_eq_empty_of_empty _
      (bShift_freeVariables_eq_empty_of_empty _ hterm)
  let formula1 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 0),
        (#1 : ArithmeticSemiterm Nat 2)]
  let formula2 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (consHeadNumeralTerm 1),
        (#0 : ArithmeticSemiterm Nat 2)]
  let formula3 : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
        closedShift 2 (shortBinaryNumeralTerm width),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        (#1 : ArithmeticSemiterm Nat 2),
        closedShift 2 (shortBinaryNumeralTerm head),
        (#0 : ArithmeticSemiterm Nat 2)]
  change (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and]
  have hformula1 : formula1.freeVariables = ∅ := by
    dsimp only [formula1]
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (consHeadNumeralTerm_freeVariables_eq_empty 0)
    · simp
  have hformula2 : formula2.freeVariables = ∅ := by
    dsimp only [formula2]
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (consHeadNumeralTerm_freeVariables_eq_empty 1)
    · simp
  have hformula3 : formula3.freeVariables = ∅ := by
    dsimp only [formula3]
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · simp
    · exact hshift _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    · simp
  rw [hformula1, hformula2, hformula3]
  simp

#print axioms compactAdditiveNatListConsRowsHeadTerminal_code_length_le_uniform
#print axioms compactAdditiveNatListConsRowsHeadTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound

import integration.FoundationCompactNumericListedDirectSequentFormulaStepFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

/-!
# Closed direct syntax for one sequent-formula step

The original twenty-six-coordinate formula is closed by short public
numerals.  Its twenty-one right-nested conjuncts retain every original
composite arithmetic term.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    apply Rew.ext
    · intro coordinate
      simp [Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

def compactSequentFormulaStepDirectPublicTerms
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    Fin 26 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm suffixBoundary,
    shortBinaryNumeralTerm suffixCount,
    shortBinaryNumeralTerm valueBoundary,
    shortBinaryNumeralTerm valueCount,
    shortBinaryNumeralTerm index,
    shortBinaryNumeralTerm row.current.start,
    shortBinaryNumeralTerm row.current.finish,
    shortBinaryNumeralTerm row.current.boundary,
    shortBinaryNumeralTerm row.current.count,
    shortBinaryNumeralTerm row.current.boundarySize,
    shortBinaryNumeralTerm row.next.start,
    shortBinaryNumeralTerm row.next.finish,
    shortBinaryNumeralTerm row.next.boundary,
    shortBinaryNumeralTerm row.next.count,
    shortBinaryNumeralTerm row.next.boundarySize,
    shortBinaryNumeralTerm row.value.start,
    shortBinaryNumeralTerm row.value.finish,
    shortBinaryNumeralTerm row.value.boundary,
    shortBinaryNumeralTerm row.value.count,
    shortBinaryNumeralTerm row.value.boundarySize,
    shortBinaryNumeralTerm row.parserStateBoundary,
    shortBinaryNumeralTerm row.parserTableWidth,
    shortBinaryNumeralTerm row.parserValueBound]

def compactSequentFormulaStepDirectClosedFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactSequentFormulaStepDef.val) ⇜
    compactSequentFormulaStepDirectPublicTerms tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row

def compactSequentFormulaStepIndexSuccessorTerm
    (index : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm index) + 1’

def compactSequentFormulaStepIndexSecondSuccessorTerm
    (index : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm index) + 2’

def compactSequentFormulaStepParserPublicTerms
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    (‘!!(FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuelTerm
          inputCount) + 1’ : ValuationTerm),
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    (‘1’ : ValuationTerm),
    (‘0’ : ValuationTerm),
    (‘0’ : ValuationTerm),
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactSequentFormulaStepParserClosedFormula
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      FoundationCompactNumericListedDirectParserSyntaxExactFormula.compactParserSyntaxExactBoundedGraphDef.val) ⇜
    compactSequentFormulaStepParserPublicTerms tokenTable width tokenCount
      stateBoundary inputBoundary inputCount expectedBoundary expectedCount
      tableWidth valueBound

def compactSequentFormulaStepDirectPartsFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm row.current.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.current.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.current.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.next.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (“!!(shortBinaryNumeralTerm row.value.count) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm index)
      (shortBinaryNumeralTerm row.current.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTerm index)
      (shortBinaryNumeralTerm row.current.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTerm index)
      (shortBinaryNumeralTerm row.next.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSecondSuccessorTerm index)
      (shortBinaryNumeralTerm row.next.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm index)
      (shortBinaryNumeralTerm row.value.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTerm index)
      (shortBinaryNumeralTerm row.value.finish) ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.next.start row.next.count row.next.finish row.next.boundary
      row.next.boundarySize ⋏
  (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.value.start row.value.count row.value.finish row.value.boundary
      row.value.boundarySize ⋏
  (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
      row.parserStateBoundary row.current.boundary
      row.current.count row.next.boundary row.next.count
      row.parserTableWidth row.parserValueBound ⋏
  (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count
      row.current.start row.current.finish row.current.count ⋏
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”)))))))))))))))))))

theorem compactSequentFormulaStepDirectClosedFormula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row =
      compactSequentFormulaStepDirectPartsFormula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row := by
  simp [compactSequentFormulaStepDirectClosedFormula,
    compactSequentFormulaStepDirectPublicTerms,
    compactSequentFormulaStepDirectPartsFormula,
    compactSequentFormulaStepDef,
    compactSequentFormulaStepIndexSuccessorTerm,
    compactSequentFormulaStepIndexSecondSuccessorTerm,
    compactFixedWidthEntryAtValuationFormula,
    compactAdditiveNatListWitnessRowsClosedFormula,
    compactSequentFormulaStepParserClosedFormula,
    compactSequentFormulaStepParserPublicTerms,
    compactAdditiveNatListAppendSlicesClosedFormula,
    rewriting_embeddedFormulaSubstitution,
    FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuelTerm,
    FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactNativeNumeralTerm,
    Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [compactSequentFormulaStepIndexSuccessorTerm,
        compactSequentFormulaStepIndexSecondSuccessorTerm,
        FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuelTerm,
        FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactNativeNumeralTerm,
        Rew.comp_app, Rew.subst_bvar]

#print axioms compactSequentFormulaStepDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

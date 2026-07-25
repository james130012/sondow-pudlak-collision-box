import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate

theorem compactUnifiedParserSyntaxRepeatClosedFormula_environment_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next binderArity repeatCount witness =
      (Rew.subst (fun coordinate =>
        shortBinaryNumeralTerm
          (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable
            width tokenCount current next binderArity repeatCount witness
            coordinate))) ▹
        (Rewriting.emb (ξ := Nat)
          compactUnifiedParserSyntaxRepeatRowsDef.val) := by
  unfold compactUnifiedParserSyntaxRepeatClosedFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf,
      compactUnifiedParserSyntaxRepeatFormulaEnvironment]

theorem compactUnifiedParserSyntaxRepeatClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
      current next binderArity repeatCount witness).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxRepeatClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

end FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment

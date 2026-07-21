import integration.FoundationCompactPAValuationTermCompiler
import integration.FoundationCompactPAUnaryAtomicTransport
import integration.FoundationCompactPAClosedAtomicCompiler

/-!
# PA atomic-formula compiler under a concrete valuation

True positive and negative arithmetic atoms are first proved on short binary
numerals.  Explicit contextual term equalities then transport those proofs to
the original terms.  Negative atoms use the reverse transport implication and
contextual modus tollens.  The compiler accepts semantic truth only; no proof
or proof-length premise is part of its input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationAtomicCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAValuationTermCompiler

def formulaValue
    (valuation : Nat -> Nat)
    (formula : ValuationFormula) : Prop :=
  LO.FirstOrder.Semiformula.Eval ![] valuation formula

theorem termFreeVariables_subset_relation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (index : Fin 2) :
    (args index).freeVariables ⊆
      (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables := by
  intro candidate hcandidate
  simp only [LO.FirstOrder.Semiformula.freeVariables_rel]
  exact Finset.mem_biUnion.mpr
    ⟨index, Finset.mem_univ index, hcandidate⟩

theorem termFreeVariables_subset_negatedRelation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (index : Fin 2) :
    (args index).freeVariables ⊆
      (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables := by
  intro candidate hcandidate
  simp only [LO.FirstOrder.Semiformula.freeVariables_nrel]
  exact Finset.mem_biUnion.mpr
    ⟨index, Finset.mem_univ index, hcandidate⟩

theorem binaryRelationFormula_eq_relation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) :
    binaryRelationFormula relationSymbol (args 0) (args 1) =
      LO.FirstOrder.Semiformula.rel relationSymbol args := by
  unfold binaryRelationFormula
  congr 1
  exact (Matrix.fun_eq_vec_two args).symm

theorem binaryRelationFormula_eq_formula
    (left right : ValuationTerm) :
    binaryRelationFormula Language.Eq.eq left right =
      (“!!left = !!right” : ValuationFormula) := by
  simp [binaryRelationFormula, Semiformula.Operator.eq_def,
    Matrix.fun_eq_vec_two]

theorem negatedBinaryRelationFormula_eq_negatedRelation
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) :
    ∼binaryRelationFormula relationSymbol (args 0) (args 1) =
      LO.FirstOrder.Semiformula.nrel relationSymbol args := by
  rw [binaryRelationFormula_eq_relation]
  rw [LO.FirstOrder.Semiformula.neg_rel]

noncomputable def compilePositiveRelation
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.rel relationSymbol args)) :
    CertifiedPAContextProof
      (valuationContext
        (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
        valuation)
      (LO.FirstOrder.Semiformula.rel relationSymbol args) := by
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
    valuation
  let firstRaw := compileTermValueEquality valuation (args 0)
  let secondRaw := compileTermValueEquality valuation (args 1)
  have hfirstVariables : (args 0).freeVariables ⊆
      (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables :=
    termFreeVariables_subset_relation relationSymbol args 0
  have hsecondVariables : (args 1).freeVariables ⊆
      (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables :=
    termFreeVariables_subset_relation relationSymbol args 1
  let firstEquality := CertifiedPAContextProof.weakenContext firstRaw
    (valuationContext_mono valuation hfirstVariables)
  let secondEquality := CertifiedPAContextProof.weakenContext secondRaw
    (valuationContext_mono valuation hsecondVariables)
  let sourceProof : CertifiedPAProof
      (binaryRelationFormula relationSymbol
        (shortBinaryNumeralTerm (termValue valuation (args 0)))
        (shortBinaryNumeralTerm (termValue valuation (args 1)))) := by
    cases relationSymbol with
    | eq =>
        have hvalue : termValue valuation (args 0) =
            termValue valuation (args 1) := by
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.equality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_eq_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
    | lt =>
        have hvalue : termValue valuation (args 0) <
            termValue valuation (args 1) := by
          change (LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.lessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact (binaryRelationFormula_lt_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
  let contextualSource := CertifiedPAContextProof.weakenCertified Gamma
    sourceProof
  let transport := relationTransportImplicationFromEqualities relationSymbol
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    (args 0) (args 1) firstEquality secondEquality
  let result := CertifiedPAContextProof.modusPonens transport contextualSource
  exact CertifiedPAContextProof.cast
    (binaryRelationFormula_eq_relation relationSymbol args) result

noncomputable def compileNegativeRelation
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (htruth : formulaValue valuation
      (LO.FirstOrder.Semiformula.nrel relationSymbol args)) :
    CertifiedPAContextProof
      (valuationContext
        (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
        valuation)
      (LO.FirstOrder.Semiformula.nrel relationSymbol args) := by
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
    valuation
  let firstForwardRaw := compileTermValueEquality valuation (args 0)
  let secondForwardRaw := compileTermValueEquality valuation (args 1)
  have hfirstVariables : (args 0).freeVariables ⊆
      (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables :=
    termFreeVariables_subset_negatedRelation relationSymbol args 0
  have hsecondVariables : (args 1).freeVariables ⊆
      (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables :=
    termFreeVariables_subset_negatedRelation relationSymbol args 1
  let firstForward := CertifiedPAContextProof.weakenContext firstForwardRaw
    (valuationContext_mono valuation hfirstVariables)
  let secondForward := CertifiedPAContextProof.weakenContext secondForwardRaw
    (valuationContext_mono valuation hsecondVariables)
  let firstBackward := CertifiedPAContextProof.equalitySymmetry
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (args 0) firstForward
  let secondBackward := CertifiedPAContextProof.equalitySymmetry
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    (args 1) secondForward
  let sourceProof : CertifiedPAProof
      (∼binaryRelationFormula relationSymbol
        (shortBinaryNumeralTerm (termValue valuation (args 0)))
        (shortBinaryNumeralTerm (termValue valuation (args 1)))) := by
    cases relationSymbol with
    | eq =>
        have hvalue : termValue valuation (args 0) ≠
            termValue valuation (args 1) := by
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.eq
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.disequality
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.Eq.eq
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_eq_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
    | lt =>
        have hvalue : ¬termValue valuation (args 0) <
            termValue valuation (args 1) := by
          change ¬(LO.FirstOrder.Arithmetic.standardModel Nat).rel
            Language.ORing.Rel.lt
            (fun index => LO.FirstOrder.Semiterm.val
              ![] valuation (args index)) at htruth
          exact htruth
        let literal := ClosedPAAtomicLiteral.notLessThan
          (.numeral (termValue valuation (args 0)))
          (.numeral (termValue valuation (args 1)))
        let raw := literal.compile hvalue
        have hformula : literal.formula =
            ∼binaryRelationFormula Language.ORing.Rel.lt
              (shortBinaryNumeralTerm (termValue valuation (args 0)))
              (shortBinaryNumeralTerm (termValue valuation (args 1))) := by
          dsimp only [literal, ClosedPAAtomicLiteral.formula,
            ClosedPATerm.term]
          exact congrArg (fun formula : ValuationFormula => ∼formula)
            (binaryRelationFormula_lt_formula _ _).symm
        exact CertifiedPAProof.cast hformula raw
  let contextualSource := CertifiedPAContextProof.weakenCertified Gamma
    sourceProof
  let reverseTransport := relationTransportImplicationFromEqualities
    relationSymbol (args 0) (args 1)
    (shortBinaryNumeralTerm (termValue valuation (args 0)))
    (shortBinaryNumeralTerm (termValue valuation (args 1)))
    firstBackward secondBackward
  let result := CertifiedPAContextProof.modusTollens
    reverseTransport contextualSource
  exact CertifiedPAContextProof.cast
    (negatedBinaryRelationFormula_eq_negatedRelation relationSymbol args)
    result

#print axioms compilePositiveRelation
#print axioms compileNegativeRelation

end FoundationCompactPAValuationAtomicCompiler

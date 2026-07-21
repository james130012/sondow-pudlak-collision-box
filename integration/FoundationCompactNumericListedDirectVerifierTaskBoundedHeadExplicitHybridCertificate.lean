import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskBoundedHeadExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simpa using
    (LO.FirstOrder.Structure.numeral_eq_numeral
      (L := ℒₒᵣ) (M := Nat) value)

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
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
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

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

/-- The bounded task head with every free numeric field closed by a short numeral. -/
def compactNumericVerifierTaskBoundedHeadClosedFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedHeadDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm taskBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tag,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaBoundary,
      shortBinaryNumeralTerm coordinates.firstFinish,
      shortBinaryNumeralTerm coordinates.firstCount,
      shortBinaryNumeralTerm coordinates.secondFinish,
      shortBinaryNumeralTerm coordinates.secondCount,
      shortBinaryNumeralTerm coordinates.witnessFinish,
      shortBinaryNumeralTerm coordinates.witnessCount,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm sizeWitness.gammaBoundarySize]

private def compactNumericVerifierTaskBoundedHeadPartsFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  [“!!(shortBinaryNumeralTerm coordinates.start) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.finish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.tag) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaBoundary) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.firstFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.firstCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.secondFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.secondCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.witnessFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.witnessCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.suffixCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm sizeWitness.gammaBoundarySize) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm taskBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm coordinates.start),
    compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm taskBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 1)
      (shortBinaryNumeralTerm coordinates.finish),
    compactNumericVerifierTaskCoreClosedFormula
      tokenTable width tokenCount coordinates sizeWitness].conj₂

/-- Exact syntactic alignment of the closed head with its seventeen conjuncts. -/
theorem compactNumericVerifierTaskBoundedHeadClosedFormula_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierTaskBoundedHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness =
      compactNumericVerifierTaskBoundedHeadPartsFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  unfold compactNumericVerifierTaskBoundedHeadClosedFormula
  unfold compactNumericVerifierTaskBoundedHeadPartsFormula
  unfold compactNumericVerifierTaskBoundedHeadDef
  simp [Rew.comp_app, compactFixedWidthEntryAtValuationFormula,
    compactNumericVerifierTaskCoreClosedFormula,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          unaryNumeralTerm]
    · intro coordinate
      exact Empty.elim coordinate

/-- Build the explicit head certificate from the bounded head data. -/
noncomputable def compactNumericVerifierTaskBoundedHeadExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness) :
    HybridCertificate
      (compactNumericVerifierTaskBoundedHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness) := by
  rcases hhead with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCountBound,
      hgammaBoundary, hfirstFinish, hfirstCountBound,
      hsecondFinish, hsecondCountBound, hwitnessFinish,
      hwitnessCountBound, hsuffixCountBound, hsizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLeCertificate coordinates.start valueBound hstart)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLeCertificate coordinates.finish valueBound hfinish)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (closedLeCertificate coordinates.tag valueBound htag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (closedLeCertificate coordinates.gammaFinish valueBound hgammaFinish)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedLeCertificate coordinates.gammaCount valueBound
              hgammaCountBound)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (closedLeCertificate coordinates.gammaBoundary valueBound
                hgammaBoundary)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (closedLeCertificate coordinates.firstFinish valueBound
                  hfirstFinish)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (closedLeCertificate coordinates.firstCount valueBound
                    hfirstCountBound)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (closedLeCertificate coordinates.secondFinish valueBound
                      hsecondFinish)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (closedLeCertificate coordinates.secondCount valueBound
                        hsecondCountBound)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (closedLeCertificate coordinates.witnessFinish valueBound
                          hwitnessFinish)
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (closedLeCertificate coordinates.witnessCount valueBound
                            hwitnessCountBound)
                          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                            (closedLeCertificate coordinates.suffixCount valueBound
                              hsuffixCountBound)
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (closedLeCertificate
                                sizeWitness.gammaBoundarySize valueBound hsizeBound)
                              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                                  zeroValuation
                                  (shortBinaryNumeralTerm taskBoundary)
                                  (shortBinaryNumeralTerm tokenCount)
                                  (unaryNumeralTerm 0)
                                  (shortBinaryNumeralTerm coordinates.start) (by
                                    simpa only [termValue_shortBinaryNumeralTerm,
                                      termValue_unaryNumeralTerm]
                                      using hstartEntry))
                                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                  (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                                    zeroValuation
                                    (shortBinaryNumeralTerm taskBoundary)
                                    (shortBinaryNumeralTerm tokenCount)
                                    (unaryNumeralTerm 1)
                                    (shortBinaryNumeralTerm coordinates.finish) (by
                                      simpa only [termValue_shortBinaryNumeralTerm,
                                        termValue_unaryNumeralTerm]
                                        using hfinishEntry))
                                  (compactNumericVerifierTaskCoreExplicitHybridCertificate
                                    hcore))))))))))))))))
  exact .cast
    (compactNumericVerifierTaskBoundedHeadClosedFormula_alignment
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness).symm parts

#print axioms compactNumericVerifierTaskBoundedHeadClosedFormula
#print axioms compactNumericVerifierTaskBoundedHeadClosedFormula_alignment
#print axioms compactNumericVerifierTaskBoundedHeadExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierTaskBoundedHeadExplicitHybridCertificate

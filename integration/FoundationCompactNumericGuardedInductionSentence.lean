import integration.FoundationCompactNumericTokenBitLength
import integration.FoundationCompactNumericSuccIndSentence

/-!
# Pure numeric guarded induction-sentence construction

The guard computes the candidate's real canonical binary bit length. It runs
`fixitr` and iterated universal closure only when the exact free-variable
supremum of `succInd(body)` is no larger than that bit length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericGuardedInductionSentence

open FoundationCompactSyntaxTokenMachine
open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaFixitr
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericAllClosure
open FoundationCompactNumericTokenBitLength
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactPAAxiomCertificate

def compactFixedAllClosureTokens
    (depthAndFormula : Nat × List Nat) : Option (List Nat) :=
  (compactFormulaFixitrExact 0
      (depthAndFormula.1, depthAndFormula.2)).map
    fun fixed => compactAllClosureTokens depthAndFormula.1 fixed

theorem compactFixedAllClosureTokens_primrec :
    Primrec compactFixedAllClosureTokens := by
  have hfixed : Primrec (fun input : Nat × List Nat =>
      compactFormulaFixitrExact 0 input) :=
    compactFormulaFixitrExact_primrec.comp
      (Primrec.const 0) Primrec.id
  have hclosure : Primrec₂
      (fun (input : Nat × List Nat) (fixed : List Nat) =>
        compactAllClosureTokens input.1 fixed) :=
    compactAllClosureTokens_primrec.comp₂
      ((Primrec.fst.comp Primrec.fst).to₂) Primrec₂.right
  exact
    (Primrec.option_map hfixed hclosure).of_eq fun input => by
      simp [compactFixedAllClosureTokens]

theorem compactFixedAllClosureTokens_canonical
    (depth : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    compactFixedAllClosureTokens
        (depth, compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens
        (∀⁰* (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) 0 depth) formula))) := by
  unfold compactFixedAllClosureTokens
  rw [compactFormulaFixitrExact_canonical]
  simp only [Option.map_some]
  congr 1
  simpa using compactAllClosureTokens_canonical
    (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 depth) formula)

def compactDepthResultWithFormula
    (formulaTokens : List Nat) (depthAndSuffix : Nat × List Nat) :
    Option (Nat × List Nat) :=
  if depthAndSuffix.2 = [] then
    some (depthAndSuffix.1, formulaTokens)
  else
    none

theorem compactDepthResultWithFormula_primrec :
    Primrec₂ compactDepthResultWithFormula := by
  apply Primrec₂.mk
  let Input := List Nat × (Nat × List Nat)
  have hempty : PrimrecPred (fun input : Input => input.2.2 = []) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
  have hpair : Primrec (fun input : Input =>
      (input.2.1, input.1)) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hsome : Primrec (fun input : Input =>
      some (input.2.1, input.1)) :=
    Primrec.option_some.comp hpair
  exact
    (Primrec.ite hempty hsome (Primrec.const none)).of_eq fun input => by
      simp [compactDepthResultWithFormula]

def compactInductionDepthAndFormulaTokens
    (bodyTokens : List Nat) : Option (Nat × List Nat) := do
  let generated <- compactSuccIndSentenceTokens bodyTokens
  let depthAndSuffix <- compactFormulaFvSupTokenTransform 0 generated
  compactDepthResultWithFormula generated depthAndSuffix

theorem compactInductionDepthAndFormulaTokens_primrec :
    Primrec compactInductionDepthAndFormulaTokens := by
  have hdepth : Primrec (fun state : List Nat × List Nat =>
      compactFormulaFvSupTokenTransform 0 state.2) :=
    compactFormulaFvSupTokenTransform_primrec.comp
      (Primrec.const 0) Primrec.snd
  have hresult : Primrec₂
      (fun (state : List Nat × List Nat)
          (depthAndSuffix : Nat × List Nat) =>
        compactDepthResultWithFormula state.2 depthAndSuffix) :=
    compactDepthResultWithFormula_primrec.comp₂
      ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
  have hdepthThenResult : Primrec₂
      (fun (bodyTokens : List Nat) (generated : List Nat) =>
        (compactFormulaFvSupTokenTransform 0 generated).bind
          fun depthAndSuffix =>
            compactDepthResultWithFormula generated depthAndSuffix) := by
    apply Primrec₂.mk
    exact Primrec.option_bind hdepth hresult
  exact
    (Primrec.option_bind compactSuccIndSentenceTokens_primrec
      hdepthThenResult).of_eq fun bodyTokens => by
        simp [compactInductionDepthAndFormulaTokens]

theorem compactInductionDepthAndFormulaTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactInductionDepthAndFormulaTokens
        (compactArithmeticFormulaTokens body) =
      some ((succInd body).fvSup,
        compactArithmeticFormulaTokens (succInd body)) := by
  rw [show compactInductionDepthAndFormulaTokens
      (compactArithmeticFormulaTokens body) =
      (compactSuccIndSentenceTokens
        (compactArithmeticFormulaTokens body)).bind fun generated =>
          (compactFormulaFvSupTokenTransform 0 generated).bind
            fun depthAndSuffix =>
              compactDepthResultWithFormula generated depthAndSuffix by
    rfl]
  rw [compactSuccIndSentenceTokens_canonical]
  simp only [Option.bind_some]
  rw [show compactFormulaFvSupTokenTransform 0
      (compactArithmeticFormulaTokens (succInd body)) =
      some ((succInd body).fvSup, []) by
    simpa using
      compactFormulaFvSupTokenTransform_canonical_append
        (succInd body) []]
  simp [compactDepthResultWithFormula]

def compactGuardedClosureFromDepth
    (candidateAndDepthFormula : List Nat × (Nat × List Nat)) :
    Option (List Nat) :=
  if candidateAndDepthFormula.2.1 <=
      compactTokenBitLength candidateAndDepthFormula.1 then
    compactFixedAllClosureTokens candidateAndDepthFormula.2
  else
    none

theorem compactGuardedClosureFromDepth_primrec :
    Primrec compactGuardedClosureFromDepth := by
  let Input := List Nat × (Nat × List Nat)
  have hdepth : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcandidateLength : Primrec (fun input : Input =>
      compactTokenBitLength input.1) :=
    compactTokenBitLength_primrec.comp Primrec.fst
  have hguard : PrimrecPred (fun input : Input =>
      input.2.1 <= compactTokenBitLength input.1) :=
    Primrec.nat_le.comp hdepth hcandidateLength
  have hclosure : Primrec (fun input : Input =>
      compactFixedAllClosureTokens input.2) :=
    compactFixedAllClosureTokens_primrec.comp Primrec.snd
  exact
    (Primrec.ite hguard hclosure (Primrec.const none)).of_eq fun input => by
      simp [compactGuardedClosureFromDepth]

def compactGuardedInductionSentenceTokens
    (bodyAndCandidate : List Nat × List Nat) : Option (List Nat) := do
  let depthAndFormula <-
    compactInductionDepthAndFormulaTokens bodyAndCandidate.1
  compactGuardedClosureFromDepth
    (bodyAndCandidate.2, depthAndFormula)

theorem compactGuardedInductionSentenceTokens_primrec :
    Primrec compactGuardedInductionSentenceTokens := by
  have hdepth : Primrec (fun input : List Nat × List Nat =>
      compactInductionDepthAndFormulaTokens input.1) :=
    compactInductionDepthAndFormulaTokens_primrec.comp Primrec.fst
  have hclosure : Primrec₂
      (fun (input : List Nat × List Nat)
          (depthAndFormula : Nat × List Nat) =>
        compactGuardedClosureFromDepth
          (input.2, depthAndFormula)) :=
    compactGuardedClosureFromDepth_primrec.comp₂
      (Primrec₂.pair.comp₂
        ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right)
  exact
    (Primrec.option_bind hdepth hclosure).of_eq fun input => by
      simp [compactGuardedInductionSentenceTokens]

def compactInductionClosureFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  ∀⁰* (Rewriting.app
    (Rew.fixitr (L := ℒₒᵣ) 0 (succInd body).fvSup) (succInd body))

theorem compactInductionClosureFormula_eq_sentence
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactInductionClosureFormula body =
      (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
        LO.FirstOrder.ArithmeticProposition) := by
  simp only [compactInductionClosureFormula,
    PAAxiomCertificate.sentence]
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl']

theorem compactGuardedInductionSentenceTokens_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactGuardedInductionSentenceTokens
        (compactArithmeticFormulaTokens body,
          compactArithmeticFormulaTokens
            (Rewriting.emb candidate :
              LO.FirstOrder.ArithmeticProposition)) =
      if (succInd body).fvSup <=
          (binaryFormulaCode
            (Rewriting.emb candidate :
              LO.FirstOrder.ArithmeticProposition)).length then
        some (compactArithmeticFormulaTokens
          (Rewriting.emb
            (PAAxiomCertificate.induction body).sentence :
              LO.FirstOrder.ArithmeticProposition))
      else
        none := by
  rw [show compactGuardedInductionSentenceTokens
      (compactArithmeticFormulaTokens body,
        compactArithmeticFormulaTokens
          (Rewriting.emb candidate :
            LO.FirstOrder.ArithmeticProposition)) =
      compactGuardedClosureFromDepth
        (compactArithmeticFormulaTokens
            (Rewriting.emb candidate :
              LO.FirstOrder.ArithmeticProposition),
          ((succInd body).fvSup,
            compactArithmeticFormulaTokens (succInd body))) by
    rw [compactGuardedInductionSentenceTokens]
    rw [compactInductionDepthAndFormulaTokens_canonical]
    rfl]
  unfold compactGuardedClosureFromDepth
  rw [compactTokenBitLength_formula_canonical]
  split <;> rename_i hguard
  · rw [compactFixedAllClosureTokens_canonical]
    change some (compactArithmeticFormulaTokens
      (compactInductionClosureFormula body)) = _
    rw [compactInductionClosureFormula_eq_sentence]
  · rfl

def compactGuardedInductionSentenceEq
    (bodyAndCandidate : List Nat × List Nat) : Bool :=
  match compactGuardedInductionSentenceTokens bodyAndCandidate with
  | none => false
  | some generated => tokenFormulaEq generated bodyAndCandidate.2

theorem compactGuardedInductionSentenceEq_primrec :
    Primrec compactGuardedInductionSentenceEq := by
  have hgenerated : Primrec (fun input : List Nat × List Nat =>
      compactGuardedInductionSentenceTokens input) :=
    compactGuardedInductionSentenceTokens_primrec
  have hsuccess : Primrec₂
      (fun (input : List Nat × List Nat) (generated : List Nat) =>
        tokenFormulaEq generated input.2) :=
    tokenFormulaEq_primrec.comp₂ Primrec₂.right
      ((Primrec.snd.comp Primrec.fst).to₂)
  exact
    (Primrec.option_casesOn hgenerated (Primrec.const false) hsuccess).of_eq
      fun input => by
        cases hresult : compactGuardedInductionSentenceTokens input <;>
          simp [compactGuardedInductionSentenceEq, hresult]

theorem compactGuardedInductionSentenceEq_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence) :
    compactGuardedInductionSentenceEq
        (compactArithmeticFormulaTokens body,
          compactArithmeticFormulaTokens
            (Rewriting.emb candidate :
              LO.FirstOrder.ArithmeticProposition)) = true ↔
      (PAAxiomCertificate.induction body).sentence = candidate := by
  unfold compactGuardedInductionSentenceEq
  rw [compactGuardedInductionSentenceTokens_canonical]
  by_cases hguard :
      (succInd body).fvSup <=
        (binaryFormulaCode
          (Rewriting.emb candidate :
            LO.FirstOrder.ArithmeticProposition)).length
  · simp only [if_pos hguard, tokenFormulaEq_eq_true_iff]
    change arithmeticPropositionTokenValue
          (Rewriting.emb (PAAxiomCertificate.induction body).sentence :
            LO.FirstOrder.ArithmeticProposition) =
        arithmeticPropositionTokenValue
          (Rewriting.emb candidate :
            LO.FirstOrder.ArithmeticProposition) ↔ _
    rw [arithmeticPropositionTokenValue_injective.eq_iff]
    exact Rewriting.emb_injective.eq_iff
  · have hsentence :
        (PAAxiomCertificate.induction body).sentence ≠ candidate := by
      intro hequality
      have htyped :=
        inductionSentenceGuardTrace_complete body candidate hequality
      have hle :=
        (inductionSentenceGuardTrace_result_eq_true_iff
          body candidate).1 htyped
      exact hguard (by
        simpa [candidateSentenceCodeLength] using hle)
    simp [hguard, hsentence]

#print axioms compactFixedAllClosureTokens_primrec
#print axioms compactInductionDepthAndFormulaTokens_primrec
#print axioms compactGuardedClosureFromDepth_primrec
#print axioms compactGuardedInductionSentenceTokens_primrec
#print axioms compactInductionClosureFormula_eq_sentence
#print axioms compactGuardedInductionSentenceTokens_canonical
#print axioms compactGuardedInductionSentenceEq_primrec
#print axioms compactGuardedInductionSentenceEq_canonical

end FoundationCompactNumericGuardedInductionSentence

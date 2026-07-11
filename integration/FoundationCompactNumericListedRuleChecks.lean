import integration.FoundationCompactNumericPAAxiomComparator
import integration.FoundationCompactNumericFormulaFree
import integration.FoundationCompactListedCertificateVerifier

/-!
# Pure numeric local checks for listed proof rules

Each function consumes only natural-token formula values, lists of such
values, child conclusions, and child Boolean results.  The recursive traversal
is deliberately left to a later stack machine; this module closes the local
rule combinators first.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedRuleChecks

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericFormulaFree
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactVerifierFormulaListChecks

abbrev CompactNumericFormulaValue := List Nat
abbrev CompactNumericSequentValue := List (List Nat)
abbrev CompactNumericChildResult := CompactNumericSequentValue × Bool

def compactFormulaFreeExact (tokens : List Nat) : Option (List Nat) :=
  compactExactFormulaTransformResult
    (compactFormulaFreeTokenTransform 1 tokens)

theorem compactFormulaFreeExact_primrec :
    Primrec compactFormulaFreeExact := by
  exact compactExactFormulaTransformResult_primrec.comp
    (compactFormulaFreeTokenTransform_primrec.comp
      (Primrec.const 1) Primrec.id)

@[simp] theorem compactFormulaFreeExact_canonical
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactFormulaFreeExact (compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens (Rewriting.free formula)) := by
  unfold compactFormulaFreeExact
  rw [show compactFormulaFreeTokenTransform 1
      (compactArithmeticFormulaTokens formula) =
      some (compactArithmeticFormulaTokens (Rewriting.free formula), []) by
    simpa using compactFormulaFreeTokenTransform_canonical_append
      formula []]
  rfl

def compactShiftedFormulaCons
    (formula : List Nat) (tail : Option (List (List Nat))) :
    Option (List (List Nat)) := do
  let shifted <- compactFormulaShiftExact 0 formula
  let shiftedTail <- tail
  some (shifted :: shiftedTail)

theorem compactShiftedFormulaCons_primrec :
    Primrec₂ compactShiftedFormulaCons := by
  apply Primrec₂.mk
  let Input := List Nat × Option (List (List Nat))
  have hshift : Primrec (fun input : Input =>
      compactFormulaShiftExact 0 input.1) :=
    compactFormulaShiftExact_primrec.comp
      (Primrec.const 0) Primrec.fst
  have htail : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hcons : Primrec₂
      (fun (input : Input) (shiftedAndTail : List Nat × List (List Nat)) =>
        some (shiftedAndTail.1 :: shiftedAndTail.2)) :=
    Primrec.option_some.comp₂
      (Primrec.list_cons.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.snd.comp₂ Primrec₂.right))
  have htailThenCons : Primrec₂
      (fun (input : Input) (shifted : List Nat) =>
        input.2.bind fun shiftedTail =>
          some (shifted :: shiftedTail)) := by
    apply Primrec₂.mk
    have hpair : Primrec₂
        (fun (state : Input × List Nat) (shiftedTail : List (List Nat)) =>
          (state.2, shiftedTail)) :=
      Primrec₂.pair.comp₂
        ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right
    have hsomeCons : Primrec₂
        (fun (state : Input × List Nat) (shiftedTail : List (List Nat)) =>
          some (state.2 :: shiftedTail)) :=
      Primrec.option_some.comp₂
        (Primrec.list_cons.comp₂
          ((Primrec.snd.comp Primrec.fst).to₂) Primrec₂.right)
    exact Primrec.option_bind
      (htail.comp Primrec.fst) hsomeCons
  exact
    (Primrec.option_bind hshift htailThenCons).of_eq fun input => by
      cases hshifted : compactFormulaShiftExact 0 input.1 <;>
        cases input.2 <;>
          simp [compactShiftedFormulaCons, hshifted]

def compactFormulaShiftExactList
    (formulas : List (List Nat)) : Option (List (List Nat)) :=
  formulas.foldr compactShiftedFormulaCons (some [])

theorem compactFormulaShiftExactList_primrec :
    Primrec compactFormulaShiftExactList := by
  let Input := List (List Nat)
  have hstep : Primrec₂
      (fun (_input : Input)
          (formulaAndTail : List Nat × Option (List (List Nat))) =>
        compactShiftedFormulaCons
          formulaAndTail.1 formulaAndTail.2) :=
    compactShiftedFormulaCons_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const (some []))
      hstep).of_eq fun formulas => by
        rfl

@[simp] theorem compactFormulaShiftExactList_canonical
    (formulas : List LO.FirstOrder.ArithmeticProposition) :
    compactFormulaShiftExactList
        (arithmeticPropositionTokenValues formulas) =
      some (arithmeticPropositionTokenValues
        (formulas.map Rewriting.shift)) := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      change compactShiftedFormulaCons
          (arithmeticPropositionTokenValue formula)
          (compactFormulaShiftExactList
            (arithmeticPropositionTokenValues formulas)) =
        some (arithmeticPropositionTokenValue (Rewriting.shift formula) ::
          arithmeticPropositionTokenValues
            (formulas.map Rewriting.shift))
      rw [ih]
      unfold compactShiftedFormulaCons
      rw [show compactFormulaShiftExact 0
          (arithmeticPropositionTokenValue formula) =
          some (arithmeticPropositionTokenValue
            (Rewriting.shift formula)) by
        simpa [arithmeticPropositionTokenValue] using
          compactFormulaShiftExact_canonical formula]
      rfl

/-! ## Leaf rules -/

def compactClosedRuleCheck
    (input : CompactNumericSequentValue × CompactNumericFormulaValue) :
    Bool :=
  match compactFormulaNegationExact 0 input.2 with
  | none => false
  | some negated =>
      tokenFormulaMem input.2 input.1 &&
        tokenFormulaMem negated input.1

theorem compactClosedRuleCheck_primrec :
    Primrec compactClosedRuleCheck := by
  let Input := CompactNumericSequentValue × CompactNumericFormulaValue
  have hnegated : Primrec (fun input : Input =>
      compactFormulaNegationExact 0 input.2) :=
    compactFormulaNegationExact_primrec.comp
      (Primrec.const 0) Primrec.snd
  have horiginalMem : Primrec₂
      (fun (input : Input) (_negated : CompactNumericFormulaValue) =>
        tokenFormulaMem input.2 input.1) :=
    tokenFormulaMem_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.left)
  have hnegatedMem : Primrec₂
      (fun (input : Input) (negated : CompactNumericFormulaValue) =>
        tokenFormulaMem negated input.1) :=
    tokenFormulaMem_primrec.comp₂ Primrec₂.right
      (Primrec.fst.comp₂ Primrec₂.left)
  have hsuccess : Primrec₂
      (fun (input : Input) (negated : CompactNumericFormulaValue) =>
        tokenFormulaMem input.2 input.1 &&
          tokenFormulaMem negated input.1) :=
    Primrec.and.comp₂ horiginalMem hnegatedMem
  exact
    (Primrec.option_casesOn hnegated (Primrec.const false) hsuccess).of_eq
      fun input => by
        cases hresult : compactFormulaNegationExact 0 input.2 <;>
          simp [compactClosedRuleCheck, hresult]

theorem compactClosedRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    compactClosedRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          arithmeticPropositionTokenValue formula) =
      (listedCertificateValidTrace (.closed Gamma formula) .leaf).1 := by
  unfold compactClosedRuleCheck
  rw [show compactFormulaNegationExact 0
      (arithmeticPropositionTokenValue formula) =
      some (arithmeticPropositionTokenValue (∼formula)) by
    simpa [arithmeticPropositionTokenValue] using
      compactFormulaNegationExact_canonical formula]
  simp only
  rw [tokenFormulaMem_canonical_eq_formulaMemTrace_result,
    tokenFormulaMem_canonical_eq_formulaMemTrace_result]
  rfl

abbrev CompactNumericAxmRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue × List Nat)

def compactAxmRuleCheck (input : CompactNumericAxmRuleInput) : Bool :=
  compactPAAxiomSentenceEqTokens (input.2.2, input.2.1) &&
    tokenFormulaMem input.2.1 input.1

theorem compactAxmRuleCheck_primrec : Primrec compactAxmRuleCheck := by
  let Input := CompactNumericAxmRuleInput
  have haxiom : Primrec (fun input : Input =>
      compactPAAxiomSentenceEqTokens (input.2.2, input.2.1)) :=
    compactPAAxiomSentenceEqTokens_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  have hmember : Primrec (fun input : Input =>
      tokenFormulaMem input.2.1 input.1) :=
    tokenFormulaMem_primrec.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst
  exact Primrec.and.comp haxiom hmember

theorem compactAxmRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (sentence : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    compactAxmRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (compactSentenceTokens sentence,
            compactPAAxiomCertificateTokens certificate)) =
      (listedCertificateValidTrace (.axm Gamma sentence)
        (.axiomCert certificate)).1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [compactAxmRuleCheck, Bool.and_eq_true]
  rw [compactPAAxiomSentenceEqTokens_canonical]
  rw [tokenFormulaMem_eq_true_iff]
  change certificate.sentence = sentence ∧
      arithmeticPropositionTokenValue
          (Rewriting.emb sentence :
            LO.FirstOrder.ArithmeticProposition) ∈
        arithmeticPropositionTokenValues Gamma ↔ _
  rw [mem_arithmeticPropositionTokenValues_iff]
  simp [listedCertificateValidTrace,
    guardedAxiomSentenceEqTrace_result_eq_true_iff,
    formulaMemTrace_result_eq_true_iff]

def compactVerumRuleCheck
    (Gamma : CompactNumericSequentValue) : Bool :=
  tokenFormulaMem tokenFormulaVerum Gamma

theorem compactVerumRuleCheck_primrec :
    Primrec compactVerumRuleCheck := by
  exact tokenFormulaMem_primrec.comp
    (Primrec.const tokenFormulaVerum) Primrec.id

theorem compactVerumRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition) :
    compactVerumRuleCheck (arithmeticPropositionTokenValues Gamma) =
      (listedCertificateValidTrace (.verum Gamma) .leaf).1 := by
  unfold compactVerumRuleCheck
  change tokenFormulaMem
      (arithmeticPropositionTokenValue
        (⊤ : LO.FirstOrder.ArithmeticProposition))
      (arithmeticPropositionTokenValues Gamma) = _
  simpa [listedCertificateValidTrace] using
    tokenFormulaMem_canonical_eq_formulaMemTrace_result
      (⊤ : LO.FirstOrder.ArithmeticProposition) Gamma

/-! ## Propositional recursive rules -/

abbrev CompactNumericAndRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue ×
      (CompactNumericFormulaValue ×
        (CompactNumericChildResult × CompactNumericChildResult)))

def compactAndRuleCheck (input : CompactNumericAndRuleInput) : Bool :=
  let Gamma := input.1
  let leftFormula := input.2.1
  let rightFormula := input.2.2.1
  let left := input.2.2.2.1
  let right := input.2.2.2.2
  tokenFormulaMem (tokenFormulaAnd leftFormula rightFormula) Gamma &&
    (tokenFormulaSetEq left.1 (leftFormula :: Gamma) &&
      (tokenFormulaSetEq right.1 (rightFormula :: Gamma) &&
        (left.2 && right.2)))

theorem compactAndRuleCheck_primrec : Primrec compactAndRuleCheck := by
  let Input := CompactNumericAndRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hleftFormula : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hrightFormula : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hchildren : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec (fun input : Input => input.2.2.2.1) :=
    Primrec.fst.comp hchildren
  have hright : Primrec (fun input : Input => input.2.2.2.2) :=
    Primrec.snd.comp hchildren
  have hleftConclusion : Primrec (fun input : Input => input.2.2.2.1.1) :=
    Primrec.fst.comp hleft
  have hrightConclusion : Primrec (fun input : Input => input.2.2.2.2.1) :=
    Primrec.fst.comp hright
  have hleftValid : Primrec (fun input : Input => input.2.2.2.1.2) :=
    Primrec.snd.comp hleft
  have hrightValid : Primrec (fun input : Input => input.2.2.2.2.2) :=
    Primrec.snd.comp hright
  have hprincipal : Primrec (fun input : Input =>
      tokenFormulaAnd input.2.1 input.2.2.1) :=
    tokenFormulaAnd_primrec.comp hleftFormula hrightFormula
  have hmember : Primrec (fun input : Input =>
      tokenFormulaMem
        (tokenFormulaAnd input.2.1 input.2.2.1) input.1) :=
    tokenFormulaMem_primrec.comp hprincipal hGamma
  have hleftExpected : Primrec (fun input : Input =>
      input.2.1 :: input.1) :=
    Primrec.list_cons.comp hleftFormula hGamma
  have hrightExpected : Primrec (fun input : Input =>
      input.2.2.1 :: input.1) :=
    Primrec.list_cons.comp hrightFormula hGamma
  have hleftEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1.1 (input.2.1 :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hleftConclusion hleftExpected
  have hrightEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.2.1
        (input.2.2.1 :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hrightConclusion hrightExpected
  have hchildrenValid : Primrec (fun input : Input =>
      input.2.2.2.1.2 && input.2.2.2.2.2) :=
    Primrec.and.comp hleftValid hrightValid
  have hrightTail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.2.1
          (input.2.2.1 :: input.1) &&
        (input.2.2.2.1.2 && input.2.2.2.2.2)) :=
    Primrec.and.comp hrightEq hchildrenValid
  have hleftTail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1.1 (input.2.1 :: input.1) &&
        (tokenFormulaSetEq input.2.2.2.2.1
            (input.2.2.1 :: input.1) &&
          (input.2.2.2.1.2 && input.2.2.2.2.2))) :=
    Primrec.and.comp hleftEq hrightTail
  exact (Primrec.and.comp hmember hleftTail).of_eq fun input => by
    rfl

theorem compactAndRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    compactAndRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (arithmeticPropositionTokenValue leftFormula,
            (arithmeticPropositionTokenValue rightFormula,
              ((arithmeticPropositionTokenValues left.conclusionList,
                  (listedCertificateValidTrace
                    left leftCertificate).1),
                (arithmeticPropositionTokenValues right.conclusionList,
                  (listedCertificateValidTrace
                    right rightCertificate).1))))) =
      (listedCertificateValidTrace
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)).1 := by
  simp only [compactAndRuleCheck]
  change
    (tokenFormulaMem
        (arithmeticPropositionTokenValue (leftFormula ⋏ rightFormula))
        (arithmeticPropositionTokenValues Gamma) &&
      (tokenFormulaSetEq
          (arithmeticPropositionTokenValues left.conclusionList)
          (arithmeticPropositionTokenValues (leftFormula :: Gamma)) &&
        (tokenFormulaSetEq
            (arithmeticPropositionTokenValues right.conclusionList)
            (arithmeticPropositionTokenValues (rightFormula :: Gamma)) &&
          ((listedCertificateValidTrace left leftCertificate).1 &&
            (listedCertificateValidTrace right rightCertificate).1)))) =
      (listedCertificateValidTrace
        (.and Gamma leftFormula rightFormula left right)
        (.binary leftCertificate rightCertificate)).1
  rw [tokenFormulaMem_canonical_eq_formulaMemTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

abbrev CompactNumericOrRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue ×
      (CompactNumericFormulaValue × CompactNumericChildResult))

def compactOrRuleCheck (input : CompactNumericOrRuleInput) : Bool :=
  let Gamma := input.1
  let leftFormula := input.2.1
  let rightFormula := input.2.2.1
  let premise := input.2.2.2
  tokenFormulaMem (tokenFormulaOr leftFormula rightFormula) Gamma &&
    (tokenFormulaSetEq premise.1
        (leftFormula :: rightFormula :: Gamma) && premise.2)

theorem compactOrRuleCheck_primrec : Primrec compactOrRuleCheck := by
  let Input := CompactNumericOrRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hleftFormula : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hrightFormula : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpremise : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpremiseConclusion : Primrec (fun input : Input =>
      input.2.2.2.1) := Primrec.fst.comp hpremise
  have hpremiseValid : Primrec (fun input : Input =>
      input.2.2.2.2) := Primrec.snd.comp hpremise
  have hprincipal : Primrec (fun input : Input =>
      tokenFormulaOr input.2.1 input.2.2.1) :=
    tokenFormulaOr_primrec.comp hleftFormula hrightFormula
  have hmember : Primrec (fun input : Input =>
      tokenFormulaMem
        (tokenFormulaOr input.2.1 input.2.2.1) input.1) :=
    tokenFormulaMem_primrec.comp hprincipal hGamma
  have hrightCons : Primrec (fun input : Input =>
      input.2.2.1 :: input.1) :=
    Primrec.list_cons.comp hrightFormula hGamma
  have hexpected : Primrec (fun input : Input =>
      input.2.1 :: input.2.2.1 :: input.1) :=
    Primrec.list_cons.comp hleftFormula hrightCons
  have hsetEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
        (input.2.1 :: input.2.2.1 :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hpremiseConclusion hexpected
  have htail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
          (input.2.1 :: input.2.2.1 :: input.1) &&
        input.2.2.2.2) :=
    Primrec.and.comp hsetEq hpremiseValid
  exact (Primrec.and.comp hmember htail).of_eq fun input => by
    rfl

theorem compactOrRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    compactOrRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (arithmeticPropositionTokenValue leftFormula,
            (arithmeticPropositionTokenValue rightFormula,
              (arithmeticPropositionTokenValues premise.conclusionList,
                (listedCertificateValidTrace
                  premise premiseCertificate).1)))) =
      (listedCertificateValidTrace
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate)).1 := by
  simp only [compactOrRuleCheck]
  change
    (tokenFormulaMem
        (arithmeticPropositionTokenValue (leftFormula ⋎ rightFormula))
        (arithmeticPropositionTokenValues Gamma) &&
      (tokenFormulaSetEq
          (arithmeticPropositionTokenValues premise.conclusionList)
          (arithmeticPropositionTokenValues
            (leftFormula :: rightFormula :: Gamma)) &&
        (listedCertificateValidTrace premise premiseCertificate).1)) =
      (listedCertificateValidTrace
        (.or Gamma leftFormula rightFormula premise)
        (.unary premiseCertificate)).1
  rw [tokenFormulaMem_canonical_eq_formulaMemTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

/-! ## Quantifier rules -/

abbrev CompactNumericAllRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue × CompactNumericChildResult)

def compactAllRuleCheck (input : CompactNumericAllRuleInput) : Bool :=
  let Gamma := input.1
  let formula := input.2.1
  let premise := input.2.2
  let freed := (compactFormulaFreeExact formula).getD []
  let shiftedGamma := (compactFormulaShiftExactList Gamma).getD []
  tokenFormulaMem (tokenFormulaAll formula) Gamma &&
    (tokenFormulaSetEq premise.1 (freed :: shiftedGamma) && premise.2)

theorem compactAllRuleCheck_primrec : Primrec compactAllRuleCheck := by
  let Input := CompactNumericAllRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hformula : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hpremise : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hpremiseConclusion : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp hpremise
  have hpremiseValid : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp hpremise
  have hfreeOption : Primrec (fun input : Input =>
      compactFormulaFreeExact input.2.1) :=
    compactFormulaFreeExact_primrec.comp hformula
  have hfreed : Primrec (fun input : Input =>
      (compactFormulaFreeExact input.2.1).getD []) :=
    Primrec.option_getD.comp hfreeOption (Primrec.const [])
  have hshiftOption : Primrec (fun input : Input =>
      compactFormulaShiftExactList input.1) :=
    compactFormulaShiftExactList_primrec.comp hGamma
  have hshiftedGamma : Primrec (fun input : Input =>
      (compactFormulaShiftExactList input.1).getD []) :=
    Primrec.option_getD.comp hshiftOption (Primrec.const [])
  have hprincipal : Primrec (fun input : Input =>
      tokenFormulaAll input.2.1) :=
    tokenFormulaAll_primrec.comp hformula
  have hmember : Primrec (fun input : Input =>
      tokenFormulaMem (tokenFormulaAll input.2.1) input.1) :=
    tokenFormulaMem_primrec.comp hprincipal hGamma
  have hexpected : Primrec (fun input : Input =>
      (compactFormulaFreeExact input.2.1).getD [] ::
        (compactFormulaShiftExactList input.1).getD []) :=
    Primrec.list_cons.comp hfreed hshiftedGamma
  have hsetEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.1
        ((compactFormulaFreeExact input.2.1).getD [] ::
          (compactFormulaShiftExactList input.1).getD [])) :=
    tokenFormulaSetEq_primrec.comp hpremiseConclusion hexpected
  have htail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.1
          ((compactFormulaFreeExact input.2.1).getD [] ::
            (compactFormulaShiftExactList input.1).getD []) &&
        input.2.2.2) :=
    Primrec.and.comp hsetEq hpremiseValid
  exact (Primrec.and.comp hmember htail).of_eq fun input => by
    rfl

theorem compactAllRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    compactAllRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula,
            (arithmeticPropositionTokenValues premise.conclusionList,
              (listedCertificateValidTrace
                premise premiseCertificate).1))) =
      (listedCertificateValidTrace
        (.all Gamma formula premise)
        (.unary premiseCertificate)).1 := by
  simp only [compactAllRuleCheck]
  rw [compactFormulaFreeExact_canonical,
    compactFormulaShiftExactList_canonical]
  simp only [Option.getD_some]
  change
    (tokenFormulaMem
        (arithmeticPropositionTokenValue (∀⁰ formula))
        (arithmeticPropositionTokenValues Gamma) &&
      (tokenFormulaSetEq
          (arithmeticPropositionTokenValues premise.conclusionList)
          (arithmeticPropositionTokenValues
            (Rewriting.free formula :: Gamma.map Rewriting.shift)) &&
        (listedCertificateValidTrace premise premiseCertificate).1)) =
      (listedCertificateValidTrace
        (.all Gamma formula premise)
        (.unary premiseCertificate)).1
  rw [tokenFormulaMem_canonical_eq_formulaMemTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

abbrev CompactNumericExsRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue ×
      (List Nat × CompactNumericChildResult))

def compactExsRuleCheck (input : CompactNumericExsRuleInput) : Bool :=
  let Gamma := input.1
  let formula := input.2.1
  let witness := input.2.2.1
  let premise := input.2.2.2
  let substituted :=
    (compactFormulaSubstitutionExact 1 (witness, formula)).getD []
  tokenFormulaMem (tokenFormulaExs formula) Gamma &&
    (tokenFormulaSetEq premise.1 (substituted :: Gamma) && premise.2)

theorem compactExsRuleCheck_primrec : Primrec compactExsRuleCheck := by
  let Input := CompactNumericExsRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hformula : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hwitness : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpremise : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpremiseConclusion : Primrec (fun input : Input => input.2.2.2.1) :=
    Primrec.fst.comp hpremise
  have hpremiseValid : Primrec (fun input : Input => input.2.2.2.2) :=
    Primrec.snd.comp hpremise
  have hsubstitutionInput : Primrec (fun input : Input =>
      (input.2.2.1, input.2.1)) :=
    Primrec.pair hwitness hformula
  have hsubstitutionOption : Primrec (fun input : Input =>
      compactFormulaSubstitutionExact 1
        (input.2.2.1, input.2.1)) :=
    compactFormulaSubstitutionExact_primrec.comp
      (Primrec.const 1) hsubstitutionInput
  have hsubstituted : Primrec (fun input : Input =>
      (compactFormulaSubstitutionExact 1
        (input.2.2.1, input.2.1)).getD []) :=
    Primrec.option_getD.comp hsubstitutionOption (Primrec.const [])
  have hprincipal : Primrec (fun input : Input =>
      tokenFormulaExs input.2.1) :=
    tokenFormulaExs_primrec.comp hformula
  have hmember : Primrec (fun input : Input =>
      tokenFormulaMem (tokenFormulaExs input.2.1) input.1) :=
    tokenFormulaMem_primrec.comp hprincipal hGamma
  have hexpected : Primrec (fun input : Input =>
      (compactFormulaSubstitutionExact 1
          (input.2.2.1, input.2.1)).getD [] :: input.1) :=
    Primrec.list_cons.comp hsubstituted hGamma
  have hsetEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
        ((compactFormulaSubstitutionExact 1
            (input.2.2.1, input.2.1)).getD [] :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hpremiseConclusion hexpected
  have htail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
          ((compactFormulaSubstitutionExact 1
              (input.2.2.1, input.2.1)).getD [] :: input.1) &&
        input.2.2.2.2) :=
    Primrec.and.comp hsetEq hpremiseValid
  exact (Primrec.and.comp hmember htail).of_eq fun input => by
    rfl

theorem compactExsRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    compactExsRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (compactArithmeticFormulaTokens formula,
            (compactArithmeticTermTokens witness,
              (arithmeticPropositionTokenValues premise.conclusionList,
                (listedCertificateValidTrace
                  premise premiseCertificate).1)))) =
      (listedCertificateValidTrace
        (.exs Gamma formula witness premise)
        (.unary premiseCertificate)).1 := by
  simp only [compactExsRuleCheck]
  rw [compactFormulaSubstitutionExact_canonical]
  simp only [Option.getD_some]
  change
    (tokenFormulaMem
        (arithmeticPropositionTokenValue (∃⁰ formula))
        (arithmeticPropositionTokenValues Gamma) &&
      (tokenFormulaSetEq
          (arithmeticPropositionTokenValues premise.conclusionList)
          (arithmeticPropositionTokenValues
            (formula/[witness] :: Gamma)) &&
        (listedCertificateValidTrace premise premiseCertificate).1)) =
      (listedCertificateValidTrace
        (.exs Gamma formula witness premise)
        (.unary premiseCertificate)).1
  rw [tokenFormulaMem_canonical_eq_formulaMemTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

/-! ## Structural and cut rules -/

abbrev CompactNumericWkRuleInput :=
  CompactNumericSequentValue × CompactNumericChildResult

def compactWkRuleCheck (input : CompactNumericWkRuleInput) : Bool :=
  tokenFormulaSubset input.2.1 input.1 && input.2.2

theorem compactWkRuleCheck_primrec : Primrec compactWkRuleCheck := by
  let Input := CompactNumericWkRuleInput
  have hsubset : Primrec (fun input : Input =>
      tokenFormulaSubset input.2.1 input.1) :=
    tokenFormulaSubset_primrec.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hvalid : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp hsubset hvalid

theorem compactWkRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    compactWkRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1)) =
      (listedCertificateValidTrace (.wk Gamma premise)
        (.unary premiseCertificate)).1 := by
  unfold compactWkRuleCheck
  rw [tokenFormulaSubset_canonical_eq_formulaSubsetTrace_result]
  rfl

def compactShiftRuleCheck (input : CompactNumericWkRuleInput) : Bool :=
  let shiftedPremise :=
    (compactFormulaShiftExactList input.2.1).getD []
  tokenFormulaSetEq input.1 shiftedPremise && input.2.2

theorem compactShiftRuleCheck_primrec :
    Primrec compactShiftRuleCheck := by
  let Input := CompactNumericWkRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hpremiseConclusion : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hpremiseValid : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hshiftOption : Primrec (fun input : Input =>
      compactFormulaShiftExactList input.2.1) :=
    compactFormulaShiftExactList_primrec.comp hpremiseConclusion
  have hshifted : Primrec (fun input : Input =>
      (compactFormulaShiftExactList input.2.1).getD []) :=
    Primrec.option_getD.comp hshiftOption (Primrec.const [])
  have hsetEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.1
        ((compactFormulaShiftExactList input.2.1).getD [])) :=
    tokenFormulaSetEq_primrec.comp hGamma hshifted
  exact (Primrec.and.comp hsetEq hpremiseValid).of_eq fun input => by
    rfl

theorem compactShiftRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate) :
    compactShiftRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (arithmeticPropositionTokenValues premise.conclusionList,
            (listedCertificateValidTrace premise premiseCertificate).1)) =
      (listedCertificateValidTrace (.shift Gamma premise)
        (.unary premiseCertificate)).1 := by
  simp only [compactShiftRuleCheck]
  rw [compactFormulaShiftExactList_canonical]
  simp only [Option.getD_some]
  rw [tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

abbrev CompactNumericCutRuleInput :=
  CompactNumericSequentValue ×
    (CompactNumericFormulaValue ×
      (CompactNumericChildResult × CompactNumericChildResult))

def compactCutRuleCheck (input : CompactNumericCutRuleInput) : Bool :=
  let Gamma := input.1
  let formula := input.2.1
  let left := input.2.2.1
  let right := input.2.2.2
  let negated := (compactFormulaNegationExact 0 formula).getD []
  tokenFormulaSetEq left.1 (formula :: Gamma) &&
    (tokenFormulaSetEq right.1 (negated :: Gamma) &&
      (left.2 && right.2))

theorem compactCutRuleCheck_primrec : Primrec compactCutRuleCheck := by
  let Input := CompactNumericCutRuleInput
  have hGamma : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hformula : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hchildren : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hleft : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp hchildren
  have hright : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp hchildren
  have hleftConclusion : Primrec (fun input : Input => input.2.2.1.1) :=
    Primrec.fst.comp hleft
  have hrightConclusion : Primrec (fun input : Input => input.2.2.2.1) :=
    Primrec.fst.comp hright
  have hleftValid : Primrec (fun input : Input => input.2.2.1.2) :=
    Primrec.snd.comp hleft
  have hrightValid : Primrec (fun input : Input => input.2.2.2.2) :=
    Primrec.snd.comp hright
  have hnegationOption : Primrec (fun input : Input =>
      compactFormulaNegationExact 0 input.2.1) :=
    compactFormulaNegationExact_primrec.comp
      (Primrec.const 0) hformula
  have hnegated : Primrec (fun input : Input =>
      (compactFormulaNegationExact 0 input.2.1).getD []) :=
    Primrec.option_getD.comp hnegationOption (Primrec.const [])
  have hleftExpected : Primrec (fun input : Input =>
      input.2.1 :: input.1) :=
    Primrec.list_cons.comp hformula hGamma
  have hrightExpected : Primrec (fun input : Input =>
      (compactFormulaNegationExact 0 input.2.1).getD [] :: input.1) :=
    Primrec.list_cons.comp hnegated hGamma
  have hleftEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.1.1 (input.2.1 :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hleftConclusion hleftExpected
  have hrightEq : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
        ((compactFormulaNegationExact 0 input.2.1).getD [] :: input.1)) :=
    tokenFormulaSetEq_primrec.comp hrightConclusion hrightExpected
  have hchildrenValid : Primrec (fun input : Input =>
      input.2.2.1.2 && input.2.2.2.2) :=
    Primrec.and.comp hleftValid hrightValid
  have htail : Primrec (fun input : Input =>
      tokenFormulaSetEq input.2.2.2.1
          ((compactFormulaNegationExact 0 input.2.1).getD [] :: input.1) &&
        (input.2.2.1.2 && input.2.2.2.2)) :=
    Primrec.and.comp hrightEq hchildrenValid
  exact (Primrec.and.comp hleftEq htail).of_eq fun input => by
    rfl

theorem compactCutRuleCheck_canonical
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate) :
    compactCutRuleCheck
        (arithmeticPropositionTokenValues Gamma,
          (arithmeticPropositionTokenValue formula,
            ((arithmeticPropositionTokenValues left.conclusionList,
                (listedCertificateValidTrace left leftCertificate).1),
              (arithmeticPropositionTokenValues right.conclusionList,
                (listedCertificateValidTrace right rightCertificate).1)))) =
      (listedCertificateValidTrace (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)).1 := by
  simp only [compactCutRuleCheck]
  rw [show compactFormulaNegationExact 0
      (arithmeticPropositionTokenValue formula) =
      some (arithmeticPropositionTokenValue (∼formula)) by
    simpa [arithmeticPropositionTokenValue] using
      compactFormulaNegationExact_canonical formula]
  simp only [Option.getD_some]
  change
    (tokenFormulaSetEq
        (arithmeticPropositionTokenValues left.conclusionList)
        (arithmeticPropositionTokenValues (formula :: Gamma)) &&
      (tokenFormulaSetEq
          (arithmeticPropositionTokenValues right.conclusionList)
          (arithmeticPropositionTokenValues ((∼formula) :: Gamma)) &&
        ((listedCertificateValidTrace left leftCertificate).1 &&
          (listedCertificateValidTrace right rightCertificate).1))) =
      (listedCertificateValidTrace (.cut Gamma formula left right)
        (.binary leftCertificate rightCertificate)).1
  rw [tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result,
    tokenFormulaSetEq_canonical_eq_formulaSetEqTrace_result]
  rfl

#print axioms compactClosedRuleCheck_primrec
#print axioms compactClosedRuleCheck_canonical
#print axioms compactAxmRuleCheck_primrec
#print axioms compactAxmRuleCheck_canonical
#print axioms compactVerumRuleCheck_primrec
#print axioms compactVerumRuleCheck_canonical
#print axioms compactAndRuleCheck_primrec
#print axioms compactAndRuleCheck_canonical
#print axioms compactOrRuleCheck_primrec
#print axioms compactOrRuleCheck_canonical
#print axioms compactFormulaFreeExact_primrec
#print axioms compactFormulaShiftExactList_primrec
#print axioms compactAllRuleCheck_primrec
#print axioms compactAllRuleCheck_canonical
#print axioms compactExsRuleCheck_primrec
#print axioms compactExsRuleCheck_canonical
#print axioms compactWkRuleCheck_primrec
#print axioms compactWkRuleCheck_canonical
#print axioms compactShiftRuleCheck_primrec
#print axioms compactShiftRuleCheck_canonical
#print axioms compactCutRuleCheck_primrec
#print axioms compactCutRuleCheck_canonical

end FoundationCompactNumericListedRuleChecks

import integration.FoundationCompactCertifiedPAProof

/-!
# Structural bounds for successful compact verification

These lemmas show that every successful compact decoder consumes enough input
bits to pay for the complete decoded syntax.  They are the first quantitative
link between the honest proof-string length and a verifier cost bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactVerifierStructuralBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof

theorem decodeBinaryNat_consumes_two
    {bits suffix : List Bool} {value : Nat}
    (hdecode : decodeBinaryNat bits = some (value, suffix)) :
    suffix.length + 2 <= bits.length := by
  induction bits using List.twoStepInduction generalizing value suffix with
  | nil => simp [decodeBinaryNat] at hdecode
  | singleton bit => cases bit <;> simp [decodeBinaryNat] at hdecode
  | cons_cons first second rest ihRest ihCons =>
      cases first with
      | false =>
          cases second with
          | false =>
              simp [decodeBinaryNat] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp
          | true => simp [decodeBinaryNat] at hdecode
      | true =>
          cases hrest : decodeBinaryNat rest with
          | none => simp [decodeBinaryNat, hrest] at hdecode
          | some result =>
              rcases result with ⟨restValue, restSuffix⟩
              have htail : restSuffix.length + 2 <= rest.length :=
                ihRest hrest
              simp [decodeBinaryNat, hrest] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp only [List.length_cons]
              omega

theorem decodeManyVector_weight_le
    {alpha : Type*}
    (decode : List Bool -> Option (alpha × List Bool))
    (weight : alpha -> Nat)
    (hdecodeWeight : forall {bits suffix item},
      decode bits = some (item, suffix) ->
        weight item + suffix.length <= bits.length) :
    forall {count bits suffix items},
      decodeManyVector decode count bits = some (items, suffix) ->
      (items.toList.map weight).sum + suffix.length <= bits.length := by
  intro count
  induction count with
  | zero =>
      intro bits suffix items hdecode
      simp [decodeManyVector] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      simp
  | succ count ih =>
      intro bits suffix items hdecode
      cases hhead : decode bits with
      | none => simp [decodeManyVector, hhead] at hdecode
      | some result =>
          rcases result with ⟨head, rest⟩
          cases htail : decodeManyVector decode count rest with
          | none => simp [decodeManyVector, hhead, htail] at hdecode
          | some result =>
              rcases result with ⟨tail, finalSuffix⟩
              simp [decodeManyVector, hhead, htail] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hheadWeight := hdecodeWeight hhead
              have htailWeight := ih htail
              simp only [List.Vector.toList_cons, List.map_cons,
                List.sum_cons]
              omega

theorem decodeCompactTerm_symbolCount_le :
    forall {arity fuel bits suffix term},
      decodeCompactTerm arity fuel bits = some (term, suffix) ->
      termSymbolCount term + suffix.length <= bits.length := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits suffix term hdecode
      simp [decodeCompactTerm] at hdecode
  | succ fuel ih =>
      intro bits suffix term hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactTerm, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_consumes_two htag
          cases tag with
          | zero =>
              cases hindex : decodeBinaryNat afterTag with
              | none => simp [decodeCompactTerm, htag, hindex] at hdecode
              | some indexResult =>
                  rcases indexResult with ⟨index, afterIndex⟩
                  by_cases hindexBound : index < arity
                  · simp [decodeCompactTerm, htag, hindex,
                      hindexBound] at hdecode
                    rcases hdecode with ⟨rfl, rfl⟩
                    have hindexLength := decodeBinaryNat_consumes_two hindex
                    simp only [termSymbolCount]
                    omega
                  · simp [decodeCompactTerm, htag, hindex,
                      hindexBound] at hdecode
          | succ tag =>
              cases tag with
              | zero =>
                  cases hindex : decodeBinaryNat afterTag with
                  | none => simp [decodeCompactTerm, htag, hindex] at hdecode
                  | some indexResult =>
                      rcases indexResult with ⟨index, afterIndex⟩
                      simp [decodeCompactTerm, htag, hindex] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have hindexLength := decodeBinaryNat_consumes_two hindex
                      simp only [termSymbolCount]
                      omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      cases harity : decodeBinaryNat afterTag with
                      | none => simp [decodeCompactTerm, htag, harity] at hdecode
                      | some arityResult =>
                          rcases arityResult with ⟨functionArity, afterArity⟩
                          cases hfunction : decodeBinaryNat afterArity with
                          | none =>
                              simp [decodeCompactTerm, htag, harity,
                                hfunction] at hdecode
                          | some functionResult =>
                              rcases functionResult with
                                ⟨functionCode, afterFunction⟩
                              cases hsymbol :
                                  (Encodable.decode₂ _ functionCode :
                                    Option (LO.FirstOrder.Language.Func
                                      ℒₒᵣ functionArity)) with
                              | none =>
                                  simp [decodeCompactTerm, htag, harity,
                                    hfunction, hsymbol] at hdecode
                              | some functionSymbol =>
                                  cases harguments :
                                      decodeManyVector
                                        (decodeCompactTerm arity fuel)
                                        functionArity afterFunction with
                                  | none =>
                                      simp [decodeCompactTerm, htag, harity,
                                        hfunction, hsymbol, harguments]
                                        at hdecode
                                  | some argumentsResult =>
                                      rcases argumentsResult with
                                        ⟨arguments, afterArguments⟩
                                      simp [decodeCompactTerm, htag, harity,
                                        hfunction, hsymbol, harguments]
                                        at hdecode
                                      rcases hdecode with ⟨rfl, rfl⟩
                                      have hargumentsLength :=
                                        decodeManyVector_weight_le
                                          (decodeCompactTerm arity fuel)
                                          termSymbolCount
                                          (fun h => ih h)
                                          harguments
                                      have harityLength :=
                                        decodeBinaryNat_consumes_two harity
                                      have hfunctionLength :=
                                        decodeBinaryNat_consumes_two hfunction
                                      have hsum :
                                          (arguments.toList.map
                                              termSymbolCount).sum =
                                            Finset.univ.sum
                                              (fun i => termSymbolCount
                                                (arguments.get i)) := by
                                        calc
                                          (arguments.toList.map
                                              termSymbolCount).sum =
                                              ((List.Vector.ofFn
                                                arguments.get).toList.map
                                                  termSymbolCount).sum := by
                                                    rw [List.Vector.ofFn_get]
                                          _ = ((List.ofFn arguments.get).map
                                                termSymbolCount).sum := by
                                                  rw [List.Vector.toList_ofFn]
                                          _ = (List.ofFn
                                                (fun i => termSymbolCount
                                                  (arguments.get i))).sum := by
                                                  simp [List.map_ofFn,
                                                    Function.comp_def]
                                          _ = Finset.univ.sum
                                                (fun i => termSymbolCount
                                                  (arguments.get i)) :=
                                            list_sum_ofFn_eq_finset_sum _
                                      rw [hsum] at hargumentsLength
                                      simp only [termSymbolCount]
                                      omega
                  | succ tag =>
                      simp [decodeCompactTerm, htag] at hdecode

theorem vector_map_sum_eq_finset_sum
    {alpha : Type*} {count : Nat}
    (items : List.Vector alpha count) (weight : alpha -> Nat) :
    (items.toList.map weight).sum =
      Finset.univ.sum (fun i => weight (items.get i)) := by
  calc
    (items.toList.map weight).sum =
        ((List.Vector.ofFn items.get).toList.map weight).sum := by
          rw [List.Vector.ofFn_get]
    _ = ((List.ofFn items.get).map weight).sum := by
          rw [List.Vector.toList_ofFn]
    _ = (List.ofFn (fun i => weight (items.get i))).sum := by
          simp [List.map_ofFn, Function.comp_def]
    _ = Finset.univ.sum (fun i => weight (items.get i)) :=
      list_sum_ofFn_eq_finset_sum _

theorem decodeCompactFormula_symbolCount_le :
    forall {arity fuel bits suffix formula},
      decodeCompactFormula arity fuel bits = some (formula, suffix) ->
      formulaSymbolCount formula + suffix.length <= bits.length := by
  intro arity fuel
  induction fuel generalizing arity with
  | zero =>
      intro bits suffix formula hdecode
      simp [decodeCompactFormula] at hdecode
  | succ fuel ih =>
      intro bits suffix formula hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodeCompactFormula, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_consumes_two htag
          cases tag with
          | zero =>
              cases harity : decodeBinaryNat afterTag with
              | none => simp [decodeCompactFormula, htag, harity] at hdecode
              | some arityResult =>
                  rcases arityResult with ⟨relationArity, afterArity⟩
                  cases hrelation : decodeBinaryNat afterArity with
                  | none =>
                      simp [decodeCompactFormula, htag, harity,
                        hrelation] at hdecode
                  | some relationResult =>
                      rcases relationResult with
                        ⟨relationCode, afterRelation⟩
                      cases hsymbol :
                          (Encodable.decode₂ _ relationCode :
                            Option (LO.FirstOrder.Language.Rel
                              ℒₒᵣ relationArity)) with
                      | none =>
                          simp [decodeCompactFormula, htag, harity,
                            hrelation, hsymbol] at hdecode
                      | some relationSymbol =>
                          cases harguments :
                              decodeManyVector
                                (decodeCompactTerm arity fuel)
                                relationArity afterRelation with
                          | none =>
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol, harguments] at hdecode
                          | some argumentsResult =>
                              rcases argumentsResult with
                                ⟨arguments, afterArguments⟩
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol, harguments] at hdecode
                              rcases hdecode with ⟨rfl, rfl⟩
                              have hargumentsLength :=
                                decodeManyVector_weight_le
                                  (decodeCompactTerm arity fuel)
                                  termSymbolCount
                                  (fun h =>
                                    decodeCompactTerm_symbolCount_le h)
                                  harguments
                              rw [vector_map_sum_eq_finset_sum]
                                at hargumentsLength
                              have harityLength :=
                                decodeBinaryNat_consumes_two harity
                              have hrelationLength :=
                                decodeBinaryNat_consumes_two hrelation
                              simp only [formulaSymbolCount]
                              omega
          | succ tag =>
              cases tag with
              | zero =>
                  cases harity : decodeBinaryNat afterTag with
                  | none =>
                      simp [decodeCompactFormula, htag, harity] at hdecode
                  | some arityResult =>
                      rcases arityResult with ⟨relationArity, afterArity⟩
                      cases hrelation : decodeBinaryNat afterArity with
                      | none =>
                          simp [decodeCompactFormula, htag, harity,
                            hrelation] at hdecode
                      | some relationResult =>
                          rcases relationResult with
                            ⟨relationCode, afterRelation⟩
                          cases hsymbol :
                              (Encodable.decode₂ _ relationCode :
                                Option (LO.FirstOrder.Language.Rel
                                  ℒₒᵣ relationArity)) with
                          | none =>
                              simp [decodeCompactFormula, htag, harity,
                                hrelation, hsymbol] at hdecode
                          | some relationSymbol =>
                              cases harguments :
                                  decodeManyVector
                                    (decodeCompactTerm arity fuel)
                                    relationArity afterRelation with
                              | none =>
                                  simp [decodeCompactFormula, htag, harity,
                                    hrelation, hsymbol, harguments] at hdecode
                              | some argumentsResult =>
                                  rcases argumentsResult with
                                    ⟨arguments, afterArguments⟩
                                  simp [decodeCompactFormula, htag, harity,
                                    hrelation, hsymbol, harguments] at hdecode
                                  rcases hdecode with ⟨rfl, rfl⟩
                                  have hargumentsLength :=
                                    decodeManyVector_weight_le
                                      (decodeCompactTerm arity fuel)
                                      termSymbolCount
                                      (fun h =>
                                        decodeCompactTerm_symbolCount_le h)
                                      harguments
                                  rw [vector_map_sum_eq_finset_sum]
                                    at hargumentsLength
                                  have harityLength :=
                                    decodeBinaryNat_consumes_two harity
                                  have hrelationLength :=
                                    decodeBinaryNat_consumes_two hrelation
                                  simp only [formulaSymbolCount]
                                  omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp [decodeCompactFormula, htag] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      simp only [formulaSymbolCount]
                      omega
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp [decodeCompactFormula, htag] at hdecode
                          rcases hdecode with ⟨rfl, rfl⟩
                          simp only [formulaSymbolCount]
                          omega
                      | succ tag =>
                          cases tag with
                          | zero =>
                              cases hleft :
                                  decodeCompactFormula arity fuel afterTag with
                              | none =>
                                  simp [decodeCompactFormula, htag, hleft]
                                    at hdecode
                              | some leftResult =>
                                  rcases leftResult with ⟨left, afterLeft⟩
                                  cases hright :
                                      decodeCompactFormula arity fuel afterLeft with
                                  | none =>
                                      simp [decodeCompactFormula, htag, hleft,
                                        hright] at hdecode
                                  | some rightResult =>
                                      rcases rightResult with
                                        ⟨right, afterRight⟩
                                      simp [decodeCompactFormula, htag, hleft,
                                        hright] at hdecode
                                      rcases hdecode with ⟨rfl, rfl⟩
                                      have hleftLength := ih hleft
                                      have hrightLength := ih hright
                                      simp only [formulaSymbolCount]
                                      omega
                          | succ tag =>
                              cases tag with
                              | zero =>
                                  cases hleft :
                                      decodeCompactFormula arity fuel afterTag with
                                  | none =>
                                      simp [decodeCompactFormula, htag, hleft]
                                        at hdecode
                                  | some leftResult =>
                                      rcases leftResult with ⟨left, afterLeft⟩
                                      cases hright :
                                          decodeCompactFormula arity fuel
                                            afterLeft with
                                      | none =>
                                          simp [decodeCompactFormula, htag,
                                            hleft, hright] at hdecode
                                      | some rightResult =>
                                          rcases rightResult with
                                            ⟨right, afterRight⟩
                                          simp [decodeCompactFormula, htag,
                                            hleft, hright] at hdecode
                                          rcases hdecode with ⟨rfl, rfl⟩
                                          have hleftLength := ih hleft
                                          have hrightLength := ih hright
                                          simp only [formulaSymbolCount]
                                          omega
                              | succ tag =>
                                  cases tag with
                                  | zero =>
                                      cases hbody :
                                          decodeCompactFormula (arity + 1)
                                            fuel afterTag with
                                      | none =>
                                          simp [decodeCompactFormula, htag,
                                            hbody] at hdecode
                                      | some bodyResult =>
                                          rcases bodyResult with
                                            ⟨body, afterBody⟩
                                          simp [decodeCompactFormula, htag,
                                            hbody] at hdecode
                                          rcases hdecode with ⟨rfl, rfl⟩
                                          have hbodyLength := ih hbody
                                          simp only [formulaSymbolCount]
                                          omega
                                  | succ tag =>
                                      cases tag with
                                      | zero =>
                                          cases hbody :
                                              decodeCompactFormula (arity + 1)
                                                fuel afterTag with
                                          | none =>
                                              simp [decodeCompactFormula,
                                                htag, hbody] at hdecode
                                          | some bodyResult =>
                                              rcases bodyResult with
                                                ⟨body, afterBody⟩
                                              simp [decodeCompactFormula,
                                                htag, hbody] at hdecode
                                              rcases hdecode with ⟨rfl, rfl⟩
                                              have hbodyLength := ih hbody
                                              simp only [formulaSymbolCount]
                                              omega
                                      | succ tag =>
                                          simp [decodeCompactFormula, htag]
                                            at hdecode

theorem list_toFinset_sum_le_map_sum
    {alpha : Type*} [DecidableEq alpha]
    (items : List alpha) (weight : alpha -> Nat) :
    items.toFinset.sum weight <= (items.map weight).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      by_cases hmem : head ∈ tail
      · simp [hmem]
        exact ih.trans (Nat.le_add_left _ _)
      · simp [hmem, ih]

theorem decodeCompactSequent_symbolCount_le
    {fuel : Nat} {bits suffix : List Bool}
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (hdecode : decodeCompactSequent fuel bits = some (Gamma, suffix)) :
    sequentSymbolCount Gamma + suffix.length <= bits.length := by
  cases hcardinality : decodeBinaryNat bits with
  | none => simp [decodeCompactSequent, hcardinality] at hdecode
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      cases hformulas :
          decodeManyVector (decodeCompactFormula 0 fuel)
            cardinality afterCardinality with
      | none =>
          simp [decodeCompactSequent, hcardinality, hformulas] at hdecode
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, afterFormulas⟩
          simp [decodeCompactSequent, hcardinality, hformulas] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hformulaLength :=
            decodeManyVector_weight_le
              (decodeCompactFormula 0 fuel) formulaSymbolCount
              (fun h => decodeCompactFormula_symbolCount_le h)
              hformulas
          have hfinset :=
            list_toFinset_sum_le_map_sum formulas.toList formulaSymbolCount
          have hcardinalityLength :=
            decodeBinaryNat_consumes_two hcardinality
          change formulas.toList.toFinset.sum formulaSymbolCount +
              afterFormulas.length <= bits.length
          have hsumWithSuffix :
              formulas.toList.toFinset.sum formulaSymbolCount +
                  afterFormulas.length <=
                (formulas.toList.map formulaSymbolCount).sum +
                  afterFormulas.length :=
            Nat.add_le_add_right hfinset _
          have hafterCardinality :
              afterCardinality.length <= bits.length := by omega
          exact hsumWithSuffix.trans
            (hformulaLength.trans hafterCardinality)

def CompactProofBudget (fuel : Nat) : Prop :=
  forall {bits suffix tree},
    decodeCompactProof fuel bits = some (tree, suffix) ->
      tree.parseWeight + suffix.length <= bits.length

theorem proofBudget_tag0
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (0, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          simp [hsequent, hformula] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          have hsequentLength :=
            decodeCompactSequent_symbolCount_le hsequent
          have hformulaLength :=
            decodeCompactFormula_symbolCount_le hformula
          simp only [CheckedPAProofTree.parseWeight]
          omega

theorem proofBudget_tag1
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (1, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      cases hformula : decodeCompactFormula 0 fuel afterSequent with
      | none => simp [hsequent, hformula] at hdecode
      | some formulaResult =>
          rcases formulaResult with ⟨formula, afterFormula⟩
          cases hsentence : propositionToSentence formula with
          | none => simp [hsequent, hformula, hsentence] at hdecode
          | some sigma =>
              simp [hsequent, hformula, hsentence] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              have hsequentLength :=
                decodeCompactSequent_symbolCount_le hsequent
              have hformulaLength :=
                decodeCompactFormula_symbolCount_le hformula
              have hemb :
                  (Rewriting.emb sigma :
                    LO.FirstOrder.ArithmeticProposition) = formula := by
                unfold propositionToSentence at hsentence
                split at hsentence
                next hclosed =>
                  simp at hsentence
                  subst sigma
                  exact Semiformula.emb_toEmpty formula hclosed
                next hnotClosed => simp at hsentence
              simp only [CheckedPAProofTree.parseWeight]
              rw [hemb]
              omega

theorem proofBudget_tag2
    {fuel : Nat} {bits afterTag suffix : List Bool}
    {tree : CheckedPAProofTree}
    (htag : decodeBinaryNat bits = some (2, afterTag))
    (hdecode : decodeCompactProof (fuel + 1) bits = some (tree, suffix)) :
    tree.parseWeight + suffix.length <= bits.length := by
  have htagLength := decodeBinaryNat_consumes_two htag
  simp only [decodeCompactProof] at hdecode
  rw [htag] at hdecode
  cases hsequent : decodeCompactSequent fuel afterTag with
  | none => simp [hsequent] at hdecode
  | some sequentResult =>
      rcases sequentResult with ⟨Gamma, afterSequent⟩
      simp [hsequent] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      have hsequentLength :=
        decodeCompactSequent_symbolCount_le hsequent
      simp only [CheckedPAProofTree.parseWeight]
      omega

end FoundationCompactVerifierStructuralBound

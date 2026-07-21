import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
import integration.FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the accepted-trace final tail

The parent tail is kept at arbitrary valuation terms.  The public certificate
specializes the table coordinates to closed short binary numerals, keeps the
original `fuelTerm`, and installs the explicit witness
`termValue zeroValuation fuelTerm - 1`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

/-- The valuation used by the closed table-coordinate specialization. -/
def zeroValuation : Nat -> Nat := fun _ => 0

/-- The exact three-coordinate final tail occurring in
`compactNumericVerifierAcceptedTraceTableDef`. -/
def compactNumericVerifierAcceptedTraceFinalDef :
    HierarchySymbol.sigmaZero.Semisentence 3 := .mkSigma
  “tableWidth table fuel.
    ∃ lastRow < fuel,
      lastRow + 1 = fuel ∧
      !(compactNumericVerifierAcceptedWitnessTableRowDef)
        tableWidth table lastRow”
  (by simp)

@[simp] theorem compactNumericVerifierAcceptedTraceFinalDef_spec
    (tableWidth table fuel : Nat) :
    compactNumericVerifierAcceptedTraceFinalDef.val.Evalb
        ![tableWidth, table, fuel] ↔
      ∃ lastRow < fuel,
        lastRow + 1 = fuel ∧
        CompactNumericVerifierAcceptedWitnessTableRow
          tableWidth table lastRow := by
  simp [compactNumericVerifierAcceptedTraceFinalDef]

/-- The parent tail instantiated by its original valuation terms. -/
def compactNumericVerifierAcceptedTraceFinalAtTermFormula
    (tableWidthTerm tableTerm fuelTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierAcceptedTraceFinalDef.val) ⇜
    ![tableWidthTerm, tableTerm, fuelTerm]

private def compactNumericVerifierAcceptedTraceFinalGuardBody
    (fuelTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift fuelTerm)”

private def compactNumericVerifierAcceptedTraceFinalSuccessorBody
    (fuelTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 + 1 = !!(Rew.bShift fuelTerm)”

private def compactNumericVerifierAcceptedTraceFinalAcceptedBody
    (tableWidthTerm tableTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!(compactNumericVerifierAcceptedWitnessTableRowDef)
      !!(Rew.bShift tableWidthTerm) !!(Rew.bShift tableTerm) #0”

/-- The body exposed below the final-row existential. -/
def compactNumericVerifierAcceptedTraceFinalWitnessBody
    (tableWidthTerm tableTerm fuelTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  compactNumericVerifierAcceptedTraceFinalGuardBody fuelTerm ⋏
    (compactNumericVerifierAcceptedTraceFinalSuccessorBody fuelTerm ⋏
      compactNumericVerifierAcceptedTraceFinalAcceptedBody
        tableWidthTerm tableTerm)

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
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
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
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

private theorem finalOuterFuelTerm_rewrite
    (tableWidthTerm tableTerm fuelTerm : ValuationTerm) :
    (Rew.subst ![tableWidthTerm, tableTerm, fuelTerm]).q
        (#3 : LO.FirstOrder.ArithmeticSemiterm Nat 4) =
      Rew.bShift fuelTerm := by
  change
    (Rew.subst ![tableWidthTerm, tableTerm, fuelTerm]).q
        (#((2 : Fin 3).succ)) = _
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  rfl

private theorem finalAcceptedBodyRewriting_eq
    (tableWidthTerm tableTerm fuelTerm : ValuationTerm) :
    (Rew.subst ![tableWidthTerm, tableTerm, fuelTerm]).q.comp
        ((Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4).comp
          (Rew.subst ![
            (#1 : LO.FirstOrder.ArithmeticSemiterm Empty 4), #2, #0])) =
      (Rew.subst ![
          Rew.bShift tableWidthTerm,
          Rew.bShift tableTerm,
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)]).comp
        (Rew.emb : Rew ℒₒᵣ Empty 3 Nat 3) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        change
          (Rew.subst ![tableWidthTerm, tableTerm, fuelTerm]).q
              (#((0 : Fin 3).succ)) = _
        rw [Rew.q_bvar_succ, Rew.subst_bvar]
        rfl
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change
              (Rew.subst ![tableWidthTerm, tableTerm, fuelTerm]).q
                  (#((1 : Fin 3).succ)) = _
            rw [Rew.q_bvar_succ, Rew.subst_bvar]
            rfl
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => simp [Rew.comp_app, Rew.q_bvar_zero]
            | succ coordinate => exact Fin.elim0 coordinate
  · exact Empty.elim coordinate

/-- Strict syntactic alignment between the substituted parent tail and the
explicit existential body. -/
theorem compactNumericVerifierAcceptedTraceFinalAtTermFormula_alignment
    (tableWidthTerm tableTerm fuelTerm : ValuationTerm) :
    compactNumericVerifierAcceptedTraceFinalAtTermFormula
        tableWidthTerm tableTerm fuelTerm =
      ∃⁰ compactNumericVerifierAcceptedTraceFinalWitnessBody
        tableWidthTerm tableTerm fuelTerm := by
  unfold compactNumericVerifierAcceptedTraceFinalAtTermFormula
  unfold compactNumericVerifierAcceptedTraceFinalWitnessBody
  unfold compactNumericVerifierAcceptedTraceFinalGuardBody
  unfold compactNumericVerifierAcceptedTraceFinalSuccessorBody
  unfold compactNumericVerifierAcceptedTraceFinalAcceptedBody
  simp [compactNumericVerifierAcceptedTraceFinalDef,
    LO.FirstOrder.Semiformula.bexsLT,
    LO.FirstOrder.bexs,
    ← TransitiveRewriting.comp_app,
    finalOuterFuelTerm_rewrite]
  rw [finalAcceptedBodyRewriting_eq]

/-- Short-numeral table coordinates with the original `fuelTerm` untouched. -/
def compactNumericVerifierAcceptedTraceFinalAtValuationFormula
    (tableWidth table : Nat) (fuelTerm : ValuationTerm) :
    ValuationFormula :=
  compactNumericVerifierAcceptedTraceFinalAtTermFormula
    (shortBinaryNumeralTerm tableWidth)
    (shortBinaryNumeralTerm table)
    fuelTerm

private def compactNumericVerifierAcceptedTraceFinalGuardFormula
    (fuelTerm : ValuationTerm) (lastRow : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm lastRow) < !!fuelTerm”

private def compactNumericVerifierAcceptedTraceFinalSuccessorFormula
    (fuelTerm : ValuationTerm) (lastRow : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm lastRow) + 1 = !!fuelTerm”

/-- The exact conjunction obtained after installing the final-row witness. -/
def compactNumericVerifierAcceptedTraceFinalPostWitnessFormula
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (lastRow : Nat) : ValuationFormula :=
  compactNumericVerifierAcceptedTraceFinalGuardFormula fuelTerm lastRow ⋏
    (compactNumericVerifierAcceptedTraceFinalSuccessorFormula
        fuelTerm lastRow ⋏
      compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table lastRow)

private theorem subst_bShiftTerm
    (term witness : ValuationTerm) :
    Rew.subst ![witness] (Rew.bShift term) = term := by
  calc
    Rew.subst ![witness] (Rew.bShift term) =
        ((Rew.subst ![witness]).comp Rew.bShift) term := by
      rw [Rew.comp_app]
    _ = Rew.id term := by rw [Rew.subst_comp_bShift_eq_id]
    _ = term := Rew.id_app term

private theorem finalGuardBody_subst
    (fuelTerm : ValuationTerm) (lastRow : Nat) :
    (compactNumericVerifierAcceptedTraceFinalGuardBody fuelTerm)/[
        shortBinaryNumeralTerm lastRow] =
      compactNumericVerifierAcceptedTraceFinalGuardFormula
        fuelTerm lastRow := by
  simp [compactNumericVerifierAcceptedTraceFinalGuardBody,
    compactNumericVerifierAcceptedTraceFinalGuardFormula,
    Rew.subst_bShift_app]

private theorem finalSuccessorBody_subst
    (fuelTerm : ValuationTerm) (lastRow : Nat) :
    (compactNumericVerifierAcceptedTraceFinalSuccessorBody fuelTerm)/[
        shortBinaryNumeralTerm lastRow] =
      compactNumericVerifierAcceptedTraceFinalSuccessorFormula
        fuelTerm lastRow := by
  simp [compactNumericVerifierAcceptedTraceFinalSuccessorBody,
    compactNumericVerifierAcceptedTraceFinalSuccessorFormula,
    Rew.subst_bShift_app]

private theorem finalAcceptedWitnessBody_subst
    (tableWidth table lastRow : Nat) :
    (compactNumericVerifierAcceptedTraceFinalAcceptedBody
      (shortBinaryNumeralTerm tableWidth)
      (shortBinaryNumeralTerm table))/[
        shortBinaryNumeralTerm lastRow] =
      compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table lastRow := by
  unfold compactNumericVerifierAcceptedTraceFinalAcceptedBody
  change Rew.subst ![shortBinaryNumeralTerm lastRow] ▹
      ((Rewriting.emb (ξ := Nat)
          compactNumericVerifierAcceptedWitnessTableRowDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tableWidth),
          Rew.bShift (shortBinaryNumeralTerm table),
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)]) = _
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericVerifierAcceptedWitnessTableRowClosedFormula
  congr 1
  funext coordinate
  cases coordinate using Fin.cases with
  | zero =>
      change Rew.subst ![shortBinaryNumeralTerm lastRow]
          (Rew.bShift (shortBinaryNumeralTerm tableWidth)) = _
      exact subst_bShiftTerm _ _
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero =>
          change Rew.subst ![shortBinaryNumeralTerm lastRow]
              (Rew.bShift (shortBinaryNumeralTerm table)) = _
          exact subst_bShiftTerm _ _
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero =>
              change Rew.subst ![shortBinaryNumeralTerm lastRow]
                  (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) = _
              rw [Rew.subst_bvar]
              rfl
          | succ coordinate => exact Fin.elim0 coordinate

/-- Installing a short numeral witness preserves `fuelTerm` literally in both
arithmetic leaves and exposes the already certified final-row formula. -/
theorem compactNumericVerifierAcceptedTraceFinalWitnessBody_subst
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (lastRow : Nat) :
    (compactNumericVerifierAcceptedTraceFinalWitnessBody
      (shortBinaryNumeralTerm tableWidth)
      (shortBinaryNumeralTerm table)
      fuelTerm)/[shortBinaryNumeralTerm lastRow] =
      compactNumericVerifierAcceptedTraceFinalPostWitnessFormula
        tableWidth table fuelTerm lastRow := by
  simp [compactNumericVerifierAcceptedTraceFinalWitnessBody,
    compactNumericVerifierAcceptedTraceFinalPostWitnessFormula,
    finalGuardBody_subst, finalSuccessorBody_subst,
    finalAcceptedWitnessBody_subst]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def compactNumericVerifierAcceptedTraceFinalGuardCertificate
    (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedTraceFinalGuardFormula fuelTerm
        (termValue zeroValuation fuelTerm - 1)) := by
  let fuel := termValue zeroValuation fuelTerm
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm (fuel - 1), fuelTerm] (by
        change termValue zeroValuation
            (shortBinaryNumeralTerm (fuel - 1)) <
          termValue zeroValuation fuelTerm
        rw [termValue_shortBinaryNumeralTerm]
        omega)
  exact .cast (by
    unfold compactNumericVerifierAcceptedTraceFinalGuardFormula
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def
    compactNumericVerifierAcceptedTraceFinalSuccessorCertificate
    (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedTraceFinalSuccessorFormula fuelTerm
        (termValue zeroValuation fuelTerm - 1)) := by
  let fuel := termValue zeroValuation fuelTerm
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm (fuel - 1)) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, fuelTerm] (by
        change termValue zeroValuation leftTerm =
          termValue zeroValuation fuelTerm
        simp only [leftTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm, termValue_arithmeticOne]
        omega)
  exact .cast (by
    unfold compactNumericVerifierAcceptedTraceFinalSuccessorFormula
    exact (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm) direct

private noncomputable def
    compactNumericVerifierAcceptedTraceFinalRowCertificate
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table (termValue zeroValuation fuelTerm - 1)) := by
  exact
    compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
      tableWidth table (termValue zeroValuation fuelTerm - 1) haccepted

/-- Explicit closure of the accepted-trace final tail.  Its witness is
definitionally `fuel - 1`, where `fuel` is the value of the original term. -/
noncomputable def
    compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedTraceFinalAtValuationFormula
        tableWidth table fuelTerm) := by
  rw [compactNumericVerifierAcceptedTraceFinalAtValuationFormula,
    compactNumericVerifierAcceptedTraceFinalAtTermFormula_alignment]
  let fuel := termValue zeroValuation fuelTerm
  refine .existsWitness
    (compactNumericVerifierAcceptedTraceFinalWitnessBody
      (shortBinaryNumeralTerm tableWidth)
      (shortBinaryNumeralTerm table) fuelTerm)
    (fuel - 1) ?_
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactNumericVerifierAcceptedTraceFinalGuardCertificate fuelTerm hfuel)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericVerifierAcceptedTraceFinalSuccessorCertificate
        fuelTerm hfuel)
      (compactNumericVerifierAcceptedTraceFinalRowCertificate
        tableWidth table fuelTerm haccepted))
  exact .cast
    (compactNumericVerifierAcceptedTraceFinalWitnessBody_subst
      tableWidth table fuelTerm (fuel - 1)).symm post

/-- The exact valuation-context proof compiled from the explicit certificate. -/
noncomputable def
    compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) :
    CertifiedPAContextProof
      (valuationContext
        (compactNumericVerifierAcceptedTraceFinalAtValuationFormula
          tableWidth table fuelTerm).freeVariables zeroValuation)
      (compactNumericVerifierAcceptedTraceFinalAtValuationFormula
        tableWidth table fuelTerm) :=
  (compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
    tableWidth table fuelTerm hfuel haccepted).compile

/-- Proof-free recursive resource for the explicit final-tail certificate. -/
noncomputable def
    compactNumericVerifierAcceptedTraceFinalExplicitHybridStructuralResource
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
      tableWidth table fuelTerm hfuel haccepted)

theorem
    compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext_payloadLength_le
    (tableWidth table : Nat) (fuelTerm : ValuationTerm)
    (hfuel : 0 < termValue zeroValuation fuelTerm)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table (termValue zeroValuation fuelTerm - 1)) :
    (compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext
      tableWidth table fuelTerm hfuel haccepted).payloadLength ≤
      compactNumericVerifierAcceptedTraceFinalExplicitHybridStructuralResource
        tableWidth table fuelTerm hfuel haccepted := by
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
        tableWidth table fuelTerm hfuel haccepted)

#print axioms compactNumericVerifierAcceptedTraceFinalDef_spec
#print axioms compactNumericVerifierAcceptedTraceFinalAtTermFormula_alignment
#print axioms compactNumericVerifierAcceptedTraceFinalWitnessBody_subst
#print axioms
  compactNumericVerifierAcceptedTraceFinalExplicitHybridCertificate
#print axioms
  compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext
#print axioms
  compactNumericVerifierAcceptedTraceFinalExplicitHybridStructuralResource
#print axioms
  compileCompactNumericVerifierAcceptedTraceFinalExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate

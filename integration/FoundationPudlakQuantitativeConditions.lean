import integration.FoundationEfficientPAProofPredicateRE

/-!
# Quantitative Pudlak conditions for the concrete PA proof predicate

This layer fixes short binary numerals and the closed instances of the exact
two-variable proof predicate before any derivability-condition estimate is
attempted.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationPudlakQuantitativeConditions

open FoundationSuccinctFiniteConsistencyTarget
open FoundationEfficientPAProofPredicateArithmetic
open FoundationEfficientPAProofPredicateRE

/-! ## Raw-code-free local proof checking -/

/-- Local validity of a proof-field-free tree.  Unlike
`CheckedPAProofTree.Valid`, this predicate never constructs Foundation's nested
numeric proof code.  Every clause is exactly one `Derivation2` rule. -/
def structurallyValid : CheckedPAProofTree → Prop
  | .closed Gamma formula =>
      formula ∈ Gamma ∧ ∼formula ∈ Gamma
  | .axm Gamma sigma =>
      sigma ∈ F.PA ∧
        (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .verum Gamma =>
      (⊤ : LO.FirstOrder.ArithmeticProposition) ∈ Gamma
  | .and Gamma leftFormula rightFormula left right =>
      leftFormula ⋏ rightFormula ∈ Gamma ∧
        left.conclusion = insert leftFormula Gamma ∧
        right.conclusion = insert rightFormula Gamma ∧
        structurallyValid left ∧ structurallyValid right
  | .or Gamma leftFormula rightFormula premise =>
      leftFormula ⋎ rightFormula ∈ Gamma ∧
        premise.conclusion =
          insert leftFormula (insert rightFormula Gamma) ∧
        structurallyValid premise
  | .all Gamma formula premise =>
      ∀⁰ formula ∈ Gamma ∧
        premise.conclusion =
          insert (Rewriting.free formula)
            (Gamma.image Rewriting.shift) ∧
        structurallyValid premise
  | .exs Gamma formula witness premise =>
      ∃⁰ formula ∈ Gamma ∧
        premise.conclusion = insert (formula/[witness]) Gamma ∧
        structurallyValid premise
  | .wk Gamma premise =>
      premise.conclusion ⊆ Gamma ∧ structurallyValid premise
  | .shift Gamma premise =>
      Gamma = premise.conclusion.image Rewriting.shift ∧
        structurallyValid premise
  | .cut Gamma formula left right =>
      left.conclusion = insert formula Gamma ∧
        right.conclusion = insert (∼formula) Gamma ∧
        structurallyValid left ∧ structurallyValid right

/-- Soundness of the compact local checker: an accepted tree constructs a real
Foundation PA derivation of exactly its displayed conclusion. -/
theorem structurallyValid_toDerivation
    (tree : CheckedPAProofTree)
    (hvalid : structurallyValid tree) :
    Nonempty (LO.FirstOrder.Derivation2 F.PA tree.conclusion) := by
  induction tree with
  | closed Gamma formula =>
      exact ⟨LO.FirstOrder.Derivation2.closed
        Gamma formula hvalid.1 hvalid.2⟩
  | axm Gamma sigma =>
      exact ⟨LO.FirstOrder.Derivation2.axm
        sigma hvalid.1 hvalid.2⟩
  | verum Gamma =>
      exact ⟨LO.FirstOrder.Derivation2.verum hvalid⟩
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hprincipal, hleftConclusion, hrightConclusion,
          hleftValid, hrightValid⟩
      rcases ihLeft hleftValid with ⟨leftDerivation⟩
      rcases ihRight hrightValid with ⟨rightDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.and hprincipal
        (LO.FirstOrder.Derivation2.cast leftDerivation hleftConclusion)
        (LO.FirstOrder.Derivation2.cast rightDerivation
          hrightConclusion)⟩
  | or Gamma leftFormula rightFormula premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremiseValid⟩
      rcases ih hpremiseValid with ⟨premiseDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.or hprincipal
        (LO.FirstOrder.Derivation2.cast premiseDerivation
          hpremiseConclusion)⟩
  | all Gamma formula premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremiseValid⟩
      rcases ih hpremiseValid with ⟨premiseDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.all hprincipal
        (LO.FirstOrder.Derivation2.cast premiseDerivation
          hpremiseConclusion)⟩
  | exs Gamma formula witness premise ih =>
      rcases hvalid with ⟨hprincipal, hpremiseConclusion, hpremiseValid⟩
      rcases ih hpremiseValid with ⟨premiseDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.exs hprincipal witness
        (LO.FirstOrder.Derivation2.cast premiseDerivation
          hpremiseConclusion)⟩
  | wk Gamma premise ih =>
      rcases hvalid with ⟨hsubset, hpremiseValid⟩
      rcases ih hpremiseValid with ⟨premiseDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.wk premiseDerivation hsubset⟩
  | shift Gamma premise ih =>
      rcases hvalid with ⟨hconclusion, hpremiseValid⟩
      rcases ih hpremiseValid with ⟨premiseDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.cast
        (LO.FirstOrder.Derivation2.shift premiseDerivation)
        hconclusion.symm⟩
  | cut Gamma formula left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hleftConclusion, hrightConclusion, hleftValid, hrightValid⟩
      rcases ihLeft hleftValid with ⟨leftDerivation⟩
      rcases ihRight hrightValid with ⟨rightDerivation⟩
      exact ⟨LO.FirstOrder.Derivation2.cut
        (LO.FirstOrder.Derivation2.cast leftDerivation hleftConclusion)
        (LO.FirstOrder.Derivation2.cast rightDerivation
          hrightConclusion)⟩

/-- Completeness of the compact representation: erasing proof fields from any
real Foundation derivation produces a locally valid tree. -/
theorem structurallyValid_ofDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 F.PA Gamma) :
    structurallyValid (CheckedPAProofTree.ofDerivation derivation) := by
  induction derivation <;>
    simp [CheckedPAProofTree.ofDerivation, structurallyValid, *]

/-- The paper-grade bounded proof predicate before arithmetization.  Its proof
object is the compact binary tree serialization itself; no Foundation raw code
is part of the witness or of the length coordinate. -/
def CompactPAProofPredicate
    (bound : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) : Prop :=
  ∃ tree : CheckedPAProofTree,
    tree.binaryLength ≤ bound ∧
      structurallyValid tree ∧ tree.conclusion = {formula}

theorem CompactPAProofPredicate.mono
    {smaller larger : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hbound : smaller ≤ larger)
    (hproof : CompactPAProofPredicate smaller formula) :
    CompactPAProofPredicate larger formula := by
  rcases hproof with ⟨tree, hlength, hvalid, hconclusion⟩
  exact ⟨tree, hlength.trans hbound, hvalid, hconclusion⟩

theorem derivation_to_compactPAProofPredicate
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 F.PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    CompactPAProofPredicate
      (binaryProofLength derivation) formula := by
  let tree := CheckedPAProofTree.ofDerivation derivation
  refine ⟨tree, ?_, structurallyValid_ofDerivation derivation, ?_⟩
  · simp [tree]
  · simpa [tree] using hconclusion

theorem CompactPAProofPredicate.toDerivation
    {bound : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hproof : CompactPAProofPredicate bound formula) :
    Nonempty (LO.FirstOrder.Derivation2 F.PA {formula}) := by
  rcases hproof with ⟨tree, _, hvalid, hconclusion⟩
  rcases structurallyValid_toDerivation tree hvalid with ⟨derivation⟩
  exact ⟨LO.FirstOrder.Derivation2.cast derivation hconclusion⟩

/-- Compact formula numbers use the same prefix serialization as the proof
object and therefore have one-bit packing overhead. -/
def compactFormulaCode
    (formula : LO.FirstOrder.ArithmeticProposition) : Nat :=
  packBinaryString (binaryFormulaCode formula)

theorem binaryFormulaCode_injective :
    Function.Injective
      (binaryFormulaCode :
        LO.FirstOrder.ArithmeticProposition → List Bool) := by
  intro left right hcode
  let fuel := max (formulaSymbolCount left)
    (formulaSymbolCount right) + 1
  have hleftFuel : formulaSymbolCount left < fuel := by
    simp [fuel]
  have hrightFuel : formulaSymbolCount right < fuel := by
    simp [fuel]
  have hleft :=
    decodeBinaryFormulaRaw_binaryFormulaCode_append
      left fuel hleftFuel []
  have hright :=
    decodeBinaryFormulaRaw_binaryFormulaCode_append
      right fuel hrightFuel []
  have hpairs :
      (Encodable.encode left, ([] : List Bool)) =
        (Encodable.encode right, ([] : List Bool)) := by
    apply Option.some.inj
    rw [← hleft, ← hright, hcode]
  apply Encodable.encode_inj.mp
  exact congrArg Prod.fst hpairs

theorem compactFormulaCode_injective :
    Function.Injective compactFormulaCode := by
  intro left right hcode
  apply binaryFormulaCode_injective
  exact packBinaryString_injective hcode

@[simp] theorem size_compactFormulaCode
    (formula : LO.FirstOrder.ArithmeticProposition) :
    Nat.size (compactFormulaCode formula) =
      (binaryFormulaCode formula).length + 1 := by
  simp [compactFormulaCode]

/-- Numeric-coordinate form of the compact predicate.  The formula number is
the packed structural binary serialization, not Foundation's inflated HFS
formula code. -/
def CompactCodedPAProofPredicate
    (bound formulaCode : Nat) : Prop :=
  ∃ (tree : CheckedPAProofTree)
      (formula : LO.FirstOrder.ArithmeticProposition),
    tree.binaryLength ≤ bound ∧
      structurallyValid tree ∧
      tree.conclusion = {formula} ∧
      compactFormulaCode formula = formulaCode

theorem compactCodedPAProofPredicate_iff
    (bound : Nat)
    (formula : LO.FirstOrder.ArithmeticProposition) :
    CompactCodedPAProofPredicate bound (compactFormulaCode formula) ↔
      CompactPAProofPredicate bound formula := by
  constructor
  · rintro ⟨tree, codedFormula, hlength, hvalid,
      hconclusion, hcode⟩
    have hformula : codedFormula = formula :=
      compactFormulaCode_injective hcode
    subst hformula
    exact ⟨tree, hlength, hvalid, hconclusion⟩
  · rintro ⟨tree, hlength, hvalid, hconclusion⟩
    exact ⟨tree, formula, hlength, hvalid, hconclusion, rfl⟩

def binaryNumeralBitStep
    (bit : Bool)
    (term : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    LO.FirstOrder.ArithmeticSemiterm Empty 0 :=
  let doubled :=
    Semiterm.Operator.Mul.mul.operator
      ![closedNumeralTerm 2, term]
  if bit then
    Semiterm.Operator.Add.add.operator
      ![doubled, closedNumeralTerm 1]
  else doubled

/-- A closed numeral whose syntax follows the low-to-high binary digits of
`n`.  Each input bit contributes at most six term symbols. -/
def binaryNumeralTerm (n : Nat) :
    LO.FirstOrder.ArithmeticSemiterm Empty 0 :=
  n.bits.foldr binaryNumeralBitStep (closedNumeralTerm 0)

@[simp] theorem val_binaryNumeralBitStep
    (bit : Bool)
    (term : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    (binaryNumeralBitStep bit term).val ![] Empty.elim =
      Nat.bit bit (term.val ![] Empty.elim) := by
  cases bit <;>
    simp [binaryNumeralBitStep, Nat.bit, val_closedNumeralTerm]

@[simp] theorem val_binaryNumeralTerm (n : Nat) :
    (binaryNumeralTerm n).val ![] Empty.elim = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryNumeralTerm, val_closedNumeralTerm]
  | bit bit n hn ih =>
      rw [binaryNumeralTerm, Nat.bits_append_bit n bit hn]
      simp only [List.foldr_cons, val_binaryNumeralBitStep]
      change Nat.bit bit ((binaryNumeralTerm n).val ![] Empty.elim) =
        Nat.bit bit n
      rw [ih]

@[simp] theorem termSymbolCount_closedNumeralTerm_zero :
    termSymbolCount (closedNumeralTerm 0) = 1 := by
  simp [closedNumeralTerm, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq,
    termSymbolCount, Rew.func]

@[simp] theorem termSymbolCount_add
    {xi : Type*} {n : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm xi n) :
    termSymbolCount
        (Semiterm.Operator.Add.add.operator ![left, right]) =
      1 + termSymbolCount left + termSymbolCount right := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq,
    termSymbolCount, Rew.func,
    show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
      ext i
      cases i using Fin.cases <;> simp]
  omega

theorem termSymbolCount_binaryNumeralBitStep_le
    (bit : Bool)
    (term : LO.FirstOrder.ArithmeticSemiterm Empty 0) :
    termSymbolCount (binaryNumeralBitStep bit term) ≤
      termSymbolCount term + 6 := by
  cases bit <;>
    simp [binaryNumeralBitStep, termSymbolCount_mul,
      termSymbolCount_add] <;>
    omega

theorem binaryNumeralFold_symbolCount_le (bits : List Bool) :
    termSymbolCount
        (bits.foldr binaryNumeralBitStep (closedNumeralTerm 0)) ≤
      6 * bits.length + 1 := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.foldr_cons, List.length_cons]
      exact (termSymbolCount_binaryNumeralBitStep_le bit _).trans (by
        omega)

theorem binaryNumeralTerm_symbolCount_le (n : Nat) :
    termSymbolCount (binaryNumeralTerm n) ≤
      6 * Nat.size n + 1 := by
  simpa [binaryNumeralTerm, Nat.size_eq_bits_len] using
    binaryNumeralFold_symbolCount_le n.bits

/-- The exact `P(bound, formulaCode)` instance, with both parameters written as
short binary terms rather than Foundation's unary numerals. -/
noncomputable def efficientPostfixPAProofSentence
    (bound formulaCode : Nat) : LO.FirstOrder.ArithmeticSentence :=
  (efficientPostfixPAProofFormula.val)/[
    binaryNumeralTerm bound, binaryNumeralTerm formulaCode]

@[simp] theorem models_efficientPostfixPAProofSentence
    (bound formulaCode : Nat) :
    Nat↓[ℒₒᵣ] ⊧
        efficientPostfixPAProofSentence bound formulaCode ↔
      EfficientPostfixPAProofPredicate bound formulaCode := by
  simpa [efficientPostfixPAProofSentence, models_iff,
    Semiformula.eval_substs, Matrix.comp_vecCons',
    val_binaryNumeralTerm] using
      efficientPostfixPAProofFormula_spec bound formulaCode

theorem efficientPostfixPAProofPredicate_mono
    {smaller larger formulaCode : Nat}
    (hbound : smaller ≤ larger)
    (hproof :
      EfficientPostfixPAProofPredicate smaller formulaCode) :
    EfficientPostfixPAProofPredicate larger formulaCode := by
  rcases hproof with ⟨tokens, hlength, hcheck⟩
  exact ⟨tokens, hlength.trans hbound, hcheck⟩

def arithmeticFalsumCode : Nat :=
  Encodable.encode
    ((⊥ : LO.FirstOrder.ArithmeticSentence) :
      LO.FirstOrder.ArithmeticProposition)

/-- Pudlak's finite-consistency sentence on the exact postfix-length
coordinate: there is no PA proof of falsity of length at most `bound`. -/
noncomputable def pudlakFiniteConsistencySentence (bound : Nat) :
    LO.FirstOrder.ArithmeticSentence :=
  ∼efficientPostfixPAProofSentence bound arithmeticFalsumCode

theorem no_efficientPostfixPAProof_falsum (bound : Nat) :
    ¬ EfficientPostfixPAProofPredicate bound arithmeticFalsumCode := by
  rintro ⟨tokens, _, hcheck⟩
  have hderivation : Nonempty
      (F.PA ⊢!₂!
        (((⊥ : LO.FirstOrder.ArithmeticSentence) :
          LO.FirstOrder.ArithmeticProposition))) := by
    exact postfixPAProofChecks_sound
      (formula :=
        ((⊥ : LO.FirstOrder.ArithmeticSentence) :
          LO.FirstOrder.ArithmeticProposition))
      (by simpa [arithmeticFalsumCode] using hcheck)
  have hfalse :
      F.PA ⊢ (⊥ : LO.FirstOrder.ArithmeticSentence) :=
    (LO.FirstOrder.provable_iff_derivable2 (T := F.PA)).mpr
      hderivation
  exact LO.Entailment.Consistent.not_bot
    (𝓢 := F.PA) inferInstance hfalse

@[simp] theorem models_pudlakFiniteConsistencySentence
    (bound : Nat) :
    Nat↓[ℒₒᵣ] ⊧ pudlakFiniteConsistencySentence bound := by
  change
    Semiformula.EvalAux
      (LO.FirstOrder.Arithmetic.standardModel Nat)
      Empty.elim ![]
      (∼efficientPostfixPAProofSentence
        bound arithmeticFalsumCode)
  rw [Semiformula.EvalAux_neg]
  intro heval
  apply no_efficientPostfixPAProof_falsum bound
  apply (models_efficientPostfixPAProofSentence
    bound arithmeticFalsumCode).mp
  change
    Semiformula.EvalAux
      (LO.FirstOrder.Arithmetic.standardModel Nat)
      Empty.elim ![]
      (efficientPostfixPAProofSentence
        bound arithmeticFalsumCode)
  exact heval

end FoundationPudlakQuantitativeConditions

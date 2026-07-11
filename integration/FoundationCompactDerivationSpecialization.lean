import integration.FoundationCompactSyntaxTransformationCodeBounds

/-!
# Explicit specialization for concrete PA derivations

This file realizes universal instantiation inside Foundation's concrete
`Derivation2` calculus.  The construction is an actual proof object with a
fixed rule shape; no completeness call or proof-length witness is used for
the varying instance.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactDerivationSpecialization

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength
open FoundationCompactSyntaxTransformationCodeBounds

/-- A sequent containing at most four named formulas has a binary code bounded
by one cardinality header and four copies of their total formula-code size. -/
theorem binarySequentCode_length_le_four_formula_budget
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (first second third fourth : LO.FirstOrder.ArithmeticProposition)
    (hmem : ∀ formula ∈ Gamma,
      formula = first ∨ formula = second ∨
        formula = third ∨ formula = fourth) :
    (binarySequentCode Gamma).length <=
      (binaryNatCode 4).length +
        4 * ((binaryFormulaCode first).length +
          (binaryFormulaCode second).length +
          (binaryFormulaCode third).length +
          (binaryFormulaCode fourth).length) := by
  let formulaBudget :=
    (binaryFormulaCode first).length +
      (binaryFormulaCode second).length +
      (binaryFormulaCode third).length +
      (binaryFormulaCode fourth).length
  have hsubset : Gamma ⊆ {first, second, third, fourth} := by
    intro formula hformula
    rcases hmem formula hformula with h | h | h | h <;> simp [h]
  have hcardSet : ({first, second, third, fourth} :
      Finset LO.FirstOrder.ArithmeticProposition).card <= 4 := by
    have hfirst := Finset.card_insert_le first {second, third, fourth}
    have hsecond := Finset.card_insert_le second {third, fourth}
    have hthird := Finset.card_insert_le third {fourth}
    simp only [Finset.card_singleton] at hthird
    omega
  have hcard : Gamma.card <= 4 :=
    (Finset.card_le_card hsubset).trans hcardSet
  have hheader := binaryNatCode_length_mono hcard
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ Gamma) :
      (binaryFormulaCode formula).length <= formulaBudget := by
    rcases hmem formula hformulaMem with h | h | h | h <;>
      subst formula <;> simp [formulaBudget] <;> omega
  have hpayload :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        Gamma.card * formulaBudget := by
    simpa [nsmul_eq_mul] using
      Gamma.sum_le_card_nsmul
        (fun formula => (binaryFormulaCode formula).length)
        formulaBudget hformula
  have hpayloadBound :
      Gamma.sum (fun formula => (binaryFormulaCode formula).length) <=
        4 * formulaBudget :=
    hpayload.trans (Nat.mul_le_mul_right formulaBudget hcard)
  have hflat :
      (Gamma.toList.flatMap binaryFormulaCode).length =
        Gamma.sum (fun formula => (binaryFormulaCode formula).length) := by
    rw [List.length_flatMap]
    simp
  simp only [binarySequentCode, List.length_append, hflat]
  exact Nat.add_le_add hheader hpayloadBound

/-- Total syntax budget used by all four sequents in the specialization tree. -/
def specializationSyntaxBudget
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) : Nat :=
  (binaryFormulaCode (formula/[witness])).length +
    (binaryFormulaCode (∀⁰ formula)).length +
    (binaryFormulaCode (∃⁰ (∼formula))).length +
    (binaryFormulaCode ((∼formula)/[witness])).length

/-- Specialize a concrete PA proof of `forall x, formula x` at a closed term.
The emitted proof has the explicit shape `cut(wk(base), exs(closed))`. -/
def specializeDerivation
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.Derivation2 PA {formula/[witness]} := by
  apply LO.FirstOrder.Derivation2.cut (φ := ∀⁰ formula)
  · exact LO.FirstOrder.Derivation2.wk base (by simp)
  · rw [Semiformula.neg_all]
    apply LO.FirstOrder.Derivation2.exs (φ := ∼formula) (by simp) witness
    exact LO.FirstOrder.Derivation2.closed _ (formula/[witness])
      (by simp) (by simp)

/-- The specialization compiler erases to a checker-valid concrete tree. -/
theorem specializeDerivation_tree_valid
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (CheckedPAProofTree.ofDerivation
      (specializeDerivation base witness)).Valid :=
  CheckedPAProofTree.valid_ofDerivation _

@[simp] theorem specializeDerivation_tree_conclusion
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (CheckedPAProofTree.ofDerivation
      (specializeDerivation base witness)).conclusion =
        {formula/[witness]} := by
  simp

/-- Exact code-length accounting for the specialization proof object.  The
only recursive contribution is the already fixed `base` derivation. -/
theorem specializeDerivation_binaryProofLength_eq
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    let instanceFormula : LO.FirstOrder.ArithmeticProposition :=
      formula/[witness]
    let universalFormula : LO.FirstOrder.ArithmeticProposition :=
      ∀⁰ formula
    let existentialNegation : LO.FirstOrder.ArithmeticProposition :=
      ∃⁰ (∼formula)
    binaryProofLength (specializeDerivation base witness) =
      (binaryNatCode 9).length +
        (binarySequentCode {instanceFormula}).length +
        (binaryFormulaCode universalFormula).length +
        ((binaryNatCode 7).length +
          (binarySequentCode
            (insert universalFormula {instanceFormula})).length +
          binaryProofLength base) +
        ((binaryNatCode 6).length +
          (binarySequentCode
            (insert existentialNegation {instanceFormula})).length +
          (binaryFormulaCode (∼formula)).length +
          (binaryTermCode witness).length +
          ((binaryNatCode 0).length +
            (binarySequentCode
              (insert ((∼formula)/[witness])
                (insert existentialNegation {instanceFormula}))).length +
            (binaryFormulaCode instanceFormula).length)) := by
  simp [specializeDerivation, binaryProofLength, binaryDerivationCode]
  omega

/-- Structural length bound before estimating the four syntax transformations.
It exposes the fixed base proof as the only recursive proof contribution. -/
theorem specializeDerivation_binaryProofLength_le_syntaxBudget
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryProofLength (specializeDerivation base witness) <=
      binaryProofLength base + 128 +
        18 * specializationSyntaxBudget formula witness +
        (binaryFormulaCode (∼formula)).length +
        (binaryTermCode witness).length := by
  let instanceFormula : LO.FirstOrder.ArithmeticProposition :=
    formula/[witness]
  let universalFormula : LO.FirstOrder.ArithmeticProposition :=
    ∀⁰ formula
  let existentialNegation : LO.FirstOrder.ArithmeticProposition :=
    ∃⁰ (∼formula)
  let substitutedNegation : LO.FirstOrder.ArithmeticProposition :=
    (∼formula)/[witness]
  let syntaxBudget := specializationSyntaxBudget formula witness
  have hbudget : syntaxBudget =
      (binaryFormulaCode instanceFormula).length +
        (binaryFormulaCode universalFormula).length +
        (binaryFormulaCode existentialNegation).length +
        (binaryFormulaCode substitutedNegation).length := by
    rfl
  have hseq
      (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
      (hmem : ∀ candidate ∈ Gamma,
        candidate = instanceFormula ∨ candidate = universalFormula ∨
          candidate = existentialNegation ∨ candidate = substitutedNegation) :
      (binarySequentCode Gamma).length <=
        (binaryNatCode 4).length + 4 * syntaxBudget := by
    simpa [hbudget] using
      binarySequentCode_length_le_four_formula_budget Gamma
        instanceFormula universalFormula existentialNegation
        substitutedNegation hmem
  have hseqInstance := hseq {instanceFormula} (by simp)
  have hseqUniversal :=
    hseq (insert universalFormula {instanceFormula}) (by simp)
  have hseqExistential :=
    hseq (insert existentialNegation {instanceFormula}) (by simp)
  have hseqLeaf :=
    hseq (insert substitutedNegation
      (insert existentialNegation {instanceFormula})) (by simp)
  have htag0 : (binaryNatCode 0).length <= 16 := by decide
  have htag4 : (binaryNatCode 4).length <= 16 := by decide
  have htag6 : (binaryNatCode 6).length <= 16 := by decide
  have htag7 : (binaryNatCode 7).length <= 16 := by decide
  have htag9 : (binaryNatCode 9).length <= 16 := by decide
  have huniversal :
      (binaryFormulaCode universalFormula).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  have hinstance :
      (binaryFormulaCode instanceFormula).length <= syntaxBudget := by
    simp [syntaxBudget, hbudget]
    omega
  dsimp only [instanceFormula, universalFormula, existentialNegation,
    substitutedNegation] at hseqInstance hseqUniversal hseqExistential hseqLeaf huniversal hinstance
  rw [specializeDerivation_binaryProofLength_eq]
  change _ <= binaryProofLength base + 128 +
    18 * syntaxBudget + (binaryFormulaCode (∼formula)).length +
      (binaryTermCode witness).length
  omega

/-- The complete syntax budget is cubic in the input formula and closed-term
code lengths.  This discharges the varying part of universal instantiation. -/
theorem specializationSyntaxBudget_le_cubic
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    let scale := (binaryFormulaCode formula).length +
      (binaryTermCode witness).length + 1
    specializationSyntaxBudget formula witness <=
      64 * scale * scale * scale := by
  let formulaLength := (binaryFormulaCode formula).length
  let witnessLength := (binaryTermCode witness).length
  let scale := formulaLength + witnessLength + 1
  let negationLength := (binaryFormulaCode (∼formula)).length
  have hscalePositive : 1 <= scale := by
    simp [scale]
  have hformula : formulaLength <= scale := by
    simp [scale]
    omega
  have hformulaSucc : formulaLength + 1 <= scale := by
    simp [scale]
  have hwitness : witnessLength <= scale := by
    simp [scale]
    omega
  have hwitnessSucc : witnessLength + 1 <= scale := by
    simp [scale]
  have hnegation : negationLength <= 2 * formulaLength := by
    simpa [negationLength, formulaLength] using
      binaryFormulaCode_neg_length_le formula
  have hnegationScale : negationLength <= 2 * scale :=
    hnegation.trans (Nat.mul_le_mul_left 2 hformula)
  have hnegationSuccScale : negationLength + 1 <= 3 * scale := by
    omega
  have hinstance :=
    binaryFormulaCode_substitution_one_length_le formula witness
  have hinstanceCubic :
      (binaryFormulaCode (formula/[witness])).length <=
        3 * scale * scale * scale := by
    apply hinstance.trans
    exact Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul le_rfl hformulaSucc)
        hwitnessSucc)
      hformula
  have hnegatedInstance :=
    binaryFormulaCode_substitution_one_length_le (∼formula) witness
  have hnegatedInstanceCubic :
      (binaryFormulaCode ((∼formula)/[witness])).length <=
        18 * scale * scale * scale := by
    apply hnegatedInstance.trans
    calc
      3 * (negationLength + 1) * (witnessLength + 1) *
            negationLength <=
          3 * (3 * scale) * scale * (2 * scale) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul le_rfl hnegationSuccScale)
            hwitnessSucc)
          hnegationScale
      _ = 18 * scale * scale * scale := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have huniversal :
      (binaryFormulaCode (∀⁰ formula)).length <=
        formulaLength + 8 := by
    have htag : (binaryNatCode 6).length <= 8 := by decide
    simp only [binaryFormulaCode, List.length_append]
    omega
  have huniversalScale :
      (binaryFormulaCode (∀⁰ formula)).length <= 9 * scale :=
    huniversal.trans (by omega)
  have hexistentialNegation :
      (binaryFormulaCode (∃⁰ (∼formula))).length <=
        negationLength + 8 := by
    have htag : (binaryNatCode 7).length <= 8 := by decide
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hexistentialNegationScale :
      (binaryFormulaCode (∃⁰ (∼formula))).length <= 10 * scale :=
    hexistentialNegation.trans (by omega)
  have hscaleSquare : scale <= scale * scale := by
    calc
      scale = scale * 1 := by simp
      _ <= scale * scale := Nat.mul_le_mul_left scale hscalePositive
  have hscaleCube : scale <= scale * scale * scale :=
    hscaleSquare.trans <| by
      calc
        scale * scale = scale * scale * 1 := by simp
        _ <= scale * scale * scale :=
          Nat.mul_le_mul_left (scale * scale) hscalePositive
  let cube := scale * scale * scale
  have hinstanceCube :
      (binaryFormulaCode (formula/[witness])).length <= 3 * cube := by
    simpa [cube, Nat.mul_assoc] using hinstanceCubic
  have huniversalCube :
      (binaryFormulaCode (∀⁰ formula)).length <= 9 * cube :=
    huniversalScale.trans (Nat.mul_le_mul_left 9 hscaleCube)
  have hexistentialNegationCube :
      (binaryFormulaCode (∃⁰ (∼formula))).length <= 10 * cube :=
    hexistentialNegationScale.trans
      (Nat.mul_le_mul_left 10 hscaleCube)
  have hnegatedInstanceCube :
      (binaryFormulaCode ((∼formula)/[witness])).length <=
        18 * cube := by
    simpa [cube, Nat.mul_assoc] using hnegatedInstanceCubic
  have hcomponentSum :
      (binaryFormulaCode (formula/[witness])).length +
            (binaryFormulaCode (∀⁰ formula)).length +
            (binaryFormulaCode (∃⁰ (∼formula))).length +
            (binaryFormulaCode ((∼formula)/[witness])).length <=
        3 * cube + 9 * cube + 10 * cube + 18 * cube :=
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add hinstanceCube huniversalCube)
        hexistentialNegationCube)
      hnegatedInstanceCube
  change
    (binaryFormulaCode (formula/[witness])).length +
          (binaryFormulaCode (∀⁰ formula)).length +
          (binaryFormulaCode (∃⁰ (∼formula))).length +
          (binaryFormulaCode ((∼formula)/[witness])).length <=
      64 * scale * scale * scale
  calc
    _ <= 3 * cube + 9 * cube + 10 * cube + 18 * cube := hcomponentSum
    _ <= 64 * cube := by omega
    _ = 64 * scale * scale * scale := by
      simp [cube, Nat.mul_assoc]

/-- Final cubic bound for the explicit specialization proof compiler. -/
theorem specializeDerivation_binaryProofLength_le_cubic
    {formula : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (base : LO.FirstOrder.Derivation2 PA {∀⁰ formula})
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    let scale := (binaryFormulaCode formula).length +
      (binaryTermCode witness).length + 1
    binaryProofLength (specializeDerivation base witness) <=
      binaryProofLength base + 128 +
        2048 * scale * scale * scale := by
  let scale := (binaryFormulaCode formula).length +
    (binaryTermCode witness).length + 1
  have hstructure :=
    specializeDerivation_binaryProofLength_le_syntaxBudget base witness
  have hsyntax := specializationSyntaxBudget_le_cubic formula witness
  change specializationSyntaxBudget formula witness <=
    64 * scale * scale * scale at hsyntax
  have hnegation := binaryFormulaCode_neg_length_le formula
  have hformulaScale :
      (binaryFormulaCode formula).length <= scale := by
    simp [scale]
    omega
  have hnegationScale :
      (binaryFormulaCode (∼formula)).length <= 2 * scale :=
    hnegation.trans (Nat.mul_le_mul_left 2 hformulaScale)
  have hwitnessScale : (binaryTermCode witness).length <= scale := by
    simp [scale]
    omega
  have hscalePositive : 1 <= scale := by simp [scale]
  have hscaleSquare : scale <= scale * scale := by
    calc
      scale = scale * 1 := by simp
      _ <= scale * scale := Nat.mul_le_mul_left scale hscalePositive
  have hscaleCube : scale <= scale * scale * scale :=
    hscaleSquare.trans <| by
      calc
        scale * scale = scale * scale * 1 := by simp
        _ <= scale * scale * scale :=
          Nat.mul_le_mul_left (scale * scale) hscalePositive
  let cube := scale * scale * scale
  have hsyntaxCube : specializationSyntaxBudget formula witness <=
      64 * cube := by
    simpa [cube, Nat.mul_assoc] using hsyntax
  have hnegationCube :
      (binaryFormulaCode (∼formula)).length <= 2 * cube :=
    hnegationScale.trans (Nat.mul_le_mul_left 2 hscaleCube)
  have hwitnessCube : (binaryTermCode witness).length <= cube :=
    hwitnessScale.trans hscaleCube
  change binaryProofLength (specializeDerivation base witness) <=
    binaryProofLength base + 128 + 2048 * scale * scale * scale
  calc
    _ <= binaryProofLength base + 128 +
          18 * specializationSyntaxBudget formula witness +
          (binaryFormulaCode (∼formula)).length +
          (binaryTermCode witness).length := hstructure
    _ <= binaryProofLength base + 128 +
          18 * (64 * cube) + 2 * cube + cube := by omega
    _ <= binaryProofLength base + 128 + 2048 * cube := by omega
    _ = binaryProofLength base + 128 +
          2048 * scale * scale * scale := by
      simp [cube, Nat.mul_assoc]

#print axioms specializeDerivation
#print axioms specializeDerivation_tree_valid
#print axioms specializeDerivation_tree_conclusion
#print axioms specializeDerivation_binaryProofLength_eq
#print axioms binarySequentCode_length_le_four_formula_budget
#print axioms specializeDerivation_binaryProofLength_le_syntaxBudget
#print axioms specializationSyntaxBudget_le_cubic
#print axioms specializeDerivation_binaryProofLength_le_cubic

end FoundationCompactDerivationSpecialization

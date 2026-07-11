import integration.FoundationPudlakQuantitativeConditions

/-!
# Compact PA proof verifier

This parser reads the structural binary proof representation directly into
typed Foundation syntax.  It never constructs Foundation's nested numeric raw
proof code.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAProofVerifier

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions

def decodeManyVector {alpha : Type*}
    (decode : List Bool → Option (alpha × List Bool)) :
    (count : Nat) → List Bool →
      Option (List.Vector alpha count × List Bool)
  | 0, bits => some (List.Vector.nil, bits)
  | count + 1, bits => do
      let (head, bits) ← decode bits
      let (tail, bits) ← decodeManyVector decode count bits
      pure (head ::ᵥ tail, bits)

def decodeCompactTerm (arity : Nat) :
    Nat → List Bool →
      Option
        (LO.FirstOrder.ArithmeticSemiterm Nat arity × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => do
          let (index, bits) ← decodeBinaryNat bits
          if hindex : index < arity then
            pure (Semiterm.bvar ⟨index, hindex⟩, bits)
          else none
      | 1 => do
          let (freeIndex, bits) ← decodeBinaryNat bits
          pure (Semiterm.fvar freeIndex, bits)
      | 2 => do
          let (functionArity, bits) ← decodeBinaryNat bits
          let (functionCode, bits) ← decodeBinaryNat bits
          let functionSymbol ←
            (Encodable.decode₂ _ functionCode :
              Option (LO.FirstOrder.Language.Func
                ℒₒᵣ functionArity))
          let (arguments, bits) ←
            decodeManyVector
              (decodeCompactTerm arity fuel) functionArity bits
          pure (Semiterm.func functionSymbol arguments.get, bits)
      | _ => none

def decodeCompactFormula (arity : Nat) :
    Nat → List Bool →
      Option
        (LO.FirstOrder.ArithmeticSemiformula Nat arity × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      match tag with
      | 0 => do
          let (relationArity, bits) ← decodeBinaryNat bits
          let (relationCode, bits) ← decodeBinaryNat bits
          let relationSymbol ←
            (Encodable.decode₂ _ relationCode :
              Option (LO.FirstOrder.Language.Rel
                ℒₒᵣ relationArity))
          let (arguments, bits) ←
            decodeManyVector
              (decodeCompactTerm arity fuel) relationArity bits
          pure (Semiformula.rel relationSymbol arguments.get, bits)
      | 1 => do
          let (relationArity, bits) ← decodeBinaryNat bits
          let (relationCode, bits) ← decodeBinaryNat bits
          let relationSymbol ←
            (Encodable.decode₂ _ relationCode :
              Option (LO.FirstOrder.Language.Rel
                ℒₒᵣ relationArity))
          let (arguments, bits) ←
            decodeManyVector
              (decodeCompactTerm arity fuel) relationArity bits
          pure (Semiformula.nrel relationSymbol arguments.get, bits)
      | 2 => pure (⊤, bits)
      | 3 => pure (⊥, bits)
      | 4 => do
          let (left, bits) ← decodeCompactFormula arity fuel bits
          let (right, bits) ← decodeCompactFormula arity fuel bits
          pure (left ⋏ right, bits)
      | 5 => do
          let (left, bits) ← decodeCompactFormula arity fuel bits
          let (right, bits) ← decodeCompactFormula arity fuel bits
          pure (left ⋎ right, bits)
      | 6 => do
          let (body, bits) ← decodeCompactFormula (arity + 1) fuel bits
          pure (∀⁰ body, bits)
      | 7 => do
          let (body, bits) ← decodeCompactFormula (arity + 1) fuel bits
          pure (∃⁰ body, bits)
      | _ => none

def decodeCompactSequent
    (fuel : Nat) (bits : List Bool) :
    Option
      (Finset LO.FirstOrder.ArithmeticProposition × List Bool) := do
  let (cardinality, bits) ← decodeBinaryNat bits
  let (formulas, bits) ←
    decodeManyVector
      (decodeCompactFormula 0 fuel) cardinality bits
  pure (formulas.toList.toFinset, bits)

def propositionToSentence
    (formula : LO.FirstOrder.ArithmeticProposition) :
    Option LO.FirstOrder.ArithmeticSentence :=
  if hclosed : formula.freeVariables = ∅ then
    some (formula.toEmpty hclosed)
  else none

def decodeCompactProof :
    Nat → List Bool → Option (CheckedPAProofTree × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) ← decodeBinaryNat bits
      let (Gamma, bits) ← decodeCompactSequent fuel bits
      match tag with
      | 0 => do
          let (formula, bits) ← decodeCompactFormula 0 fuel bits
          pure (.closed Gamma formula, bits)
      | 1 => do
          let (formula, bits) ← decodeCompactFormula 0 fuel bits
          let sigma ← propositionToSentence formula
          pure (.axm Gamma sigma, bits)
      | 2 => pure (.verum Gamma, bits)
      | 3 => do
          let (leftFormula, bits) ← decodeCompactFormula 0 fuel bits
          let (rightFormula, bits) ← decodeCompactFormula 0 fuel bits
          let (left, bits) ← decodeCompactProof fuel bits
          let (right, bits) ← decodeCompactProof fuel bits
          pure (.and Gamma leftFormula rightFormula left right, bits)
      | 4 => do
          let (leftFormula, bits) ← decodeCompactFormula 0 fuel bits
          let (rightFormula, bits) ← decodeCompactFormula 0 fuel bits
          let (premise, bits) ← decodeCompactProof fuel bits
          pure (.or Gamma leftFormula rightFormula premise, bits)
      | 5 => do
          let (formula, bits) ← decodeCompactFormula 1 fuel bits
          let (premise, bits) ← decodeCompactProof fuel bits
          pure (.all Gamma formula premise, bits)
      | 6 => do
          let (formula, bits) ← decodeCompactFormula 1 fuel bits
          let (witness, bits) ← decodeCompactTerm 0 fuel bits
          let (premise, bits) ← decodeCompactProof fuel bits
          pure (.exs Gamma formula witness premise, bits)
      | 7 => do
          let (premise, bits) ← decodeCompactProof fuel bits
          pure (.wk Gamma premise, bits)
      | 8 => do
          let (premise, bits) ← decodeCompactProof fuel bits
          pure (.shift Gamma premise, bits)
      | 9 => do
          let (formula, bits) ← decodeCompactFormula 0 fuel bits
          let (left, bits) ← decodeCompactProof fuel bits
          let (right, bits) ← decodeCompactProof fuel bits
          pure (.cut Gamma formula left right, bits)
      | _ => none

def decodeCompactPackedProof
    (code : Nat) : Option CheckedPAProofTree := do
  let bits := code.bits
  guard (bits.getLast? = some true)
  let payload := bits.dropLast
  let (tree, suffix) ←
    decodeCompactProof (payload.length + 1) payload
  guard suffix.isEmpty
  pure tree

theorem decodeManyVector_toList_flatMap_append
    {alpha : Type*}
    (decode : List Bool → Option (alpha × List Bool))
    (encode : alpha → List Bool)
    {count : Nat} (items : List.Vector alpha count)
    (suffix : List Bool)
    (hdecode : ∀ item, item ∈ items.toList → ∀ rest,
      decode (encode item ++ rest) = some (item, rest)) :
    decodeManyVector decode count
        (items.toList.flatMap encode ++ suffix) =
      some (items, suffix) := by
  induction count with
  | zero =>
      have hitems : items = List.Vector.nil := Subsingleton.elim _ _
      subst hitems
      simp [decodeManyVector]
  | succ count ih =>
      obtain ⟨head, tail, rfl⟩ := List.Vector.exists_eq_cons items
      simp only [List.Vector.toList_cons, List.flatMap_cons]
      rw [decodeManyVector, List.append_assoc,
        hdecode head (by simp)
          (tail.toList.flatMap encode ++ suffix)]
      simp [ih tail (fun item hitem rest ↦
        hdecode item (by simp [hitem]) rest)]

theorem decodeCompactTerm_binaryTermCode_append
    {arity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (fuel : Nat) (hfuel : termSymbolCount term < fuel)
    (suffix : List Bool) :
    decodeCompactTerm arity fuel
        (binaryTermCode term ++ suffix) =
      some (term, suffix) := by
  induction term generalizing fuel suffix with
  | bvar index =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryTermCode, decodeCompactTerm, index.isLt]
  | fvar freeIndex =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryTermCode, decodeCompactTerm]
  | func functionSymbol arguments ih =>
      cases fuel with
      | zero => simp [termSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [termSymbolCount] at hfuel
            omega
          let argumentVector :
              List.Vector _ _ :=
            List.Vector.ofFn arguments
          have hmany :=
            decodeManyVector_toList_flatMap_append
              (decodeCompactTerm _ fuel)
              binaryTermCode argumentVector suffix
              (fun child hchildMem rest ↦ by
                rcases (List.mem_ofFn' arguments child).mp
                    (by simpa [argumentVector] using hchildMem) with
                  ⟨i, rfl⟩
                exact ih i fuel (hchild i) rest)
          have hmany' :
              decodeManyVector (decodeCompactTerm _ fuel) _
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some (argumentVector, suffix) := by
            simpa [argumentVector, List.flatMap,
              Function.comp_def] using hmany
          simp [binaryTermCode, decodeCompactTerm, hmany',
            argumentVector]
          funext i
          simp

theorem decodeCompactFormula_binaryFormulaCode_append
    {arity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat arity)
    (fuel : Nat) (hfuel : formulaSymbolCount formula < fuel)
    (suffix : List Bool) :
    decodeCompactFormula arity fuel
        (binaryFormulaCode formula ++ suffix) =
      some (formula, suffix) := by
  induction formula generalizing fuel suffix with
  | rel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [formulaSymbolCount] at hfuel
            omega
          let argumentVector :
              List.Vector _ _ :=
            List.Vector.ofFn arguments
          have hmany :=
            decodeManyVector_toList_flatMap_append
              (decodeCompactTerm _ fuel)
              binaryTermCode argumentVector suffix
              (fun child hchildMem rest ↦ by
                rcases (List.mem_ofFn' arguments child).mp
                    (by simpa [argumentVector] using hchildMem) with
                  ⟨i, rfl⟩
                exact decodeCompactTerm_binaryTermCode_append
                  (arguments i) fuel (hchild i) rest)
          have hmany' :
              decodeManyVector (decodeCompactTerm _ fuel) _
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some (argumentVector, suffix) := by
            simpa [argumentVector, List.flatMap,
              Function.comp_def] using hmany
          simp [binaryFormulaCode, decodeCompactFormula, hmany',
            argumentVector]
          funext i
          simp
  | nrel relationSymbol arguments =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hchild (i) :
              termSymbolCount (arguments i) < fuel := by
            have hle :
                termSymbolCount (arguments i) ≤
                  Finset.univ.sum
                    (fun j ↦ termSymbolCount (arguments j)) :=
              Finset.single_le_sum
                (f := fun j ↦ termSymbolCount (arguments j))
                (s := Finset.univ)
                (fun j _ ↦ Nat.zero_le
                  (termSymbolCount (arguments j)))
                (Finset.mem_univ i)
            simp [formulaSymbolCount] at hfuel
            omega
          let argumentVector :
              List.Vector _ _ :=
            List.Vector.ofFn arguments
          have hmany :=
            decodeManyVector_toList_flatMap_append
              (decodeCompactTerm _ fuel)
              binaryTermCode argumentVector suffix
              (fun child hchildMem rest ↦ by
                rcases (List.mem_ofFn' arguments child).mp
                    (by simpa [argumentVector] using hchildMem) with
                  ⟨i, rfl⟩
                exact decodeCompactTerm_binaryTermCode_append
                  (arguments i) fuel (hchild i) rest)
          have hmany' :
              decodeManyVector (decodeCompactTerm _ fuel) _
                  ((List.ofFn fun i ↦
                    binaryTermCode (arguments i)).flatten ++ suffix) =
                some (argumentVector, suffix) := by
            simpa [argumentVector, List.flatMap,
              Function.comp_def] using hmany
          simp [binaryFormulaCode, decodeCompactFormula, hmany',
            argumentVector]
          funext i
          simp
  | verum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryFormulaCode, decodeCompactFormula]
          rfl
  | falsum =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          simp [binaryFormulaCode, decodeCompactFormula]
          rfl
  | and left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hleft : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hright : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeCompactFormula,
            ihLeft fuel hleft, ihRight fuel hright]
          rfl
  | or left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hleft : formulaSymbolCount left < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          have hright : formulaSymbolCount right < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeCompactFormula,
            ihLeft fuel hleft, ihRight fuel hright]
          rfl
  | all body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hbody : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeCompactFormula,
            ih fuel hbody]
          rfl
  | exs body ih =>
      cases fuel with
      | zero => simp [formulaSymbolCount] at hfuel
      | succ fuel =>
          have hbody : formulaSymbolCount body < fuel := by
            simp [formulaSymbolCount] at hfuel
            omega
          simp [binaryFormulaCode, decodeCompactFormula,
            ih fuel hbody]
          rfl

theorem decodeCompactSequent_binarySequentCode_append
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (fuel : Nat) (hfuel : sequentSymbolCount Gamma < fuel)
    (suffix : List Bool) :
    decodeCompactSequent fuel
        (binarySequentCode Gamma ++ suffix) =
      some (Gamma, suffix) := by
  let formulaVector :
      List.Vector LO.FirstOrder.ArithmeticProposition Gamma.card :=
    ⟨Gamma.toList, by simp⟩
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ formulaVector.toList) :
      formulaSymbolCount formula < fuel := by
    have hmem : formula ∈ Gamma := by
      simpa [formulaVector] using hformulaMem
    have hle :
        formulaSymbolCount formula ≤
          Gamma.sum formulaSymbolCount :=
      Finset.single_le_sum
        (f := formulaSymbolCount) (s := Gamma)
        (fun item _ ↦ Nat.zero_le (formulaSymbolCount item)) hmem
    exact hle.trans_lt hfuel
  have hmany :=
    decodeManyVector_toList_flatMap_append
      (decodeCompactFormula 0 fuel)
      binaryFormulaCode formulaVector suffix
      (fun formula hformulaMem rest ↦
        decodeCompactFormula_binaryFormulaCode_append
          formula fuel (hformula formula hformulaMem) rest)
  have hmany' :
      decodeManyVector (decodeCompactFormula 0 fuel) Gamma.card
          (Gamma.toList.flatMap binaryFormulaCode ++ suffix) =
        some (formulaVector, suffix) := by
    simpa [formulaVector] using hmany
  simp [binarySequentCode, decodeCompactSequent, hmany',
    formulaVector]

theorem decodeCompactProof_binaryCode_append
    (tree : CheckedPAProofTree) (fuel : Nat)
    (hfuel : tree.parseWeight < fuel) (suffix : List Bool) :
    decodeCompactProof fuel (tree.binaryCode ++ suffix) =
      some (tree, suffix) := by
  induction tree generalizing fuel suffix with
  | closed Gamma formula =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula]
  | axm Gamma sigma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula :
              formulaSymbolCount
                  (Rewriting.emb sigma :
                    LO.FirstOrder.ArithmeticProposition) < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              (Rewriting.emb sigma :
                LO.FirstOrder.ArithmeticProposition) fuel hformula,
            propositionToSentence]
  | verum Gamma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleftFormula :
              formulaSymbolCount leftFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hrightFormula :
              formulaSymbolCount rightFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ihLeft fuel hleft, ihRight fuel hright]
  | or Gamma leftFormula rightFormula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleftFormula :
              formulaSymbolCount leftFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hrightFormula :
              formulaSymbolCount rightFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ih fuel hpremise]
  | all Gamma formula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ih fuel hpremise]
  | exs Gamma formula witness premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hwitness : termSymbolCount witness < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            decodeCompactTerm_binaryTermCode_append
              witness fuel hwitness,
            ih fuel hpremise]
  | wk Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            ih fuel hpremise]
  | shift Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            ih fuel hpremise]
  | cut Gamma formula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [CheckedPAProofTree.binaryCode, decodeCompactProof,
            decodeCompactSequent_binarySequentCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ihLeft fuel hleft, ihRight fuel hright]

theorem decodeCompactProof_binaryCode
    (tree : CheckedPAProofTree) :
    decodeCompactProof (tree.binaryCode.length + 1)
        tree.binaryCode = some (tree, []) := by
  have hfuel : tree.parseWeight < tree.binaryCode.length + 1 := by
    have hweight := tree.parseWeight_le_binaryLength
    simp only [CheckedPAProofTree.binaryLength] at hweight
    omega
  simpa using decodeCompactProof_binaryCode_append
    tree (tree.binaryCode.length + 1) hfuel []

@[simp] theorem decodeCompactPackedProof_packedCode
    (tree : CheckedPAProofTree) :
    decodeCompactPackedProof tree.packedCode = some tree := by
  simp [decodeCompactPackedProof, CheckedPAProofTree.packedCode,
    decodeCompactProof_binaryCode]

/-- The compact packed checker.  Its witness and length coordinate contain no
Foundation raw proof code. -/
def CompactPackedPAProofChecks
    (code formulaCode : Nat) : Prop :=
  ∃ (tree : CheckedPAProofTree)
      (formula : LO.FirstOrder.ArithmeticProposition),
    decodeCompactPackedProof code = some tree ∧
      structurallyValid tree ∧
      tree.conclusion = {formula} ∧
      compactFormulaCode formula = formulaCode

def EfficientCompactPAProofPredicate
    (bound formulaCode : Nat) : Prop :=
  ∃ code : Nat,
    packedPayloadLength code ≤ bound ∧
      CompactPackedPAProofChecks code formulaCode

theorem compactTree_checks
    (tree : CheckedPAProofTree)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (hvalid : structurallyValid tree)
    (hconclusion : tree.conclusion = {formula}) :
    CompactPackedPAProofChecks tree.packedCode
      (compactFormulaCode formula) := by
  exact ⟨tree, formula, by simp, hvalid, hconclusion, rfl⟩

theorem compactPAProofPredicate_to_efficientCoded
    {bound : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hproof : CompactPAProofPredicate bound formula) :
    EfficientCompactPAProofPredicate bound
      (compactFormulaCode formula) := by
  rcases hproof with ⟨tree, hlength, hvalid, hconclusion⟩
  refine ⟨tree.packedCode, ?_,
    compactTree_checks tree formula hvalid hconclusion⟩
  simpa [packedPayloadLength] using hlength

theorem derivation_to_efficientCompactPAProofPredicate
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (derivation : LO.FirstOrder.Derivation2 PA Gamma)
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hconclusion : Gamma = {formula}) :
    EfficientCompactPAProofPredicate
      (binaryProofLength derivation)
      (compactFormulaCode formula) :=
  compactPAProofPredicate_to_efficientCoded
    (derivation_to_compactPAProofPredicate derivation hconclusion)

theorem CompactPackedPAProofChecks.toDerivation
    {code : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hcheck : CompactPackedPAProofChecks code
      (compactFormulaCode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  rcases hcheck with
    ⟨tree, decodedFormula, _, hvalid, hconclusion, hcode⟩
  have hformula : decodedFormula = formula :=
    compactFormulaCode_injective hcode
  subst hformula
  rcases structurallyValid_toDerivation tree hvalid with ⟨derivation⟩
  exact ⟨LO.FirstOrder.Derivation2.cast derivation hconclusion⟩

theorem EfficientCompactPAProofPredicate.toDerivation
    {bound : Nat}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hproof : EfficientCompactPAProofPredicate bound
      (compactFormulaCode formula)) :
    Nonempty (LO.FirstOrder.Derivation2 PA {formula}) := by
  rcases hproof with ⟨code, _, hcheck⟩
  exact hcheck.toDerivation

theorem EfficientCompactPAProofPredicate.mono
    {smaller larger formulaCode : Nat}
    (hbound : smaller ≤ larger)
    (hproof : EfficientCompactPAProofPredicate
      smaller formulaCode) :
    EfficientCompactPAProofPredicate larger formulaCode := by
  rcases hproof with ⟨code, hlength, hcheck⟩
  exact ⟨code, hlength.trans hbound, hcheck⟩

end FoundationCompactPAProofVerifier

import integration.FoundationCompactVerifierFormulaListChecks

/-!
# List-preserving decoder for compact PA proof trees

The original decoder immediately quotients each displayed sequent to a
`Finset`.  This equivalent syntax retains the decoded list, allowing every
membership, inclusion, and extensional-equality check to use the explicit
costed routines from the preceding layer.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofDecoder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier

inductive ListedCheckedPAProofTree where
  | closed
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticProposition)
  | axm
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (sentence : LO.FirstOrder.ArithmeticSentence)
  | verum
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
  | and
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
      (left right : ListedCheckedPAProofTree)
  | or
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
      (premise : ListedCheckedPAProofTree)
  | all
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (premise : ListedCheckedPAProofTree)
  | exs
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (premise : ListedCheckedPAProofTree)
  | wk
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (premise : ListedCheckedPAProofTree)
  | shift
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (premise : ListedCheckedPAProofTree)
  | cut
      (Gamma : List LO.FirstOrder.ArithmeticProposition)
      (formula : LO.FirstOrder.ArithmeticProposition)
      (left right : ListedCheckedPAProofTree)

def ListedCheckedPAProofTree.conclusionList :
    ListedCheckedPAProofTree ->
      List LO.FirstOrder.ArithmeticProposition
  | .closed Gamma _ => Gamma
  | .axm Gamma _ => Gamma
  | .verum Gamma => Gamma
  | .and Gamma _ _ _ _ => Gamma
  | .or Gamma _ _ _ => Gamma
  | .all Gamma _ _ => Gamma
  | .exs Gamma _ _ _ => Gamma
  | .wk Gamma _ => Gamma
  | .shift Gamma _ => Gamma
  | .cut Gamma _ _ _ => Gamma

def ListedCheckedPAProofTree.toChecked :
    ListedCheckedPAProofTree -> CheckedPAProofTree
  | .closed Gamma formula => .closed Gamma.toFinset formula
  | .axm Gamma sentence => .axm Gamma.toFinset sentence
  | .verum Gamma => .verum Gamma.toFinset
  | .and Gamma leftFormula rightFormula left right =>
      .and Gamma.toFinset leftFormula rightFormula
        left.toChecked right.toChecked
  | .or Gamma leftFormula rightFormula premise =>
      .or Gamma.toFinset leftFormula rightFormula premise.toChecked
  | .all Gamma formula premise =>
      .all Gamma.toFinset formula premise.toChecked
  | .exs Gamma formula witness premise =>
      .exs Gamma.toFinset formula witness premise.toChecked
  | .wk Gamma premise => .wk Gamma.toFinset premise.toChecked
  | .shift Gamma premise => .shift Gamma.toFinset premise.toChecked
  | .cut Gamma formula left right =>
      .cut Gamma.toFinset formula left.toChecked right.toChecked

@[simp] theorem ListedCheckedPAProofTree.toChecked_conclusion
    (tree : ListedCheckedPAProofTree) :
    tree.toChecked.conclusion = tree.conclusionList.toFinset := by
  cases tree <;>
    rfl

def decodeCompactSequentList
    (fuel : Nat) (bits : List Bool) :
    Option
      (List LO.FirstOrder.ArithmeticProposition × List Bool) := do
  let (cardinality, bits) <- decodeBinaryNat bits
  let (formulas, bits) <-
    decodeManyVector (decodeCompactFormula 0 fuel) cardinality bits
  pure (formulas.toList, bits)

theorem decodeCompactSequentList_toFinset
    {fuel : Nat} {bits suffix : List Bool}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    (hdecode : decodeCompactSequentList fuel bits = some (Gamma, suffix)) :
    decodeCompactSequent fuel bits = some (Gamma.toFinset, suffix) := by
  cases hcardinality : decodeBinaryNat bits with
  | none => simp [decodeCompactSequentList, hcardinality] at hdecode
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      cases hformulas :
          decodeManyVector (decodeCompactFormula 0 fuel) cardinality
            afterCardinality with
      | none =>
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, afterFormulas⟩
          simp [decodeCompactSequentList, hcardinality, hformulas] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          simp [decodeCompactSequent, hcardinality, hformulas]

def decodeCompactListedProof :
    Nat -> List Bool -> Option (ListedCheckedPAProofTree × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (tag, bits) <- decodeBinaryNat bits
      let (Gamma, bits) <- decodeCompactSequentList fuel bits
      match tag with
      | 0 => do
          let (formula, bits) <- decodeCompactFormula 0 fuel bits
          pure (.closed Gamma formula, bits)
      | 1 => do
          let (formula, bits) <- decodeCompactFormula 0 fuel bits
          let sentence <- propositionToSentence formula
          pure (.axm Gamma sentence, bits)
      | 2 => pure (.verum Gamma, bits)
      | 3 => do
          let (leftFormula, bits) <- decodeCompactFormula 0 fuel bits
          let (rightFormula, bits) <- decodeCompactFormula 0 fuel bits
          let (left, bits) <- decodeCompactListedProof fuel bits
          let (right, bits) <- decodeCompactListedProof fuel bits
          pure (.and Gamma leftFormula rightFormula left right, bits)
      | 4 => do
          let (leftFormula, bits) <- decodeCompactFormula 0 fuel bits
          let (rightFormula, bits) <- decodeCompactFormula 0 fuel bits
          let (premise, bits) <- decodeCompactListedProof fuel bits
          pure (.or Gamma leftFormula rightFormula premise, bits)
      | 5 => do
          let (formula, bits) <- decodeCompactFormula 1 fuel bits
          let (premise, bits) <- decodeCompactListedProof fuel bits
          pure (.all Gamma formula premise, bits)
      | 6 => do
          let (formula, bits) <- decodeCompactFormula 1 fuel bits
          let (witness, bits) <- decodeCompactTerm 0 fuel bits
          let (premise, bits) <- decodeCompactListedProof fuel bits
          pure (.exs Gamma formula witness premise, bits)
      | 7 => do
          let (premise, bits) <- decodeCompactListedProof fuel bits
          pure (.wk Gamma premise, bits)
      | 8 => do
          let (premise, bits) <- decodeCompactListedProof fuel bits
          pure (.shift Gamma premise, bits)
      | 9 => do
          let (formula, bits) <- decodeCompactFormula 0 fuel bits
          let (left, bits) <- decodeCompactListedProof fuel bits
          let (right, bits) <- decodeCompactListedProof fuel bits
          pure (.cut Gamma formula left right, bits)
      | _ => none

end FoundationCompactListedProofDecoder

import integration.FoundationCompactCertificateTokenMachine

/-!
# Pure numeric fixed PA-axiom sentence table

The 22 non-induction PA-certificate tags are converted directly to canonical
sentence-token values.  Runtime inputs and outputs contain only naturals and
lists of naturals.  Function and relation extensionality dispatch on the
explicit ordered-ring arity/symbol-code pairs; no typed syntax is an external
input to the numeric function.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFixedPAAxiomSentence

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate

def compactSentenceTokens
    (sentence : LO.FirstOrder.ArithmeticSentence) : List Nat :=
  compactArithmeticFormulaTokens
    (Rewriting.emb sentence : LO.FirstOrder.ArithmeticProposition)

def compactFunctionExtSentenceTokens
    (parameters : Nat × Nat) : Option (List Nat) :=
  if parameters.1 = 0 then
    if parameters.2 = 0 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.zero))
    else if parameters.2 = 1 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.one))
    else
      none
  else if parameters.1 = 2 then
    if parameters.2 = 0 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.add))
    else if parameters.2 = 1 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.mul))
    else
      none
  else
    none

theorem compactFunctionExtSentenceTokens_primrec :
    Primrec compactFunctionExtSentenceTokens := by
  have harity0 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.1 = 0) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have harity2 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.1 = 2) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 2)
  have hcode0 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcode1 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.2 = 1) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hnone : Primrec (fun _parameters : Nat × Nat =>
      (none : Option (List Nat))) := Primrec.const none
  have hzero : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.zero))) :=
    Primrec.const _
  have hone : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.one))) :=
    Primrec.const _
  have hadd : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.add))) :=
    Primrec.const _
  have hmul : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt Language.ORing.Func.mul))) :=
    Primrec.const _
  exact
    (Primrec.ite harity0
      (Primrec.ite hcode0 hzero (Primrec.ite hcode1 hone hnone))
      (Primrec.ite harity2
        (Primrec.ite hcode0 hadd (Primrec.ite hcode1 hmul hnone))
        hnone)).of_eq fun parameters => by
          simp [compactFunctionExtSentenceTokens]

theorem compactFunctionExtSentenceTokens_encode
    {arity : Nat}
    (functionSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Func arity) :
    compactFunctionExtSentenceTokens
        (arity, Encodable.encode functionSymbol) =
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.funcExt functionSymbol)) := by
  match arity, functionSymbol with
  | 0, Language.ORing.Func.zero => rfl
  | 0, Language.ORing.Func.one => rfl
  | 2, Language.ORing.Func.add => rfl
  | 2, Language.ORing.Func.mul => rfl

def compactRelationExtSentenceTokens
    (parameters : Nat × Nat) : Option (List Nat) :=
  if parameters.1 = 2 then
    if parameters.2 = 0 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.eq))
    else if parameters.2 = 1 then
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.lt))
    else
      none
  else
    none

theorem compactRelationExtSentenceTokens_primrec :
    Primrec compactRelationExtSentenceTokens := by
  have harity2 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.1 = 2) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 2)
  have hcode0 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hcode1 : PrimrecPred (fun parameters : Nat × Nat =>
      parameters.2 = 1) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have hnone : Primrec (fun _parameters : Nat × Nat =>
      (none : Option (List Nat))) := Primrec.const none
  have heq : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.eq))) :=
    Primrec.const _
  have hlt : Primrec (fun _parameters : Nat × Nat =>
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt Language.ORing.Rel.lt))) :=
    Primrec.const _
  exact
    (Primrec.ite harity2
      (Primrec.ite hcode0 heq (Primrec.ite hcode1 hlt hnone))
      hnone).of_eq fun parameters => by
        simp [compactRelationExtSentenceTokens]

theorem compactRelationExtSentenceTokens_encode
    {arity : Nat}
    (relationSymbol :
      (ℒₒᵣ : LO.FirstOrder.Language).Rel arity) :
    compactRelationExtSentenceTokens
        (arity, Encodable.encode relationSymbol) =
      some (compactSentenceTokens
        (LO.FirstOrder.Theory.Eq.relExt relationSymbol)) := by
  match arity, relationSymbol with
  | 2, Language.ORing.Rel.eq => rfl
  | 2, Language.ORing.Rel.lt => rfl

def compactFixedPAAxiomSentenceBaseTable :
    List (Option (List Nat)) :=
  [ some (compactSentenceTokens (LO.FirstOrder.Theory.Eq.refl ℒₒᵣ)),
    some (compactSentenceTokens (LO.FirstOrder.Theory.Eq.symm ℒₒᵣ)),
    some (compactSentenceTokens (LO.FirstOrder.Theory.Eq.trans ℒₒᵣ)),
    none,
    none,
    some (compactSentenceTokens PeanoMinus.Axiom.addZero),
    some (compactSentenceTokens PeanoMinus.Axiom.addAssoc),
    some (compactSentenceTokens PeanoMinus.Axiom.addComm),
    some (compactSentenceTokens PeanoMinus.Axiom.addEqOfLt),
    some (compactSentenceTokens PeanoMinus.Axiom.zeroLe),
    some (compactSentenceTokens PeanoMinus.Axiom.zeroLtOne),
    some (compactSentenceTokens PeanoMinus.Axiom.oneLeOfZeroLt),
    some (compactSentenceTokens PeanoMinus.Axiom.addLtAdd),
    some (compactSentenceTokens PeanoMinus.Axiom.mulZero),
    some (compactSentenceTokens PeanoMinus.Axiom.mulOne),
    some (compactSentenceTokens PeanoMinus.Axiom.mulAssoc),
    some (compactSentenceTokens PeanoMinus.Axiom.mulComm),
    some (compactSentenceTokens PeanoMinus.Axiom.mulLtMul),
    some (compactSentenceTokens PeanoMinus.Axiom.distr),
    some (compactSentenceTokens PeanoMinus.Axiom.ltIrrefl),
    some (compactSentenceTokens PeanoMinus.Axiom.ltTrans),
    some (compactSentenceTokens PeanoMinus.Axiom.ltTri) ]

def compactFixedPAAxiomSentenceTable
    (parameters : Nat × Nat) : List (Option (List Nat)) :=
  (compactFixedPAAxiomSentenceBaseTable.set 3
      (compactFunctionExtSentenceTokens parameters)).set 4
    (compactRelationExtSentenceTokens parameters)

theorem compactFixedPAAxiomSentenceTable_primrec :
    Primrec compactFixedPAAxiomSentenceTable := by
  have hbase : Primrec (fun _parameters : Nat × Nat =>
      compactFixedPAAxiomSentenceBaseTable) := Primrec.const _
  have hsetThree : Primrec (fun parameters : Nat × Nat =>
      compactFixedPAAxiomSentenceBaseTable.set 3
        (compactFunctionExtSentenceTokens parameters)) :=
    Primrec.list_set.comp hbase
      (Primrec.pair (Primrec.const 3)
        compactFunctionExtSentenceTokens_primrec)
  exact
    (Primrec.list_set.comp hsetThree
      (Primrec.pair (Primrec.const 4)
        compactRelationExtSentenceTokens_primrec)).of_eq
      fun parameters => by rfl

def compactOptionJoin
    (value : Option (Option (List Nat))) : Option (List Nat) :=
  value.join

theorem compactOptionJoin_primrec : Primrec compactOptionJoin := by
  exact
    (Primrec.option_casesOn Primrec.id
      (Primrec.const none) Primrec₂.right).of_eq fun value => by
        cases value <;> rfl

def compactOptionListGet
    (values : List (Option (List Nat))) (index : Nat) :
    Option (Option (List Nat)) :=
  values[index]?

theorem compactOptionListGet_primrec :
    Primrec₂ compactOptionListGet := by
  exact Primrec.list_getElem?

def compactFixedPAAxiomSentenceTokens
    (tag : Nat) (parameters : Nat × Nat) : Option (List Nat) :=
  compactOptionJoin
    (compactOptionListGet (compactFixedPAAxiomSentenceTable parameters) tag)

theorem compactFixedPAAxiomSentenceTokens_primrec :
    Primrec₂ compactFixedPAAxiomSentenceTokens := by
  apply Primrec₂.mk
  let Input := Nat × (Nat × Nat)
  have htable : Primrec (fun input : Input =>
      compactFixedPAAxiomSentenceTable input.2) :=
    compactFixedPAAxiomSentenceTable_primrec.comp Primrec.snd
  have hlookup : Primrec (fun input : Input =>
      compactOptionListGet
        (compactFixedPAAxiomSentenceTable input.2) input.1) :=
    compactOptionListGet_primrec.comp htable Primrec.fst
  exact
    (compactOptionJoin_primrec.comp hlookup).of_eq fun input => by rfl

def FixedPAAxiomCertificate : PAAxiomCertificate -> Prop
  | .induction _ => False
  | _ => True

theorem compactFixedPAAxiomSentenceTokens_canonical
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    compactFixedPAAxiomSentenceTokens
        (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate),
          compactTokenAt 2 (compactPAAxiomCertificateTokens certificate)) =
      some (compactSentenceTokens certificate.sentence) := by
  cases certificate with
  | eqFuncExt functionSymbol =>
      simpa [compactPAAxiomCertificateTokens, compactTokenAt,
        compactFixedPAAxiomSentenceTokens,
        compactOptionJoin,
        compactOptionListGet,
        compactFixedPAAxiomSentenceTable,
        compactFixedPAAxiomSentenceBaseTable,
        PAAxiomCertificate.sentence] using
          compactFunctionExtSentenceTokens_encode functionSymbol
  | eqRelExt relationSymbol =>
      simpa [compactPAAxiomCertificateTokens, compactTokenAt,
        compactFixedPAAxiomSentenceTokens,
        compactOptionJoin,
        compactOptionListGet,
        compactFixedPAAxiomSentenceTable,
        compactFixedPAAxiomSentenceBaseTable,
        PAAxiomCertificate.sentence] using
          compactRelationExtSentenceTokens_encode relationSymbol
  | induction body =>
      simp [FixedPAAxiomCertificate] at hfixed
  | eqRefl | eqSymm | eqTrans | addZero | addAssoc | addComm |
      addEqOfLt | zeroLe | zeroLtOne | oneLeOfZeroLt | addLtAdd |
      mulZero | mulOne | mulAssoc | mulComm | mulLtMul | distr |
      ltIrrefl | ltTrans | ltTri =>
      simp [compactPAAxiomCertificateTokens, compactTokenAt,
        compactFixedPAAxiomSentenceTokens,
        compactOptionJoin,
        compactOptionListGet,
        compactFixedPAAxiomSentenceTable,
        compactFixedPAAxiomSentenceBaseTable,
        compactSentenceTokens, PAAxiomCertificate.sentence]

#print axioms compactFunctionExtSentenceTokens_primrec
#print axioms compactRelationExtSentenceTokens_primrec
#print axioms compactFixedPAAxiomSentenceTable_primrec
#print axioms compactFixedPAAxiomSentenceTokens_primrec
#print axioms compactFixedPAAxiomSentenceTokens_canonical

end FoundationCompactNumericFixedPAAxiomSentence

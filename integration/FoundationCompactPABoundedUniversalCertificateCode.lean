import integration.FoundationCompactPABoundedUniversalCompilerBounds
import integration.FoundationCompactCanonicalDecodeLength

/-!
# Proof-free input code for bounded-universal certificates

This serialization contains only constructor tags, the target formula at each
recursive node, arithmetic terms, atomic literals, witnesses, and the indexed
formula body.  Equality proofs, truth proofs, and closedness proofs live in
`Prop` and contribute no bits.  Recording expanded target syntax prevents
substitution growth from being hidden outside the fixed-polynomial coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABoundedUniversalCertificateCode

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCanonicalDecodeLength
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAUnaryBoundedFormulaTransport
open FoundationCompactPABoundedUniversalCompiler

namespace ClosedPATerm

def proofFreeCode : ClosedPATerm → List Bool
  | .numeral value => binaryNatCode 0 ++ binaryNatCode value
  | .add left right =>
      binaryNatCode 1 ++ proofFreeCode left ++ proofFreeCode right
  | .mul left right =>
      binaryNatCode 2 ++ proofFreeCode left ++ proofFreeCode right

theorem nodeCount_le_proofFreeCode_length
    (expression : ClosedPATerm) :
    expression.nodeCount <= (proofFreeCode expression).length := by
  induction expression with
  | numeral value =>
      have htag := two_le_binaryNatCode_length 0
      have hvalue := two_le_binaryNatCode_length value
      simp only [ClosedPATerm.nodeCount, proofFreeCode, List.length_append]
      omega
  | add left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 1
      simp only [ClosedPATerm.nodeCount, proofFreeCode, List.length_append]
      omega
  | mul left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 2
      simp only [ClosedPATerm.nodeCount, proofFreeCode, List.length_append]
      omega

theorem leafBitWeight_le_proofFreeCode_length
    (expression : ClosedPATerm) :
    expression.leafBitWeight <= (proofFreeCode expression).length := by
  induction expression with
  | numeral value =>
      have hvalue := binaryNatCode_length value
      simp only [ClosedPATerm.leafBitWeight, proofFreeCode,
        List.length_append]
      omega
  | add left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 1
      simp only [ClosedPATerm.leafBitWeight, proofFreeCode,
        List.length_append]
      omega
  | mul left right ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 2
      simp only [ClosedPATerm.leafBitWeight, proofFreeCode,
        List.length_append]
      omega

def resourceWeight (expression : ClosedPATerm) : Nat :=
  expression.nodeCount + expression.leafBitWeight

theorem resourceWeight_le_two_mul_code_length
    (expression : ClosedPATerm) :
    resourceWeight expression <= 2 * (proofFreeCode expression).length := by
  have hnodes := nodeCount_le_proofFreeCode_length expression
  have hbits := leafBitWeight_le_proofFreeCode_length expression
  unfold resourceWeight
  omega

theorem termCode_length_le_compilerCode
    (expression : ClosedPATerm) :
    (binaryTermCode expression.term).length <=
      FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.compilerTermCodeEnvelope
        (proofFreeCode expression).length
        (proofFreeCode expression).length := by
  exact
    FoundationCompactPAClosedAtomicCompilerBounds.ClosedPATerm.generatedTerm_code_length_le_compiler
      (nodeCount_le_proofFreeCode_length expression)
      (leafBitWeight_le_proofFreeCode_length expression)

end ClosedPATerm

namespace ClosedPAAtomicLiteral

def proofFreeCode : ClosedPAAtomicLiteral → List Bool
  | .equality left right =>
      binaryNatCode 0 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right
  | .disequality left right =>
      binaryNatCode 1 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right
  | .lessThan left right =>
      binaryNatCode 2 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right
  | .notLessThan left right =>
      binaryNatCode 3 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right
  | .lessEqual left right =>
      binaryNatCode 4 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right
  | .notLessEqual left right =>
      binaryNatCode 5 ++ ClosedPATerm.proofFreeCode left ++
        ClosedPATerm.proofFreeCode right

def resourceWeight : ClosedPAAtomicLiteral → Nat
  | .equality left right
  | .disequality left right
  | .lessThan left right
  | .notLessThan left right
  | .lessEqual left right
  | .notLessEqual left right =>
      ClosedPATerm.resourceWeight left +
        ClosedPATerm.resourceWeight right + 1

theorem resourceWeight_le_four_mul_code_length
    (literal : ClosedPAAtomicLiteral) :
    resourceWeight literal <= 4 * (proofFreeCode literal).length := by
  cases literal with
  | equality left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 0
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega
  | disequality left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 1
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega
  | lessThan left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 2
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega
  | notLessThan left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 3
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega
  | lessEqual left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 4
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega
  | notLessEqual left right =>
      have hleft := ClosedPATerm.resourceWeight_le_two_mul_code_length left
      have hright := ClosedPATerm.resourceWeight_le_two_mul_code_length right
      have htag := two_le_binaryNatCode_length 5
      simp only [resourceWeight, proofFreeCode, List.length_append]
      omega

end ClosedPAAtomicLiteral

namespace CheckedUnaryReplacementCertificate

def proofFreeCode
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → List Bool
  | _, .verum =>
      binaryNatCode 0 ++
        binaryFormulaCode (⊤ : LO.FirstOrder.ArithmeticProposition)
  | _, .positiveAtomic relationSymbol arguments literal _ _ =>
      binaryNatCode 1 ++
        binaryFormulaCode
          (unaryRelationFormula relationSymbol arguments right) ++
        binaryNatCode (Encodable.encode relationSymbol) ++
        binaryTermCode (arguments 0) ++ binaryTermCode (arguments 1) ++
        ClosedPAAtomicLiteral.proofFreeCode literal
  | _, .negativeAtomic relationSymbol arguments literal _ _ =>
      binaryNatCode 2 ++
        binaryFormulaCode
          (∼unaryRelationFormula relationSymbol arguments right) ++
        binaryNatCode (Encodable.encode relationSymbol) ++
        binaryTermCode (arguments 0) ++ binaryTermCode (arguments 1) ++
        ClosedPAAtomicLiteral.proofFreeCode literal
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate rightCertificate =>
      binaryNatCode 3 ++ binaryFormulaCode (leftFormula ⋏ rightFormula) ++
        proofFreeCode leftCertificate ++
        proofFreeCode rightCertificate
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate =>
      binaryNatCode 4 ++ binaryFormulaCode (leftFormula ⋎ rightFormula) ++
        proofFreeCode leftCertificate
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) rightCertificate =>
      binaryNatCode 5 ++ binaryFormulaCode (leftFormula ⋎ rightFormula) ++
        proofFreeCode rightCertificate
  | _, .existsWitness body witness bodyCertificate =>
      binaryNatCode 6 ++
        binaryFormulaCode (∃⁰ body) ++
        ClosedPATerm.proofFreeCode witness ++
        proofFreeCode bodyCertificate

def nodeCount
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum => 1
  | _, .positiveAtomic _ _ _ _ _ => 1
  | _, .negativeAtomic _ _ _ _ _ => 1
  | _, .conjunction leftCertificate rightCertificate =>
      1 + nodeCount leftCertificate + nodeCount rightCertificate
  | _, .disjunctionLeft leftCertificate => 1 + nodeCount leftCertificate
  | _, .disjunctionRight rightCertificate => 1 + nodeCount rightCertificate
  | _, .existsWitness _ _ bodyCertificate => 1 + nodeCount bodyCertificate

def storedSyntaxCodeLength
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0} :
    {formula : LO.FirstOrder.ArithmeticProposition} →
      CheckedUnaryReplacementCertificate left right formula → Nat
  | _, .verum =>
      (binaryFormulaCode
        (⊤ : LO.FirstOrder.ArithmeticProposition)).length
  | _, .positiveAtomic relationSymbol arguments literal _ _ =>
      (binaryFormulaCode
          (unaryRelationFormula relationSymbol arguments right)).length +
        (binaryTermCode (arguments 0)).length +
        (binaryTermCode (arguments 1)).length +
        (ClosedPAAtomicLiteral.proofFreeCode literal).length
  | _, .negativeAtomic relationSymbol arguments literal _ _ =>
      (binaryFormulaCode
          (∼unaryRelationFormula relationSymbol arguments right)).length +
        (binaryTermCode (arguments 0)).length +
        (binaryTermCode (arguments 1)).length +
        (ClosedPAAtomicLiteral.proofFreeCode literal).length
  | _, .conjunction (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate rightCertificate =>
      (binaryFormulaCode (leftFormula ⋏ rightFormula)).length +
        storedSyntaxCodeLength leftCertificate +
        storedSyntaxCodeLength rightCertificate
  | _, .disjunctionLeft (leftFormula := leftFormula)
      (rightFormula := rightFormula) leftCertificate =>
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length +
        storedSyntaxCodeLength leftCertificate
  | _, .disjunctionRight (leftFormula := leftFormula)
      (rightFormula := rightFormula) rightCertificate =>
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length +
        storedSyntaxCodeLength rightCertificate
  | _, .existsWitness body witness bodyCertificate =>
      (binaryFormulaCode (∃⁰ body)).length +
        (ClosedPATerm.proofFreeCode witness).length +
        storedSyntaxCodeLength bodyCertificate

theorem one_le_proofFreeCode_length
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    1 <= (proofFreeCode certificate).length := by
  cases certificate with
  | verum =>
      have htag := two_le_binaryNatCode_length 0
      simp only [proofFreeCode, List.length_append]
      omega
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have htag := two_le_binaryNatCode_length 1
      simp only [proofFreeCode, List.length_append]
      omega
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have htag := two_le_binaryNatCode_length 2
      simp only [proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate =>
      have htag := two_le_binaryNatCode_length 3
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate =>
      have htag := two_le_binaryNatCode_length 4
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate =>
      have htag := two_le_binaryNatCode_length 5
      simp only [proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate =>
      have htag := two_le_binaryNatCode_length 6
      simp only [proofFreeCode, List.length_append]
      omega

theorem targetFormulaCodeLength_le_proofFreeCode_length
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    (binaryFormulaCode formula).length <=
      (proofFreeCode certificate).length := by
  cases certificate with
  | verum =>
      simp only [proofFreeCode, List.length_append]
      omega
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp only [proofFreeCode, List.length_append]
      omega
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp only [proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate =>
      simp only [proofFreeCode, List.length_append]
      omega

theorem nodeCount_le_proofFreeCode_length
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    nodeCount certificate <= (proofFreeCode certificate).length := by
  induction certificate with
  | verum =>
      have htag := two_le_binaryNatCode_length 0
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have htag := two_le_binaryNatCode_length 1
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      have htag := two_le_binaryNatCode_length 2
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      have htag := two_le_binaryNatCode_length 3
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      have htag := two_le_binaryNatCode_length 4
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate ihRight =>
      have htag := two_le_binaryNatCode_length 5
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      have htag := two_le_binaryNatCode_length 6
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega

theorem storedSyntaxCodeLength_le_proofFreeCode_length
    {left right : LO.FirstOrder.ArithmeticSemiterm Nat 0}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedUnaryReplacementCertificate left right formula) :
    storedSyntaxCodeLength certificate <=
      (proofFreeCode certificate).length := by
  induction certificate with
  | verum => simp [storedSyntaxCodeLength, proofFreeCode]
  | positiveAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega
  | negativeAtomic relationSymbol arguments literal sourceFormula hvalue =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega
  | conjunction leftCertificate rightCertificate ihLeft ihRight =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega
  | disjunctionLeft leftCertificate ihLeft =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega
  | disjunctionRight rightCertificate ihRight =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega
  | existsWitness body witness bodyCertificate ihBody =>
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega

end CheckedUnaryReplacementCertificate

namespace CheckedFiniteUniversalBranches

def proofFreeCode
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
    {bound : Nat} → CheckedFiniteUniversalBranches body bound → List Bool
  | 0, .nil => binaryNatCode 0
  | _ + 1, .snoc initial last =>
      binaryNatCode 1 ++ proofFreeCode initial ++
        CheckedUnaryReplacementCertificate.proofFreeCode last

def nodeCount
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
    {bound : Nat} → CheckedFiniteUniversalBranches body bound → Nat
  | 0, .nil => 1
  | _ + 1, .snoc initial last =>
      1 + nodeCount initial +
        CheckedUnaryReplacementCertificate.nodeCount last

def storedSyntaxCodeLength
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
    {bound : Nat} → CheckedFiniteUniversalBranches body bound → Nat
  | 0, .nil => 0
  | _ + 1, .snoc initial last =>
      storedSyntaxCodeLength initial +
        CheckedUnaryReplacementCertificate.storedSyntaxCodeLength last

theorem caseCount_le_proofFreeCode_length
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (branches : CheckedFiniteUniversalBranches body bound) :
    bound <= (proofFreeCode branches).length := by
  induction branches with
  | nil => simp [proofFreeCode]
  | @snoc bound initial last ih =>
      have htag := two_le_binaryNatCode_length 1
      have hlast :=
        CheckedUnaryReplacementCertificate.one_le_proofFreeCode_length last
      simp only [proofFreeCode, List.length_append]
      omega

theorem nodeCount_le_proofFreeCode_length
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (branches : CheckedFiniteUniversalBranches body bound) :
    nodeCount branches <= (proofFreeCode branches).length := by
  induction branches with
  | nil =>
      have htag := two_le_binaryNatCode_length 0
      simp only [nodeCount, proofFreeCode]
      omega
  | @snoc bound initial last ih =>
      have htag := two_le_binaryNatCode_length 1
      have hlast :=
        CheckedUnaryReplacementCertificate.nodeCount_le_proofFreeCode_length
          last
      simp only [nodeCount, proofFreeCode, List.length_append]
      omega

theorem storedSyntaxCodeLength_le_proofFreeCode_length
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (branches : CheckedFiniteUniversalBranches body bound) :
    storedSyntaxCodeLength branches <= (proofFreeCode branches).length := by
  induction branches with
  | nil => simp [storedSyntaxCodeLength, proofFreeCode]
  | @snoc bound initial last ih =>
      have hlast :=
        CheckedUnaryReplacementCertificate.storedSyntaxCodeLength_le_proofFreeCode_length
          last
      simp only [storedSyntaxCodeLength, proofFreeCode, List.length_append]
      omega

end CheckedFiniteUniversalBranches

namespace CheckedFiniteBoundedUniversalCertificate

def proofFreeCode
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    List Bool :=
  binaryNatCode bound ++ binaryFormulaCode body ++
    CheckedFiniteUniversalBranches.proofFreeCode certificate.branches

def encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  (proofFreeCode certificate).length

theorem bound_le_encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    bound <= encodedSize certificate := by
  have hbranches :=
    CheckedFiniteUniversalBranches.caseCount_le_proofFreeCode_length
      certificate.branches
  simp only [encodedSize, proofFreeCode, List.length_append]
  omega

theorem body_code_length_le_encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    (binaryFormulaCode body).length <= encodedSize certificate := by
  simp only [encodedSize, proofFreeCode, List.length_append]
  omega

theorem branches_code_length_le_encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    (CheckedFiniteUniversalBranches.proofFreeCode certificate.branches).length <=
      encodedSize certificate := by
  simp only [encodedSize, proofFreeCode, List.length_append]
  omega

theorem branch_nodeCount_le_encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    CheckedFiniteUniversalBranches.nodeCount certificate.branches <=
      encodedSize certificate := by
  have hnodes :=
    CheckedFiniteUniversalBranches.nodeCount_le_proofFreeCode_length
      certificate.branches
  simp only [encodedSize, proofFreeCode, List.length_append]
  omega

theorem branch_storedSyntaxCodeLength_le_encodedSize
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    CheckedFiniteUniversalBranches.storedSyntaxCodeLength
        certificate.branches <=
      encodedSize certificate := by
  have hsyntax :=
    CheckedFiniteUniversalBranches.storedSyntaxCodeLength_le_proofFreeCode_length
      certificate.branches
  exact hsyntax.trans (branches_code_length_le_encodedSize certificate)

end CheckedFiniteBoundedUniversalCertificate

#print axioms ClosedPATerm.resourceWeight_le_two_mul_code_length
#print axioms ClosedPATerm.termCode_length_le_compilerCode
#print axioms ClosedPAAtomicLiteral.resourceWeight_le_four_mul_code_length
#print axioms CheckedUnaryReplacementCertificate.nodeCount_le_proofFreeCode_length
#print axioms CheckedUnaryReplacementCertificate.targetFormulaCodeLength_le_proofFreeCode_length
#print axioms CheckedUnaryReplacementCertificate.storedSyntaxCodeLength_le_proofFreeCode_length
#print axioms CheckedFiniteUniversalBranches.caseCount_le_proofFreeCode_length
#print axioms CheckedFiniteUniversalBranches.storedSyntaxCodeLength_le_proofFreeCode_length
#print axioms CheckedFiniteBoundedUniversalCertificate.bound_le_encodedSize
#print axioms CheckedFiniteBoundedUniversalCertificate.branch_storedSyntaxCodeLength_le_encodedSize

end FoundationCompactPABoundedUniversalCertificateCode

import integration.FoundationCompactNumericListedDirectVerifierPAAxiomNonInductionLeafRows
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomInductionLeafRows
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness
import integration.FoundationCompactNumericListedDirectNatListListWitnessRows
import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality

/-!
# Self-contained joint PA-axiom leaf rows

The certificate endpoint and the canonical rule table may use separate
fixed-width tables.  A bounded cross-table slice equality identifies the
certificate slice consumed by the endpoint with the full axiom slice used by
the rule.  The rule table itself realizes the context, candidate, and axiom
lists, so soundness needs no external layout hypotheses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericGuardedInductionSentence
open FoundationCompactNumericTokenBitLength
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactNumericListedDirectFixedPAAxiomCandidate
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
open FoundationCompactNumericListedDirectFormulaMembership
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPAAxiomNonInductionLeafRows
open FoundationCompactNumericListedDirectVerifierPAAxiomInductionLeafRows
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectPackedRouteTable

structure CompactNumericVerifierPAAxiomJointLeafCoordinates where
  endpointTable : Nat
  endpointWidth : Nat
  endpointTokenCount : Nat
  ruleTable : Nat
  ruleWidth : Nat
  ruleTokenCount : Nat
  inputStart : Nat
  inputFinish : Nat
  endpointAxiomStart : Nat
  endpointAxiomFinish : Nat
  formulaStart : Nat
  formulaFinish : Nat
  suffixStart : Nat
  suffixFinish : Nat
  proofTag : Nat
  certificateTag : Nat
  gammaStart : Nat
  gammaFinish : Nat
  gammaBoundary : Nat
  gammaCount : Nat
  gammaBoundarySize : Nat
  candidate : CompactNatListRowSlot
  ruleAxiom : CompactNatListRowSlot
  resultBool : Nat
  depth : Nat
  fixedEndpoint : CompactCertificateNodeFixedPAEndpointCoordinates
  symbolEndpoint : CompactCertificateNodeSymbolPAEndpointCoordinates
  inductionEndpoint : CompactCertificateNodeInductionPAEndpointCoordinates
  body : CompactNatListRowSlot
  zeroWitness : CompactNatListRowSlot
  openZeroWitness : CompactNatListRowSlot
  openSuccessorWitness : CompactNatListRowSlot
  captureOne : CompactNatListRowSlot
  empty : CompactNatListRowSlot
  base : CompactNatListRowSlot
  negatedBase : CompactNatListRowSlot
  stepZero : CompactNatListRowSlot
  stepSuccessor : CompactNatListRowSlot
  negatedStepZero : CompactNatListRowSlot
  stepDisjunction : CompactNatListRowSlot
  quantifiedStep : CompactNatListRowSlot
  negatedQuantifiedStep : CompactNatListRowSlot
  quantifiedFinal : CompactNatListRowSlot
  innerDisjunction : CompactNatListRowSlot
  sentence : CompactNatListRowSlot
  fvarList : CompactNatListRowSlot
  depthCapture : CompactNatListRowSlot
  fixed : CompactNatListRowSlot
  generated : CompactNatListRowSlot
  route : CompactGuardedInductionSentenceRouteCoordinates

def CompactNumericVerifierPAAxiomJointLeafRows
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Prop :=
  CompactAdditiveNatListListWitnessRows
      c.ruleTable c.ruleWidth c.ruleTokenCount
      c.gammaStart c.gammaCount c.gammaFinish c.gammaBoundary
      c.gammaBoundarySize /\
    CompactAdditiveNatListWitnessRows
      c.ruleTable c.ruleWidth c.ruleTokenCount
      c.candidate.start c.candidate.count c.candidate.finish
      c.candidate.boundary c.candidate.boundarySize /\
    CompactAdditiveNatListWitnessRows
      c.ruleTable c.ruleWidth c.ruleTokenCount
      c.ruleAxiom.start c.ruleAxiom.count c.ruleAxiom.finish
      c.ruleAxiom.boundary c.ruleAxiom.boundarySize /\
    CompactFixedWidthCrossTableSlicesEq
      c.endpointTable c.endpointWidth c.endpointTokenCount
        c.endpointAxiomStart c.endpointAxiomFinish
      c.ruleTable c.ruleWidth c.ruleTokenCount
        c.ruleAxiom.start c.ruleAxiom.finish /\
    c.proofTag = 1 /\
    (((CompactCertificateNodeFixedPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish
          c.endpointAxiomStart c.endpointAxiomFinish
          c.suffixStart c.suffixFinish c.certificateTag c.fixedEndpoint /\
        CompactAdditiveFixedPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount
          c.gammaBoundary c.gammaCount
          c.candidate.start c.candidate.finish c.candidate.count
          c.fixedEndpoint.paTag 0 0 c.resultBool) \/
      (CompactCertificateNodeSymbolPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish
          c.endpointAxiomStart c.endpointAxiomFinish
          c.suffixStart c.suffixFinish c.certificateTag c.symbolEndpoint /\
        CompactAdditiveFixedPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount
          c.gammaBoundary c.gammaCount
          c.candidate.start c.candidate.finish c.candidate.count
          c.symbolEndpoint.paTag c.symbolEndpoint.arity
          c.symbolEndpoint.symbolCode c.resultBool)) \/
      (CompactCertificateNodeInductionPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish
          c.endpointAxiomStart c.endpointAxiomFinish
          c.formulaStart c.formulaFinish c.suffixStart c.suffixFinish
          c.certificateTag c.inductionEndpoint /\
        CompactAdditiveInductionPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount
          c.gammaBoundary c.gammaCount c.resultBool c.ruleAxiom
          c.body c.zeroWitness c.openZeroWitness c.openSuccessorWitness
          c.captureOne c.empty c.base c.negatedBase c.stepZero
          c.stepSuccessor c.negatedStepZero c.stepDisjunction
          c.quantifiedStep c.negatedQuantifiedStep c.quantifiedFinal
          c.innerDisjunction c.sentence c.fvarList c.depthCapture c.fixed
          c.generated c.candidate c.depth c.route))

def compactPAAxiomJointGammaWitnessLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveNatListListWitnessRowsDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #197, #178, #198, #177, #199]

def compactPAAxiomJointCandidateWitnessLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveNatListWitnessRowsDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #182, #201, #183, #200, #202]

def compactPAAxiomJointAxiomWitnessLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveNatListWitnessRowsDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #203, #181, #204, #180, #205]

def compactPAAxiomJointCrossTableAxiomLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactFixedWidthCrossTableSlicesEqDef.val ⇜
    ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #189, #190,
      #0, #1, #2, #203, #204]

def compactPAAxiomJointFixedEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactCertificateNodeFixedPAEndpointGraphDef.val ⇜
    ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
      #189, #190, #193, #194, #196,
      #206, #207, #208, #209, #210, #211, #212, #213,
      #214, #215, #216, #217, #218, #219, #220]

def compactPAAxiomJointSymbolEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactCertificateNodeSymbolPAEndpointGraphDef.val ⇜
    ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
      #189, #190, #193, #194, #196,
      #221, #222, #223, #224, #225, #226, #227, #228,
      #229, #230, #231, #232, #233, #234, #235, #236, #237]

def compactPAAxiomJointInductionEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactCertificateNodeInductionPAEndpointGraphDef.val ⇜
    ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
      #189, #190, #191, #192, #193, #194, #196,
      #238, #239, #240, #241, #242, #243, #244, #245,
      #246, #247, #248, #249, #250, #251, #252, #253,
      #254, #255, #256, #257, #258]

def compactPAAxiomJointFixedRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveFixedPAAxiomRuleCheckDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
      #182, #183, #201, #220, ‘0’, ‘0’, #179]

def compactPAAxiomJointSymbolRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveFixedPAAxiomRuleCheckDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
      #182, #183, #201, #235, #236, #237, #179]

def compactPAAxiomJointInductionRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 259 :=
  compactAdditiveInductionPAAxiomRuleCheckDef.val ⇜
    (fun index : Fin 184 =>
      (#(Fin.castLE (show 184 <= 259 by omega) index) :
        Semiterm ℒₒᵣ Empty 259))

def compactNumericVerifierPAAxiomJointLeafRowsDef :
    𝚺₀.Semisentence 259 := .mkSigma
  (compactPAAxiomJointGammaWitnessLift ⋏
    compactPAAxiomJointCandidateWitnessLift ⋏
    compactPAAxiomJointAxiomWitnessLift ⋏
    compactPAAxiomJointCrossTableAxiomLift ⋏
    “(#195 = 1)” ⋏
    (((compactPAAxiomJointFixedEndpointLift ⋏
          compactPAAxiomJointFixedRuleLift) ⋎
        (compactPAAxiomJointSymbolEndpointLift ⋏
          compactPAAxiomJointSymbolRuleLift)) ⋎
      (compactPAAxiomJointInductionEndpointLift ⋏
        compactPAAxiomJointInductionRuleLift)))
  (by
    simp [compactPAAxiomJointGammaWitnessLift,
      compactPAAxiomJointCandidateWitnessLift,
      compactPAAxiomJointAxiomWitnessLift,
      compactPAAxiomJointCrossTableAxiomLift,
      compactPAAxiomJointFixedEndpointLift,
      compactPAAxiomJointSymbolEndpointLift,
      compactPAAxiomJointInductionEndpointLift,
      compactPAAxiomJointFixedRuleLift,
      compactPAAxiomJointSymbolRuleLift,
      compactPAAxiomJointInductionRuleLift])

def compactNumericVerifierPAAxiomJointLeafRowsEnvironment
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Fin 259 -> Nat :=
  Matrix.vecAppend rfl
    (compactAdditiveInductionPAAxiomRuleCheckEnvironment
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
      c.resultBool c.depth c.ruleAxiom c.body c.zeroWitness
      c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
      c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
      c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
      c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
      c.depthCapture c.fixed c.generated c.candidate c.route)
    ![c.endpointTable, c.endpointWidth, c.endpointTokenCount,
      c.inputStart, c.inputFinish, c.endpointAxiomStart,
      c.endpointAxiomFinish, c.formulaStart, c.formulaFinish,
      c.suffixStart, c.suffixFinish, c.proofTag, c.certificateTag,
      c.gammaStart, c.gammaFinish, c.gammaBoundarySize,
      c.candidate.boundary, c.candidate.count, c.candidate.boundarySize,
      c.ruleAxiom.start, c.ruleAxiom.finish, c.ruleAxiom.boundarySize,
      c.fixedEndpoint.inputBoundary, c.fixedEndpoint.inputCount,
      c.fixedEndpoint.inputBoundarySize, c.fixedEndpoint.tailStart,
      c.fixedEndpoint.tailFinish, c.fixedEndpoint.tailBoundary,
      c.fixedEndpoint.tailCount, c.fixedEndpoint.tailBoundarySize,
      c.fixedEndpoint.axiomBoundary, c.fixedEndpoint.axiomCount,
      c.fixedEndpoint.axiomBoundarySize, c.fixedEndpoint.suffixBoundary,
      c.fixedEndpoint.suffixCount, c.fixedEndpoint.suffixBoundarySize,
      c.fixedEndpoint.paTag,
      c.symbolEndpoint.inputBoundary, c.symbolEndpoint.inputCount,
      c.symbolEndpoint.inputBoundarySize, c.symbolEndpoint.tailStart,
      c.symbolEndpoint.tailFinish, c.symbolEndpoint.tailBoundary,
      c.symbolEndpoint.tailCount, c.symbolEndpoint.tailBoundarySize,
      c.symbolEndpoint.axiomBoundary, c.symbolEndpoint.axiomCount,
      c.symbolEndpoint.axiomBoundarySize, c.symbolEndpoint.suffixBoundary,
      c.symbolEndpoint.suffixCount, c.symbolEndpoint.suffixBoundarySize,
      c.symbolEndpoint.paTag, c.symbolEndpoint.arity,
      c.symbolEndpoint.symbolCode,
      c.inductionEndpoint.inputBoundary, c.inductionEndpoint.inputCount,
      c.inductionEndpoint.inputBoundarySize, c.inductionEndpoint.tailStart,
      c.inductionEndpoint.tailFinish, c.inductionEndpoint.tailBoundary,
      c.inductionEndpoint.tailCount, c.inductionEndpoint.tailBoundarySize,
      c.inductionEndpoint.axiomBoundary, c.inductionEndpoint.axiomCount,
      c.inductionEndpoint.axiomBoundarySize,
      c.inductionEndpoint.parser.inputBoundary,
      c.inductionEndpoint.parser.inputCount,
      c.inductionEndpoint.parser.inputBoundarySize,
      c.inductionEndpoint.parser.expectedBoundary,
      c.inductionEndpoint.parser.expectedCount,
      c.inductionEndpoint.parser.expectedBoundarySize,
      c.inductionEndpoint.parser.stateBoundary,
      c.inductionEndpoint.parser.stateCount,
      c.inductionEndpoint.parser.tableWidth,
      c.inductionEndpoint.parser.valueBound]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierPAAxiomJointLeafRowsDef_spec
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) :
    compactNumericVerifierPAAxiomJointLeafRowsDef.val.Evalb
        (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c) <->
      CompactNumericVerifierPAAxiomJointLeafRows c := by
  let env := compactNumericVerifierPAAxiomJointLeafRowsEnvironment c
  have henv0 : env 0 = c.ruleTable := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv1 : env 1 = c.ruleWidth := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv2 : env 2 = c.ruleTokenCount := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      compactGuardedInductionSentenceRouteEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv177 : env 177 = c.gammaBoundary := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv178 : env 178 = c.gammaCount := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv179 : env 179 = c.resultBool := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv180 : env 180 = c.ruleAxiom.boundary := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv181 : env 181 = c.ruleAxiom.count := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv182 : env 182 = c.candidate.start := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv183 : env 183 = c.candidate.finish := by
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have henv184 : env 184 = c.endpointTable := by rfl
  have henv185 : env 185 = c.endpointWidth := by rfl
  have henv186 : env 186 = c.endpointTokenCount := by rfl
  have henv187 : env 187 = c.inputStart := by rfl
  have henv188 : env 188 = c.inputFinish := by rfl
  have henv189 : env 189 = c.endpointAxiomStart := by rfl
  have henv190 : env 190 = c.endpointAxiomFinish := by rfl
  have henv191 : env 191 = c.formulaStart := by rfl
  have henv192 : env 192 = c.formulaFinish := by rfl
  have henv193 : env 193 = c.suffixStart := by rfl
  have henv194 : env 194 = c.suffixFinish := by rfl
  have henv195 : env 195 = c.proofTag := by rfl
  have henv196 : env 196 = c.certificateTag := by rfl
  have henv197 : env 197 = c.gammaStart := by rfl
  have henv198 : env 198 = c.gammaFinish := by rfl
  have henv199 : env 199 = c.gammaBoundarySize := by rfl
  have henv200 : env 200 = c.candidate.boundary := by rfl
  have henv201 : env 201 = c.candidate.count := by rfl
  have henv202 : env 202 = c.candidate.boundarySize := by rfl
  have henv203 : env 203 = c.ruleAxiom.start := by rfl
  have henv204 : env 204 = c.ruleAxiom.finish := by rfl
  have henv205 : env 205 = c.ruleAxiom.boundarySize := by rfl
  have henv206 : env 206 = c.fixedEndpoint.inputBoundary := by rfl
  have henv207 : env 207 = c.fixedEndpoint.inputCount := by rfl
  have henv208 : env 208 = c.fixedEndpoint.inputBoundarySize := by rfl
  have henv209 : env 209 = c.fixedEndpoint.tailStart := by rfl
  have henv210 : env 210 = c.fixedEndpoint.tailFinish := by rfl
  have henv211 : env 211 = c.fixedEndpoint.tailBoundary := by rfl
  have henv212 : env 212 = c.fixedEndpoint.tailCount := by rfl
  have henv213 : env 213 = c.fixedEndpoint.tailBoundarySize := by rfl
  have henv214 : env 214 = c.fixedEndpoint.axiomBoundary := by rfl
  have henv215 : env 215 = c.fixedEndpoint.axiomCount := by rfl
  have henv216 : env 216 = c.fixedEndpoint.axiomBoundarySize := by rfl
  have henv217 : env 217 = c.fixedEndpoint.suffixBoundary := by rfl
  have henv218 : env 218 = c.fixedEndpoint.suffixCount := by rfl
  have henv219 : env 219 = c.fixedEndpoint.suffixBoundarySize := by rfl
  have henv220 : env 220 = c.fixedEndpoint.paTag := by rfl
  have henv221 : env 221 = c.symbolEndpoint.inputBoundary := by rfl
  have henv222 : env 222 = c.symbolEndpoint.inputCount := by rfl
  have henv223 : env 223 = c.symbolEndpoint.inputBoundarySize := by rfl
  have henv224 : env 224 = c.symbolEndpoint.tailStart := by rfl
  have henv225 : env 225 = c.symbolEndpoint.tailFinish := by rfl
  have henv226 : env 226 = c.symbolEndpoint.tailBoundary := by rfl
  have henv227 : env 227 = c.symbolEndpoint.tailCount := by rfl
  have henv228 : env 228 = c.symbolEndpoint.tailBoundarySize := by rfl
  have henv229 : env 229 = c.symbolEndpoint.axiomBoundary := by rfl
  have henv230 : env 230 = c.symbolEndpoint.axiomCount := by rfl
  have henv231 : env 231 = c.symbolEndpoint.axiomBoundarySize := by rfl
  have henv232 : env 232 = c.symbolEndpoint.suffixBoundary := by rfl
  have henv233 : env 233 = c.symbolEndpoint.suffixCount := by rfl
  have henv234 : env 234 = c.symbolEndpoint.suffixBoundarySize := by rfl
  have henv235 : env 235 = c.symbolEndpoint.paTag := by rfl
  have henv236 : env 236 = c.symbolEndpoint.arity := by rfl
  have henv237 : env 237 = c.symbolEndpoint.symbolCode := by rfl
  have henv238 : env 238 = c.inductionEndpoint.inputBoundary := by rfl
  have henv239 : env 239 = c.inductionEndpoint.inputCount := by rfl
  have henv240 : env 240 = c.inductionEndpoint.inputBoundarySize := by rfl
  have henv241 : env 241 = c.inductionEndpoint.tailStart := by rfl
  have henv242 : env 242 = c.inductionEndpoint.tailFinish := by rfl
  have henv243 : env 243 = c.inductionEndpoint.tailBoundary := by rfl
  have henv244 : env 244 = c.inductionEndpoint.tailCount := by rfl
  have henv245 : env 245 = c.inductionEndpoint.tailBoundarySize := by rfl
  have henv246 : env 246 = c.inductionEndpoint.axiomBoundary := by rfl
  have henv247 : env 247 = c.inductionEndpoint.axiomCount := by rfl
  have henv248 : env 248 = c.inductionEndpoint.axiomBoundarySize := by rfl
  have henv249 : env 249 = c.inductionEndpoint.parser.inputBoundary := by rfl
  have henv250 : env 250 = c.inductionEndpoint.parser.inputCount := by rfl
  have henv251 : env 251 = c.inductionEndpoint.parser.inputBoundarySize := by rfl
  have henv252 : env 252 = c.inductionEndpoint.parser.expectedBoundary := by rfl
  have henv253 : env 253 = c.inductionEndpoint.parser.expectedCount := by rfl
  have henv254 : env 254 = c.inductionEndpoint.parser.expectedBoundarySize := by rfl
  have henv255 : env 255 = c.inductionEndpoint.parser.stateBoundary := by rfl
  have henv256 : env 256 = c.inductionEndpoint.parser.stateCount := by rfl
  have henv257 : env 257 = c.inductionEndpoint.parser.tableWidth := by rfl
  have henv258 : env 258 = c.inductionEndpoint.parser.valueBound := by rfl
  have hgammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #197, #178, #198,
          #177, #199]) =
      ![c.ruleTable, c.ruleWidth, c.ruleTokenCount, c.gammaStart,
        c.gammaCount, c.gammaFinish, c.gammaBoundary,
        c.gammaBoundarySize] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv177, henv178, henv197, henv198,
        henv199]
  have hcandidateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #182, #201, #183,
          #200, #202]) =
      ![c.ruleTable, c.ruleWidth, c.ruleTokenCount, c.candidate.start,
        c.candidate.count, c.candidate.finish, c.candidate.boundary,
        c.candidate.boundarySize] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv182, henv183, henv200, henv201,
        henv202]
  have haxiomEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #203, #181, #204,
          #180, #205]) =
      ![c.ruleTable, c.ruleWidth, c.ruleTokenCount, c.ruleAxiom.start,
        c.ruleAxiom.count, c.ruleAxiom.finish, c.ruleAxiom.boundary,
        c.ruleAxiom.boundarySize] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv180, henv181, henv203, henv204,
        henv205]
  have hcrossEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #189, #190,
          #0, #1, #2, #203, #204]) =
      ![c.endpointTable, c.endpointWidth, c.endpointTokenCount,
        c.endpointAxiomStart, c.endpointAxiomFinish,
        c.ruleTable, c.ruleWidth, c.ruleTokenCount,
        c.ruleAxiom.start, c.ruleAxiom.finish] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv184, henv185, henv186, henv189,
        henv190, henv203, henv204]
  have hfixedEndpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
          #189, #190, #193, #194, #196,
          #206, #207, #208, #209, #210, #211, #212, #213,
          #214, #215, #216, #217, #218, #219, #220]) =
      compactCertificateNodeFixedPAEndpointEnvironment
        c.endpointTable c.endpointWidth c.endpointTokenCount
        c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
        c.suffixStart c.suffixFinish c.certificateTag c.fixedEndpoint := by
    funext index
    fin_cases index <;>
      simp [henv184, henv185, henv186, henv187, henv188, henv189,
        henv190, henv193, henv194, henv196, henv206, henv207, henv208,
        henv209, henv210, henv211, henv212, henv213, henv214, henv215,
        henv216, henv217, henv218, henv219, henv220,
        compactCertificateNodeFixedPAEndpointEnvironment]
  have hsymbolEndpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
          #189, #190, #193, #194, #196,
          #221, #222, #223, #224, #225, #226, #227, #228,
          #229, #230, #231, #232, #233, #234, #235, #236, #237]) =
      compactCertificateNodeSymbolPAEndpointEnvironment
        c.endpointTable c.endpointWidth c.endpointTokenCount
        c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
        c.suffixStart c.suffixFinish c.certificateTag c.symbolEndpoint := by
    funext index
    fin_cases index <;>
      simp [henv184, henv185, henv186, henv187, henv188, henv189,
        henv190, henv193, henv194, henv196, henv221, henv222, henv223,
        henv224, henv225, henv226, henv227, henv228, henv229, henv230,
        henv231, henv232, henv233, henv234, henv235, henv236, henv237,
        compactCertificateNodeSymbolPAEndpointEnvironment]
  have hinductionEndpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
          #189, #190, #191, #192, #193, #194, #196,
          #238, #239, #240, #241, #242, #243, #244, #245,
          #246, #247, #248, #249, #250, #251, #252, #253,
          #254, #255, #256, #257, #258]) =
      compactCertificateNodeInductionPAEndpointEnvironment
        c.endpointTable c.endpointWidth c.endpointTokenCount
        c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
        c.formulaStart c.formulaFinish c.suffixStart c.suffixFinish
        c.certificateTag c.inductionEndpoint := by
    funext index
    fin_cases index <;>
      simp [henv184, henv185, henv186, henv187, henv188, henv189,
        henv190, henv191, henv192, henv193, henv194, henv196, henv238,
        henv239, henv240, henv241, henv242, henv243, henv244, henv245,
        henv246, henv247, henv248, henv249, henv250, henv251, henv252,
        henv253, henv254, henv255, henv256, henv257, henv258,
        compactCertificateNodeInductionPAEndpointEnvironment]
  have hfixedRuleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
          #182, #183, #201, #220,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 259),
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 259), #179]) =
      ![c.ruleTable, c.ruleWidth, c.ruleTokenCount,
        c.gammaBoundary, c.gammaCount, c.candidate.start,
        c.candidate.finish, c.candidate.count,
        c.fixedEndpoint.paTag, 0, 0, c.resultBool] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv177, henv178, henv179, henv182,
        henv183, henv201, henv220]
  have hsymbolRuleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
          #182, #183, #201, #235, #236, #237, #179]) =
      ![c.ruleTable, c.ruleWidth, c.ruleTokenCount,
        c.gammaBoundary, c.gammaCount, c.candidate.start,
        c.candidate.finish, c.candidate.count,
        c.symbolEndpoint.paTag, c.symbolEndpoint.arity,
        c.symbolEndpoint.symbolCode, c.resultBool] := by
    funext index
    fin_cases index <;>
      simp [henv0, henv1, henv2, henv177, henv178, henv179, henv182,
        henv183, henv201, henv235, henv236, henv237]
  have hinductionRuleEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 184 =>
          (#(Fin.castLE (show 184 <= 259 by omega) index) :
            Semiterm ℒₒᵣ Empty 259))) =
      compactAdditiveInductionPAAxiomRuleCheckEnvironment
        c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
        c.resultBool c.depth c.ruleAxiom c.body c.zeroWitness
        c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
        c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
        c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
        c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
        c.depthCapture c.fixed c.generated c.candidate c.route := by
    funext index
    simp [env, compactNumericVerifierPAAxiomJointLeafRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  have hproofTag : env 195 = c.proofTag := henv195
  have hgammaSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #197, #178, #198,
              #177, #199])
          Empty.elim compactAdditiveNatListListWitnessRowsDef.val <->
        CompactAdditiveNatListListWitnessRows
          c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaStart
          c.gammaCount c.gammaFinish c.gammaBoundary c.gammaBoundarySize := by
    rw [hgammaEnv]
    exact compactAdditiveNatListListWitnessRowsDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaStart c.gammaCount
      c.gammaFinish c.gammaBoundary c.gammaBoundarySize
  have hcandidateSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #182, #201, #183,
              #200, #202])
          Empty.elim compactAdditiveNatListWitnessRowsDef.val <->
        CompactAdditiveNatListWitnessRows
          c.ruleTable c.ruleWidth c.ruleTokenCount c.candidate.start
          c.candidate.count c.candidate.finish c.candidate.boundary
          c.candidate.boundarySize := by
    rw [hcandidateEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.candidate.start
      c.candidate.count c.candidate.finish c.candidate.boundary
      c.candidate.boundarySize
  have haxiomSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #203, #181, #204,
              #180, #205])
          Empty.elim compactAdditiveNatListWitnessRowsDef.val <->
        CompactAdditiveNatListWitnessRows
          c.ruleTable c.ruleWidth c.ruleTokenCount c.ruleAxiom.start
          c.ruleAxiom.count c.ruleAxiom.finish c.ruleAxiom.boundary
          c.ruleAxiom.boundarySize := by
    rw [haxiomEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.ruleAxiom.start
      c.ruleAxiom.count c.ruleAxiom.finish c.ruleAxiom.boundary
      c.ruleAxiom.boundarySize
  have hcrossSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #189, #190,
              #0, #1, #2, #203, #204])
          Empty.elim compactFixedWidthCrossTableSlicesEqDef.val <->
        CompactFixedWidthCrossTableSlicesEq
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.endpointAxiomStart c.endpointAxiomFinish
          c.ruleTable c.ruleWidth c.ruleTokenCount
          c.ruleAxiom.start c.ruleAxiom.finish := by
    rw [hcrossEnv]
    exact compactFixedWidthCrossTableSlicesEqDef_spec
      c.endpointTable c.endpointWidth c.endpointTokenCount
      c.endpointAxiomStart c.endpointAxiomFinish
      c.ruleTable c.ruleWidth c.ruleTokenCount
      c.ruleAxiom.start c.ruleAxiom.finish
  have hfixedEndpointSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
              #189, #190, #193, #194, #196,
              #206, #207, #208, #209, #210, #211, #212, #213,
              #214, #215, #216, #217, #218, #219, #220])
          Empty.elim compactCertificateNodeFixedPAEndpointGraphDef.val <->
        CompactCertificateNodeFixedPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish c.endpointAxiomStart
          c.endpointAxiomFinish c.suffixStart c.suffixFinish
          c.certificateTag c.fixedEndpoint := by
    rw [hfixedEndpointEnv]
    exact compactCertificateNodeFixedPAEndpointGraphDef_spec
      c.endpointTable c.endpointWidth c.endpointTokenCount
      c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
      c.suffixStart c.suffixFinish c.certificateTag c.fixedEndpoint
  have hsymbolEndpointSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
              #189, #190, #193, #194, #196,
              #221, #222, #223, #224, #225, #226, #227, #228,
              #229, #230, #231, #232, #233, #234, #235, #236, #237])
          Empty.elim compactCertificateNodeSymbolPAEndpointGraphDef.val <->
        CompactCertificateNodeSymbolPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish c.endpointAxiomStart
          c.endpointAxiomFinish c.suffixStart c.suffixFinish
          c.certificateTag c.symbolEndpoint := by
    rw [hsymbolEndpointEnv]
    exact compactCertificateNodeSymbolPAEndpointGraphDef_spec
      c.endpointTable c.endpointWidth c.endpointTokenCount
      c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
      c.suffixStart c.suffixFinish c.certificateTag c.symbolEndpoint
  have hinductionEndpointSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#184 : Semiterm ℒₒᵣ Empty 259), #185, #186, #187, #188,
              #189, #190, #191, #192, #193, #194, #196,
              #238, #239, #240, #241, #242, #243, #244, #245,
              #246, #247, #248, #249, #250, #251, #252, #253,
              #254, #255, #256, #257, #258])
          Empty.elim compactCertificateNodeInductionPAEndpointGraphDef.val <->
        CompactCertificateNodeInductionPAEndpointGraph
          c.endpointTable c.endpointWidth c.endpointTokenCount
          c.inputStart c.inputFinish c.endpointAxiomStart
          c.endpointAxiomFinish c.formulaStart c.formulaFinish
          c.suffixStart c.suffixFinish c.certificateTag
          c.inductionEndpoint := by
    rw [hinductionEndpointEnv]
    exact compactCertificateNodeInductionPAEndpointGraphDef_spec
      c.endpointTable c.endpointWidth c.endpointTokenCount
      c.inputStart c.inputFinish c.endpointAxiomStart c.endpointAxiomFinish
      c.formulaStart c.formulaFinish c.suffixStart c.suffixFinish
      c.certificateTag c.inductionEndpoint
  have hfixedRuleSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
              #182, #183, #201, #220,
              (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 259),
              (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 259), #179])
          Empty.elim compactAdditiveFixedPAAxiomRuleCheckDef.val <->
        CompactAdditiveFixedPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary
          c.gammaCount c.candidate.start c.candidate.finish
          c.candidate.count c.fixedEndpoint.paTag 0 0 c.resultBool := by
    rw [hfixedRuleEnv]
    exact compactAdditiveFixedPAAxiomRuleCheckDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
      c.candidate.start c.candidate.finish c.candidate.count
      c.fixedEndpoint.paTag 0 0 c.resultBool
  have hsymbolRuleSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 259), #1, #2, #177, #178,
              #182, #183, #201, #235, #236, #237, #179])
          Empty.elim compactAdditiveFixedPAAxiomRuleCheckDef.val <->
        CompactAdditiveFixedPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary
          c.gammaCount c.candidate.start c.candidate.finish
          c.candidate.count c.symbolEndpoint.paTag c.symbolEndpoint.arity
          c.symbolEndpoint.symbolCode c.resultBool := by
    rw [hsymbolRuleEnv]
    exact compactAdditiveFixedPAAxiomRuleCheckDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
      c.candidate.start c.candidate.finish c.candidate.count
      c.symbolEndpoint.paTag c.symbolEndpoint.arity
      c.symbolEndpoint.symbolCode c.resultBool
  have hinductionRuleSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            (fun index : Fin 184 =>
              (#(Fin.castLE (show 184 <= 259 by omega) index) :
                Semiterm ℒₒᵣ Empty 259)))
          Empty.elim compactAdditiveInductionPAAxiomRuleCheckDef.val <->
        CompactAdditiveInductionPAAxiomRuleCheck
          c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary
          c.gammaCount c.resultBool c.ruleAxiom c.body c.zeroWitness
          c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
          c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
          c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
          c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
          c.depthCapture c.fixed c.generated c.candidate c.depth c.route := by
    rw [hinductionRuleEnv]
    exact compactAdditiveInductionPAAxiomRuleCheckDef_spec
      c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
      c.resultBool c.depth c.ruleAxiom c.body c.zeroWitness
      c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
      c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
      c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
      c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
      c.depthCapture c.fixed c.generated c.candidate c.route
  change
    (Semiformula.Eval env Empty.elim compactPAAxiomJointGammaWitnessLift /\
      Semiformula.Eval env Empty.elim compactPAAxiomJointCandidateWitnessLift /\
      Semiformula.Eval env Empty.elim compactPAAxiomJointAxiomWitnessLift /\
      Semiformula.Eval env Empty.elim compactPAAxiomJointCrossTableAxiomLift /\
      env 195 = 1 /\
      (((Semiformula.Eval env Empty.elim compactPAAxiomJointFixedEndpointLift /\
            Semiformula.Eval env Empty.elim compactPAAxiomJointFixedRuleLift) \/
          (Semiformula.Eval env Empty.elim compactPAAxiomJointSymbolEndpointLift /\
            Semiformula.Eval env Empty.elim compactPAAxiomJointSymbolRuleLift)) \/
        (Semiformula.Eval env Empty.elim compactPAAxiomJointInductionEndpointLift /\
          Semiformula.Eval env Empty.elim compactPAAxiomJointInductionRuleLift))) <->
      CompactNumericVerifierPAAxiomJointLeafRows c
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointGammaWitnessLift <-> _ by
      simpa [compactPAAxiomJointGammaWitnessLift] using hgammaSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointCandidateWitnessLift <-> _ by
      simpa [compactPAAxiomJointCandidateWitnessLift] using hcandidateSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointAxiomWitnessLift <-> _ by
      simpa [compactPAAxiomJointAxiomWitnessLift] using haxiomSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointCrossTableAxiomLift <-> _ by
      simpa [compactPAAxiomJointCrossTableAxiomLift] using hcrossSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointFixedEndpointLift <-> _ by
      simpa [compactPAAxiomJointFixedEndpointLift] using hfixedEndpointSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointSymbolEndpointLift <-> _ by
      simpa [compactPAAxiomJointSymbolEndpointLift] using hsymbolEndpointSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointInductionEndpointLift <-> _ by
      simpa [compactPAAxiomJointInductionEndpointLift] using
        hinductionEndpointSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointFixedRuleLift <-> _ by
      simpa [compactPAAxiomJointFixedRuleLift] using hfixedRuleSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointSymbolRuleLift <-> _ by
      simpa [compactPAAxiomJointSymbolRuleLift] using hsymbolRuleSpec]
  rw [show Semiformula.Eval env Empty.elim
        compactPAAxiomJointInductionRuleLift <-> _ by
      simpa [compactPAAxiomJointInductionRuleLift] using hinductionRuleSpec]
  rw [hproofTag]
  rfl

theorem compactNumericVerifierPAAxiomJointLeafRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomJointLeafRowsDef.val := by
  exact compactNumericVerifierPAAxiomJointLeafRowsDef.sigma_prop

private theorem compactPAAxiomSentenceEqTokens_fixed_list_iff
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate)
    (candidateTokens : List Nat) :
    compactPAAxiomSentenceEqTokens
        (compactPAAxiomCertificateTokens certificate, candidateTokens) = true <->
      candidateTokens = compactSentenceTokens certificate.sentence := by
  have hparse : compactPAAxiomCertificateTokenParser
      (compactPAAxiomCertificateTokens certificate) = some [] := by
    simpa using compactPAAxiomCertificateTokenParser_canonical_append
      certificate []
  have htag : compactTokenAt 0
      (compactPAAxiomCertificateTokens certificate) ≠ 22 := by
    cases certificate <;>
      simp [FixedPAAxiomCertificate, compactPAAxiomCertificateTokens,
        compactTokenAt] at hfixed ⊢
  unfold compactPAAxiomSentenceEqTokens
  rw [if_pos hparse, if_neg htag]
  unfold compactFixedPAAxiomSentenceEqTokens
  rw [compactFixedPAAxiomSentenceTokens_canonical certificate hfixed]
  change tokenFormulaEq (compactSentenceTokens certificate.sentence)
      candidateTokens = true <->
    candidateTokens = compactSentenceTokens certificate.sentence
  simp [tokenFormulaEq, eq_comm]

private theorem compactAdditiveFixedPAAxiomRuleCheck_list_iff
    {tokenTable width tokenCount gammaBoundary candidateStart candidateFinish
      resultBoolValue : Nat}
    {Gamma : List (List Nat)} {candidateTokens : List Nat}
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hCandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateStart candidateFinish
        candidateTokens) :
    CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length
        candidateStart candidateFinish candidateTokens.length
        (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
        (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
        resultBoolValue <->
      resultBoolValue = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (candidateTokens,
            compactPAAxiomCertificateTokens certificate))) := by
  simp only [CompactAdditiveFixedPAAxiomRuleCheck]
  rw [compactFixedPAAxiomCandidateRows_canonical_iff
    certificate hfixed hCandidate rfl]
  rw [compactAdditiveFormulaMemberRows_iff_mem hGamma hCandidate]
  have haxiom := compactPAAxiomSentenceEqTokens_fixed_list_iff
    certificate hfixed candidateTokens
  have hmember := tokenFormulaMem_eq_true_iff candidateTokens Gamma
  unfold compactAxmRuleCheck
  cases haxiomValue : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens certificate, candidateTokens) <;>
    cases hmemberValue : tokenFormulaMem candidateTokens Gamma <;>
      simp [compactAdditiveBoolTag, haxiomValue, hmemberValue]
        at haxiom hmember ⊢ <;>
      simp_all <;> omega

private theorem compactPAAxiomSentenceEqTokens_induction_list_iff
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidateTokens : List Nat) :
    compactPAAxiomSentenceEqTokens
        (compactPAAxiomCertificateTokens (PAAxiomCertificate.induction body),
          candidateTokens) =
          true <->
      candidateTokens = compactSentenceTokens
        (PAAxiomCertificate.induction body).sentence := by
  have hparse : compactPAAxiomCertificateTokenParser
      (compactPAAxiomCertificateTokens
        (PAAxiomCertificate.induction body)) = some [] := by
    simpa using compactPAAxiomCertificateTokenParser_canonical_append
      (PAAxiomCertificate.induction body) []
  unfold compactPAAxiomSentenceEqTokens
  rw [if_pos hparse]
  change compactGuardedInductionSentenceEq
      (compactArithmeticFormulaTokens body, candidateTokens) = true <->
    candidateTokens = compactSentenceTokens
      (PAAxiomCertificate.induction body).sentence
  have hgenerated : compactGuardedInductionSentenceTokens
      (compactArithmeticFormulaTokens body, candidateTokens) =
        if (succInd body).fvSup <= compactTokenBitLength candidateTokens then
          some (compactSentenceTokens
            (PAAxiomCertificate.induction body).sentence)
        else none := by
    rw [compactGuardedInductionSentenceTokens,
      compactInductionDepthAndFormulaTokens_canonical]
    change compactGuardedClosureFromDepth
      (candidateTokens,
        ((succInd body).fvSup,
          compactArithmeticFormulaTokens (succInd body))) = _
    unfold compactGuardedClosureFromDepth
    by_cases hguard :
        (succInd body).fvSup <= compactTokenBitLength candidateTokens
    · rw [if_pos hguard, compactFixedAllClosureTokens_canonical,
        if_pos hguard]
      congr 1
      change compactArithmeticFormulaTokens
          (compactInductionClosureFormula body) =
        compactSentenceTokens (PAAxiomCertificate.induction body).sentence
      rw [compactInductionClosureFormula_eq_sentence]
      rfl
    · rw [if_neg hguard, if_neg hguard]
  unfold compactGuardedInductionSentenceEq
  rw [hgenerated]
  by_cases hguard :
      (succInd body).fvSup <= compactTokenBitLength candidateTokens
  · rw [if_pos hguard]
    simp [tokenFormulaEq, eq_comm]
  · rw [if_neg hguard]
    simp only [Bool.false_eq_true, false_iff]
    intro hcandidate
    apply hguard
    have htyped :=
      FoundationCompactSyntaxTransformationTrace.inductionSentenceGuardTrace_complete body
      (PAAxiomCertificate.induction body).sentence (by rfl)
    have hle :=
      (FoundationCompactSyntaxTransformationTrace.inductionSentenceGuardTrace_result_eq_true_iff
        body (PAAxiomCertificate.induction body).sentence).1 htyped
    subst candidateTokens
    rw [compactSentenceTokens, compactTokenBitLength_formula_canonical]
    exact hle

private theorem compactAdditiveInductionPAAxiomRuleCheck_list_iff_of_route
    {tokenTable width tokenCount gammaBoundary resultBoolValue depth : Nat}
    {axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
      openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
      negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
      depthCaptureSlot fixedSlot generatedSlot candidateSlot :
        CompactNatListRowSlot}
    {coordinates : CompactGuardedInductionSentenceRouteCoordinates}
    {Gamma : List (List Nat)} {candidateTokens : List Nat}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hcons : CompactAdditiveNatListConsRows tokenTable width tokenCount
      bodySlot.boundary bodySlot.count axiomSlot.boundary axiomSlot.count 22)
    (hroute : CompactGuardedInductionSentenceRoute
      tokenTable width tokenCount depth bodySlot zeroWitnessSlot
      openZeroWitnessSlot openSuccessorWitnessSlot captureOneSlot emptySlot
      baseSlot negatedBaseSlot stepZeroSlot stepSuccessorSlot
      negatedStepZeroSlot stepDisjunctionSlot quantifiedStepSlot
      negatedQuantifiedStepSlot quantifiedFinalSlot innerDisjunctionSlot
      sentenceSlot fvarListSlot depthCaptureSlot fixedSlot generatedSlot
      coordinates)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body))
    (hCandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateSlot.start candidateSlot.finish
        candidateTokens) :
    CompactAdditiveInductionPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length resultBoolValue
        axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
        openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
        negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
        stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
        quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
        depthCaptureSlot fixedSlot generatedSlot candidateSlot depth
        coordinates <->
      resultBoolValue = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (candidateTokens,
            compactPAAxiomCertificateTokens
              (PAAxiomCertificate.induction body)))) := by
  rcases hroute.sound_canonical body hbody with
    ⟨generatedTokens, hgeneratedLayout, hgeneratedCanonical⟩
  have hgeneratedSentence : generatedTokens =
      compactSentenceTokens (PAAxiomCertificate.induction body).sentence := by
    simpa [compactSentenceTokens] using hgeneratedCanonical
  have hslices : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        generatedSlot.start generatedSlot.finish
        candidateSlot.start candidateSlot.finish <->
      candidateTokens = compactSentenceTokens
        (PAAxiomCertificate.induction body).sentence := by
    constructor
    · intro heq
      have htokens := CompactFixedWidthTokenSlicesEq.natListValues_eq
        heq hgeneratedLayout hCandidate
      simpa [hgeneratedSentence] using htokens
    · intro htokens
      apply CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hgeneratedLayout hCandidate
      simpa [hgeneratedSentence] using htokens.symm
  have hmember := compactAdditiveFormulaMemberRows_iff_mem
    hGamma hCandidate
  have haxiom := compactPAAxiomSentenceEqTokens_induction_list_iff
    body candidateTokens
  have hformulaMember := tokenFormulaMem_eq_true_iff candidateTokens Gamma
  simp only [CompactAdditiveInductionPAAxiomRuleCheck,
    CompactAdditiveInductionPAAxiomRuleCheckShell, hcons, hroute, true_and,
    hslices, hmember]
  cases haxiomValue : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens (PAAxiomCertificate.induction body),
        candidateTokens) <;>
    cases hmemberValue : tokenFormulaMem candidateTokens Gamma <;>
      simp [compactAxmRuleCheck, compactAdditiveBoolTag, haxiomValue,
        hmemberValue] at haxiom hformulaMember ⊢ <;>
      simp_all <;> omega

private theorem inductionEndpoint_sound_certificate
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeInductionPAEndpointCoordinates}
    (hendpoint : CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      coordinates) :
    ∃ body : LO.FirstOrder.ArithmeticSemiformula Nat 1,
    ∃ input suffix : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        inputStart inputFinish input /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        axiomStart axiomFinish
          (compactPAAxiomCertificateTokens
            (PAAxiomCertificate.induction body)) /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixStart suffixFinish suffix /\
      compactStructuralCertificateNodeParser input =
        some (certificateTag,
          (compactPAAxiomCertificateTokens
            (PAAxiomCertificate.induction body), suffix)) := by
  rcases hendpoint.sound with
    ⟨input, endpointAxiom, suffix, hinput, haxiom, hsuffix, hparser⟩
  rcases hendpoint with
    ⟨_hinputRows, htailRows, haxiomRows, _hcertificateTag,
      _houterCons, hinnerCons, hformula, happend⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨decodedAxiom, hdecodedAxiomCount, hdecodedAxiomLayout,
      _hdecodedAxiomRows⟩
  have hendpointAxiom : endpointAxiom = decodedAxiom :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      haxiom hdecodedAxiomLayout).1.symm
  subst endpointAxiom
  rcases hformula.1.realize with
    ⟨formulaInput, hformulaInputCount, hformulaInputLayout,
      hformulaInputRows⟩
  rcases hformula.2.1.realize with
    ⟨formulaSuffix, hformulaSuffixCount, hformulaSuffixLayout,
      _hformulaSuffixRows⟩
  have hsuffixEq : suffix = formulaSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsuffix hformulaSuffixLayout).1.symm
  subst suffix
  rcases hformula.sound_formula with
    ⟨parsedInput, parsedSuffix, hparsedInputLayout, hparsedSuffixLayout,
      hformulaParser⟩
  have hparsedInputEq : parsedInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hparsedInputLayout hformulaInputLayout).1.symm
  have hparsedSuffixEq : parsedSuffix = formulaSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hparsedSuffixLayout hformulaSuffixLayout).1.symm
  subst parsedInput
  subst parsedSuffix
  have hinnerCons' : CompactAdditiveNatListConsRows tokenTable width tokenCount
      coordinates.parser.inputBoundary formulaInput.length
      coordinates.tailBoundary tail.length 22 := by
    simpa only [hformulaInputCount, htailCount] using hinnerCons
  have htailCons : tail = 22 :: formulaInput :=
    hinnerCons'.eq_cons_of_rows hformulaInputRows htailElementRows
  have happend' :
      FoundationCompactNumericListedDirectNatListAppendSlices.CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount axiomStart axiomFinish
        decodedAxiom.length suffixStart suffixFinish formulaSuffix.length
        coordinates.tailStart coordinates.tailFinish tail.length := by
    simpa only [hdecodedAxiomCount, hformulaSuffixCount, htailCount]
      using happend
  have htailAppend : tail = decodedAxiom ++ formulaSuffix :=
    (compactAdditiveNatListAppendSlices_iff_append hdecodedAxiomLayout
      hformulaSuffixLayout htailLayout).mp happend'
  rcases (compactFormulaTokenParser_success_iff
      1 formulaInput formulaSuffix).mp hformulaParser with
    ⟨body, hformulaSplit⟩
  have haxiomAppend : decodedAxiom ++ formulaSuffix =
      (22 :: compactArithmeticFormulaTokens body) ++ formulaSuffix := by
    rw [← htailAppend, htailCons, hformulaSplit]
    simp
  have haxiomCanonical : decodedAxiom =
      compactPAAxiomCertificateTokens (PAAxiomCertificate.induction body) := by
    simpa [compactPAAxiomCertificateTokens] using
      List.append_cancel_right haxiomAppend
  refine ⟨body, input, formulaSuffix, hinput, ?_, hformulaSuffixLayout, ?_⟩
  · simpa [haxiomCanonical] using hdecodedAxiomLayout
  · simpa [haxiomCanonical] using hparser

private theorem fixedEndpoint_sound_certificate
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    (hendpoint : CompactCertificateNodeFixedPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag coordinates) :
    ∃ certificate : PAAxiomCertificate, FixedPAAxiomCertificate certificate /\
    ∃ input suffix : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        inputStart inputFinish input /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixStart suffixFinish suffix /\
      compactStructuralCertificateNodeParser input =
        some (certificateTag,
          (compactPAAxiomCertificateTokens certificate, suffix)) := by
  have hknown :=
    CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact hendpoint
  rcases hendpoint.sound with
    ⟨input, endpointAxiom, suffix, hinput, haxiom, hsuffix, hparser⟩
  have haxiomEq : endpointAxiom = [coordinates.paTag] :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      haxiom hknown).1.symm
  subst endpointAxiom
  rcases hendpoint with ⟨_, _, _, _, _, hfixedTag, _, _, _⟩
  have hpaParser := compactPAAxiomCertificateTokenParser_fixed
    coordinates.paTag [] hfixedTag
  rcases (compactPAAxiomCertificateTokenParser_success_iff
      [coordinates.paTag] []).mp hpaParser with
    ⟨certificate, hcertificateTokens⟩
  have hcertificateTokens' : compactPAAxiomCertificateTokens certificate =
      [coordinates.paTag] := by simpa using hcertificateTokens.symm
  have hfixedCertificate : FixedPAAxiomCertificate certificate := by
    cases certificate <;>
      simp_all [FixedPAAxiomCertificate, compactPAAxiomCertificateTokens,
        CompactFixedPAAxiomTag]
  refine ⟨certificate, hfixedCertificate, input, suffix, hinput, ?_, hsuffix, ?_⟩
  · simpa [hcertificateTokens'] using hknown
  · simpa [hcertificateTokens'] using hparser

private theorem symbolEndpoint_sound_certificate
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    (hendpoint : CompactCertificateNodeSymbolPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag coordinates) :
    ∃ certificate : PAAxiomCertificate, FixedPAAxiomCertificate certificate /\
    ∃ input suffix : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        inputStart inputFinish input /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixStart suffixFinish suffix /\
      compactStructuralCertificateNodeParser input =
        some (certificateTag,
          (compactPAAxiomCertificateTokens certificate, suffix)) := by
  have hknown :=
    CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact hendpoint
  rcases hendpoint.sound with
    ⟨input, endpointAxiom, suffix, hinput, haxiom, hsuffix, hparser⟩
  have haxiomEq : endpointAxiom =
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      haxiom hknown).1.symm
  subst endpointAxiom
  rcases hendpoint with ⟨_, _, _, _, _, _, hvalid, _, _, _, _, _⟩
  have hpaParser := compactPAAxiomCertificateTokenParser_symbol
    coordinates.paTag coordinates.arity coordinates.symbolCode [] hvalid
  rcases (compactPAAxiomCertificateTokenParser_success_iff
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] []).mp
      hpaParser with
    ⟨certificate, hcertificateTokens⟩
  have hcertificateTokens' : compactPAAxiomCertificateTokens certificate =
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] := by
    simpa using hcertificateTokens.symm
  have hfixedCertificate : FixedPAAxiomCertificate certificate := by
    cases certificate <;>
      simp_all [FixedPAAxiomCertificate, compactPAAxiomCertificateTokens,
        CompactSymbolPAAxiomTagValid]
  refine ⟨certificate, hfixedCertificate, input, suffix, hinput, ?_, hsuffix, ?_⟩
  · simpa [hcertificateTokens'] using hknown
  · simpa [hcertificateTokens'] using hparser

theorem CompactNumericVerifierPAAxiomJointLeafRows.sound
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates}
    (hrows : CompactNumericVerifierPAAxiomJointLeafRows c) :
    ∃ Gamma : List (List Nat), ∃ candidateTokens : List Nat,
    ∃ certificate : PAAxiomCertificate, ∃ input suffix : List Nat,
      Gamma.length = c.gammaCount /\
      candidateTokens.length = c.candidate.count /\
      (compactPAAxiomCertificateTokens certificate).length =
        c.ruleAxiom.count /\
      CompactAdditiveNatListListDirectLayout c.ruleTable c.ruleWidth
        c.ruleTokenCount c.gammaStart c.gammaFinish Gamma /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout c.ruleTable c.ruleWidth
          c.ruleTokenCount c.gammaBoundary Gamma /\
      CompactAdditiveNatListDirectLayout c.ruleTable c.ruleWidth
        c.ruleTokenCount c.candidate.start c.candidate.finish
          candidateTokens /\
      CompactAdditiveNatListDirectLayout c.ruleTable c.ruleWidth
        c.ruleTokenCount c.ruleAxiom.start c.ruleAxiom.finish
          (compactPAAxiomCertificateTokens certificate) /\
      CompactAdditiveNatListDirectLayout c.endpointTable c.endpointWidth
        c.endpointTokenCount c.endpointAxiomStart c.endpointAxiomFinish
          (compactPAAxiomCertificateTokens certificate) /\
      CompactAdditiveNatListDirectLayout c.endpointTable c.endpointWidth
        c.endpointTokenCount c.inputStart c.inputFinish input /\
      CompactAdditiveNatListDirectLayout c.endpointTable c.endpointWidth
        c.endpointTokenCount c.suffixStart c.suffixFinish suffix /\
      compactStructuralCertificateNodeParser input =
        some (c.certificateTag,
          (compactPAAxiomCertificateTokens certificate, suffix)) /\
      c.resultBool = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (candidateTokens,
            compactPAAxiomCertificateTokens certificate))) := by
  rcases hrows with
    ⟨hGammaRows, hCandidateRows, hRuleAxiomRows, hcross, _hproofTag,
      hfixedOrSymbol | hinduction⟩
  · rcases hGammaRows.realize with
      ⟨Gamma, hGammaCount, hGammaLayout, hGammaElementRows⟩
    rcases hCandidateRows.realize with
      ⟨candidateTokens, hCandidateCount, hCandidateLayout, _⟩
    rcases hRuleAxiomRows.realize with
      ⟨ruleAxiomTokens, hRuleAxiomCount, hRuleAxiomLayout,
        hRuleAxiomElementRows⟩
    rcases hfixedOrSymbol with hfixed | hsymbol
    · rcases hfixed with ⟨hendpoint, hcheck⟩
      rcases fixedEndpoint_sound_certificate hendpoint with
        ⟨certificate, hfixedCertificate, input, suffix, hinput,
          hEndpointAxiom, hsuffix, hparser⟩
      have hRuleAxiomEq : ruleAxiomTokens =
          compactPAAxiomCertificateTokens certificate :=
        hcross.natListValues_eq hEndpointAxiom hRuleAxiomLayout
      subst ruleAxiomTokens
      have hknown :=
        CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact
          hendpoint
      have hcertificateCoordinates : compactPAAxiomCertificateTokens
          certificate = [c.fixedEndpoint.paTag] :=
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hEndpointAxiom hknown).1.symm
      have hcheck' : CompactAdditiveFixedPAAxiomRuleCheck c.ruleTable
          c.ruleWidth c.ruleTokenCount c.gammaBoundary Gamma.length
          c.candidate.start c.candidate.finish candidateTokens.length
          (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
          c.resultBool := by
        simpa [hGammaCount, hCandidateCount, hcertificateCoordinates,
          compactTokenAt] using hcheck
      have hresult :=
        (compactAdditiveFixedPAAxiomRuleCheck_list_iff certificate
          hfixedCertificate hGammaElementRows hCandidateLayout).mp hcheck'
      exact ⟨Gamma, candidateTokens, certificate, input, suffix,
        hGammaCount, hCandidateCount, hRuleAxiomCount, hGammaLayout,
        hGammaElementRows, hCandidateLayout, hRuleAxiomLayout,
        hEndpointAxiom, hinput, hsuffix, hparser, hresult⟩
    · rcases hsymbol with ⟨hendpoint, hcheck⟩
      rcases symbolEndpoint_sound_certificate hendpoint with
        ⟨certificate, hfixedCertificate, input, suffix, hinput,
          hEndpointAxiom, hsuffix, hparser⟩
      have hRuleAxiomEq : ruleAxiomTokens =
          compactPAAxiomCertificateTokens certificate :=
        hcross.natListValues_eq hEndpointAxiom hRuleAxiomLayout
      subst ruleAxiomTokens
      have hknown :=
        CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact
          hendpoint
      have hcertificateCoordinates : compactPAAxiomCertificateTokens
          certificate = [c.symbolEndpoint.paTag, c.symbolEndpoint.arity,
            c.symbolEndpoint.symbolCode] :=
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hEndpointAxiom hknown).1.symm
      have hcheck' : CompactAdditiveFixedPAAxiomRuleCheck c.ruleTable
          c.ruleWidth c.ruleTokenCount c.gammaBoundary Gamma.length
          c.candidate.start c.candidate.finish candidateTokens.length
          (compactTokenAt 0 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 1 (compactPAAxiomCertificateTokens certificate))
          (compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))
          c.resultBool := by
        simpa [hGammaCount, hCandidateCount, hcertificateCoordinates,
          compactTokenAt] using hcheck
      have hresult :=
        (compactAdditiveFixedPAAxiomRuleCheck_list_iff certificate
          hfixedCertificate hGammaElementRows hCandidateLayout).mp hcheck'
      exact ⟨Gamma, candidateTokens, certificate, input, suffix,
        hGammaCount, hCandidateCount, hRuleAxiomCount, hGammaLayout,
        hGammaElementRows, hCandidateLayout, hRuleAxiomLayout,
        hEndpointAxiom, hinput, hsuffix, hparser, hresult⟩
  · rcases hGammaRows.realize with
      ⟨Gamma, hGammaCount, hGammaLayout, hGammaElementRows⟩
    rcases hCandidateRows.realize with
      ⟨candidateTokens, hCandidateCount, hCandidateLayout, _⟩
    rcases hRuleAxiomRows.realize with
      ⟨ruleAxiomTokens, hRuleAxiomCount, hRuleAxiomLayout,
        hRuleAxiomElementRows⟩
    rcases hinduction with ⟨hendpoint, hrule⟩
    rcases inductionEndpoint_sound_certificate hendpoint with
      ⟨body, input, suffix, hinput, hEndpointAxiom, hsuffix, hparser⟩
    have hRuleAxiomEq : ruleAxiomTokens = compactPAAxiomCertificateTokens
        (PAAxiomCertificate.induction body) :=
      hcross.natListValues_eq hEndpointAxiom hRuleAxiomLayout
    subst ruleAxiomTokens
    have hroute := hrule.1
    have hcons := hrule.2.1
    rcases hroute.1.1.2.2.1.2.1.realize with
      ⟨bodyTokens, hbodyCount, hbodyLayout, hbodyRows⟩
    have hcons' : CompactAdditiveNatListConsRows c.ruleTable c.ruleWidth
        c.ruleTokenCount c.body.boundary bodyTokens.length
        c.ruleAxiom.boundary
          (compactPAAxiomCertificateTokens
            (PAAxiomCertificate.induction body)).length 22 := by
      simpa only [hbodyCount, hRuleAxiomCount] using hcons
    have haxiomCons : compactPAAxiomCertificateTokens
        (PAAxiomCertificate.induction body) = 22 :: bodyTokens :=
      hcons'.eq_cons_of_rows hbodyRows hRuleAxiomElementRows
    have hbodyTokens : bodyTokens = compactArithmeticFormulaTokens body := by
      simpa [compactPAAxiomCertificateTokens] using
        (List.cons.inj haxiomCons.symm).2
    have hbodyLayout' : CompactAdditiveNatListDirectLayout c.ruleTable
        c.ruleWidth c.ruleTokenCount c.body.start c.body.finish
          (compactArithmeticFormulaTokens body) := by
      simpa [hbodyTokens] using hbodyLayout
    have hrule' : CompactAdditiveInductionPAAxiomRuleCheck c.ruleTable
        c.ruleWidth c.ruleTokenCount c.gammaBoundary Gamma.length c.resultBool
        c.ruleAxiom c.body c.zeroWitness c.openZeroWitness
        c.openSuccessorWitness c.captureOne c.empty c.base c.negatedBase
        c.stepZero c.stepSuccessor c.negatedStepZero c.stepDisjunction
        c.quantifiedStep c.negatedQuantifiedStep c.quantifiedFinal
        c.innerDisjunction c.sentence c.fvarList c.depthCapture c.fixed
        c.generated c.candidate c.depth c.route := by
      simpa [hGammaCount] using hrule
    have hresult :=
      (compactAdditiveInductionPAAxiomRuleCheck_list_iff_of_route body hcons
        hroute hGammaElementRows hbodyLayout' hCandidateLayout).mp hrule'
    exact ⟨Gamma, candidateTokens, PAAxiomCertificate.induction body,
      input, suffix, hGammaCount, hCandidateCount, hRuleAxiomCount,
      hGammaLayout, hGammaElementRows, hCandidateLayout, hRuleAxiomLayout,
      hEndpointAxiom, hinput, hsuffix, hparser, hresult⟩

def compactPAAxiomJointInactiveFixedEndpoint :
    CompactCertificateNodeFixedPAEndpointCoordinates where
  inputBoundary := 0
  inputCount := 0
  inputBoundarySize := 0
  tailStart := 0
  tailFinish := 0
  tailBoundary := 0
  tailCount := 0
  tailBoundarySize := 0
  axiomBoundary := 0
  axiomCount := 0
  axiomBoundarySize := 0
  suffixBoundary := 0
  suffixCount := 0
  suffixBoundarySize := 0
  paTag := 0

def compactPAAxiomJointInactiveSymbolEndpoint :
    CompactCertificateNodeSymbolPAEndpointCoordinates where
  inputBoundary := 0
  inputCount := 0
  inputBoundarySize := 0
  tailStart := 0
  tailFinish := 0
  tailBoundary := 0
  tailCount := 0
  tailBoundarySize := 0
  axiomBoundary := 0
  axiomCount := 0
  axiomBoundarySize := 0
  suffixBoundary := 0
  suffixCount := 0
  suffixBoundarySize := 0
  paTag := 0
  arity := 0
  symbolCode := 0

def compactPAAxiomJointInactiveInductionEndpoint :
    CompactCertificateNodeInductionPAEndpointCoordinates where
  inputBoundary := 0
  inputCount := 0
  inputBoundarySize := 0
  tailStart := 0
  tailFinish := 0
  tailBoundary := 0
  tailCount := 0
  tailBoundarySize := 0
  axiomBoundary := 0
  axiomCount := 0
  axiomBoundarySize := 0
  parser :=
    { inputBoundary := 0
      inputCount := 0
      inputBoundarySize := 0
      expectedBoundary := 0
      expectedCount := 0
      expectedBoundarySize := 0
      stateBoundary := 0
      stateCount := 0
      tableWidth := 0
      valueBound := 0 }

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem exists_nonInductionEndpoint
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    ∃ tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish,
    ∃ fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
    ∃ symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) /\
      ((CompactCertificateNodeFixedPAEndpointGraph tokenTable width tokenCount
          inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish
          1 fixedCoordinates /\
        fixedCoordinates.paTag =
          compactTokenAt 0 (compactPAAxiomCertificateTokens certificate) /\
        compactTokenAt 1 (compactPAAxiomCertificateTokens certificate) = 0 /\
        compactTokenAt 2 (compactPAAxiomCertificateTokens certificate) = 0) \/
       (CompactCertificateNodeSymbolPAEndpointGraph tokenTable width tokenCount
          inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish
          1 symbolCoordinates /\
        symbolCoordinates.paTag =
          compactTokenAt 0 (compactPAAxiomCertificateTokens certificate) /\
        symbolCoordinates.arity =
          compactTokenAt 1 (compactPAAxiomCertificateTokens certificate) /\
        symbolCoordinates.symbolCode =
          compactTokenAt 2 (compactPAAxiomCertificateTokens certificate))) := by
  let tokens := compactPAAxiomCertificateTokens certificate
  by_cases hsymbol : compactTokenAt 0 tokens = 3 \/ compactTokenAt 0 tokens = 4
  · have hvalid : CompactSymbolPAAxiomTagValid (compactTokenAt 0 tokens)
      (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt,
          CompactSymbolPAAxiomTagValid] <;>
        first
        | exact arithmeticFuncCodeValid_encode _
        | exact arithmeticRelCodeValid_encode _
    rcases exists_compactCertificateNodeSymbolPAEndpointGraph_of_results_with_inputLayout
        (compactTokenAt 0 tokens) (compactTokenAt 1 tokens)
        (compactTokenAt 2 tokens) [] hvalid with
      ⟨table, width, count, inputStart, inputFinish, axiomStart, axiomFinish,
        suffixStart, suffixFinish, coordinates, hinput, hgraph⟩
    have haxiom :=
      CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact hgraph
    rcases hgraph.sound with
      ⟨decodedInput, decodedAxiom, decodedSuffix, hdecodedInput,
        hdecodedAxiom, _hdecodedSuffix, hparser⟩
    have hinputEq : decodedInput =
        (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
          compactTokenAt 2 tokens :: []) :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hdecodedInput hinput).1.symm
    subst decodedInput
    have hparserExpected : compactStructuralCertificateNodeParser
        (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
          compactTokenAt 2 tokens :: []) =
        some (1, ([compactTokenAt 0 tokens, compactTokenAt 1 tokens,
          compactTokenAt 2 tokens], [])) := by
      simp [compactStructuralCertificateNodeParser,
        compactPAAxiomCertificateTokenParser_symbol,
        hvalid, consumedTokenPrefix]
    rw [hparserExpected] at hparser
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
    have hdecodedAxiomEq : decodedAxiom =
        [compactTokenAt 0 tokens, compactTokenAt 1 tokens,
          compactTokenAt 2 tokens] := by simpa using hparser.1.symm
    have hcoordinateList :
        [coordinates.paTag, coordinates.arity, coordinates.symbolCode] =
          [compactTokenAt 0 tokens, compactTokenAt 1 tokens,
            compactTokenAt 2 tokens] := by
      rw [← hdecodedAxiomEq]
      exact
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hdecodedAxiom haxiom).1
    simp at hcoordinateList
    have htokens : tokens = [compactTokenAt 0 tokens,
        compactTokenAt 1 tokens, compactTokenAt 2 tokens] := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    refine ⟨table, width, count, inputStart, inputFinish, axiomStart,
      axiomFinish, suffixStart, suffixFinish,
      compactPAAxiomJointInactiveFixedEndpoint, coordinates, ?_, Or.inr ?_⟩
    · change CompactAdditiveNatListDirectLayout table width count axiomStart
        axiomFinish tokens
      rw [htokens]
      simpa only [hcoordinateList.1, hcoordinateList.2.1,
        hcoordinateList.2.2] using haxiom
    · exact ⟨hgraph, hcoordinateList.1, hcoordinateList.2.1,
        hcoordinateList.2.2⟩
  · have htag : CompactFixedPAAxiomTag (compactTokenAt 0 tokens) := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt,
          CompactFixedPAAxiomTag]
    have hone : compactTokenAt 1 tokens = 0 := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    have htwo : compactTokenAt 2 tokens = 0 := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    rcases exists_compactCertificateNodeFixedPAEndpointGraph_of_results_with_inputLayout
        (compactTokenAt 0 tokens) [] htag with
      ⟨table, width, count, inputStart, inputFinish, axiomStart, axiomFinish,
        suffixStart, suffixFinish, coordinates, hinput, hgraph⟩
    have haxiom :=
      CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact hgraph
    rcases hgraph.sound with
      ⟨decodedInput, decodedAxiom, decodedSuffix, hdecodedInput,
        hdecodedAxiom, _hdecodedSuffix, hparser⟩
    have hinputEq : decodedInput =
        (1 :: compactTokenAt 0 tokens :: []) :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hdecodedInput hinput).1.symm
    subst decodedInput
    have hparserExpected : compactStructuralCertificateNodeParser
        (1 :: compactTokenAt 0 tokens :: []) =
        some (1, ([compactTokenAt 0 tokens], [])) := by
      simp [compactStructuralCertificateNodeParser,
        compactPAAxiomCertificateTokenParser_fixed,
        htag, consumedTokenPrefix]
    rw [hparserExpected] at hparser
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
    have hdecodedAxiomEq : decodedAxiom = [compactTokenAt 0 tokens] := by
      simpa using hparser.1.symm
    have hcoordinateList : [coordinates.paTag] =
        [compactTokenAt 0 tokens] := by
      rw [← hdecodedAxiomEq]
      exact
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hdecodedAxiom haxiom).1
    simp at hcoordinateList
    have htokens : tokens = [compactTokenAt 0 tokens] := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    refine ⟨table, width, count, inputStart, inputFinish, axiomStart,
      axiomFinish, suffixStart, suffixFinish, coordinates,
      compactPAAxiomJointInactiveSymbolEndpoint, ?_, Or.inl ?_⟩
    · change CompactAdditiveNatListDirectLayout table width count axiomStart
        axiomFinish tokens
      rw [htokens]
      simpa only [hcoordinateList] using haxiom
    · exact ⟨hgraph, hcoordinateList, hone, htwo⟩

def CompactCanonicalNumericVerifierPAAxiomJointLeafRows
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Prop :=
  CompactNumericVerifierPAAxiomJointLeafRows c /\
    c.resultBool = compactAdditiveBoolTag
      (compactAxmRuleCheck
        (Gamma, (compactSentenceTokens candidate,
          compactPAAxiomCertificateTokens certificate))) /\
    CompactAdditiveNatListListDirectLayout c.ruleTable c.ruleWidth
      c.ruleTokenCount c.gammaStart c.gammaFinish Gamma /\
    CompactAdditiveNatListDirectLayout c.ruleTable c.ruleWidth
      c.ruleTokenCount c.candidate.start c.candidate.finish
        (compactSentenceTokens candidate) /\
    CompactAdditiveNatListDirectLayout c.ruleTable c.ruleWidth
      c.ruleTokenCount c.ruleAxiom.start c.ruleAxiom.finish
        (compactPAAxiomCertificateTokens certificate) /\
    CompactAdditiveNatListDirectLayout c.endpointTable c.endpointWidth
      c.endpointTokenCount c.endpointAxiomStart c.endpointAxiomFinish
        (compactPAAxiomCertificateTokens certificate)

private theorem exists_fixedCanonicalJoint
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
      Gamma candidate certificate c := by
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := compactPAAxiomCertificateTokens certificate
  let chunks := compactFixedPAAxiomLeafRuleRowsCanonicalChunks
    Gamma candidate certificate
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let ruleTable := compactFixedWidthTableCode width tokens
  let gammaStart := (compactPackedChunkPrefix chunks 0).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let ruleAxiom := compactPackedNatListSlot chunks 1 certificateTokens
  let candidateSlot := compactPackedNatListSlot chunks 2 candidateTokens
  have hGammaLayout : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma := by
    simpa [ruleTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 0 Gamma
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaWitness : CompactAdditiveNatListListWitnessRows ruleTable width
      tokens.length gammaStart Gamma.length gammaFinish gammaBoundary
        (Nat.size gammaBoundary) :=
    ⟨hGammaStructure,
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hGammaElementRows,
      rfl, by simpa using hGammaSize⟩
  have hRuleAxiom := compactPackedNatListSlot_canonical chunks 1
    certificateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      certificateTokens])
  have hCandidate := compactPackedNatListSlot_canonical chunks 2
    candidateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      candidateTokens])
  dsimp only [ruleAxiom, candidateSlot] at hRuleAxiom hCandidate
  have hfixedRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
      tokens.length gammaBoundary Gamma.length candidateSlot.start
      candidateSlot.finish candidateSlot.count
      (compactTokenAt 0 certificateTokens) (compactTokenAt 1 certificateTokens)
      (compactTokenAt 2 certificateTokens)
      (compactAdditiveBoolTag
        (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))) := by
    have hcanonical :=
      (compactAdditiveFixedPAAxiomRuleCheck_canonical_iff candidate certificate
        hfixed hGammaElementRows hCandidate.2.2.1).2 rfl
    simpa [candidateTokens, certificateTokens, candidateSlot, hCandidate.1]
      using hcanonical
  rcases exists_nonInductionEndpoint certificate hfixed with
    ⟨endpointTable, endpointWidth, endpointTokenCount, inputStart, inputFinish,
      endpointAxiomStart, endpointAxiomFinish, suffixStart, suffixFinish,
      fixedEndpoint, symbolEndpoint, hEndpointAxiom,
      hfixedEndpoint | hsymbolEndpoint⟩
  · rcases hfixedEndpoint with
      ⟨hendpoint, hpaTag, harity, hsymbolCode⟩
    have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hEndpointAxiom hRuleAxiom.2.2.1
    have hjointRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
        tokens.length gammaBoundary Gamma.length candidateSlot.start
        candidateSlot.finish candidateSlot.count fixedEndpoint.paTag 0 0
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (Gamma, (candidateTokens, certificateTokens)))) := by
      simpa [certificateTokens, hpaTag, harity, hsymbolCode] using hfixedRule
    let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
      { endpointTable := endpointTable
        endpointWidth := endpointWidth
        endpointTokenCount := endpointTokenCount
        ruleTable := ruleTable
        ruleWidth := width
        ruleTokenCount := tokens.length
        inputStart := inputStart
        inputFinish := inputFinish
        endpointAxiomStart := endpointAxiomStart
        endpointAxiomFinish := endpointAxiomFinish
        formulaStart := 0
        formulaFinish := 0
        suffixStart := suffixStart
        suffixFinish := suffixFinish
        proofTag := 1
        certificateTag := 1
        gammaStart := gammaStart
        gammaFinish := gammaFinish
        gammaBoundary := gammaBoundary
        gammaCount := Gamma.length
        gammaBoundarySize := Nat.size gammaBoundary
        candidate := candidateSlot
        ruleAxiom := ruleAxiom
        resultBool := compactAdditiveBoolTag
          (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
        depth := 0
        fixedEndpoint := fixedEndpoint
        symbolEndpoint := symbolEndpoint
        inductionEndpoint := compactPAAxiomJointInactiveInductionEndpoint
        body := compactPAAxiomLeafInactiveNatListRowSlot
        zeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openZeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openSuccessorWitness := compactPAAxiomLeafInactiveNatListRowSlot
        captureOne := compactPAAxiomLeafInactiveNatListRowSlot
        empty := compactPAAxiomLeafInactiveNatListRowSlot
        base := compactPAAxiomLeafInactiveNatListRowSlot
        negatedBase := compactPAAxiomLeafInactiveNatListRowSlot
        stepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepSuccessor := compactPAAxiomLeafInactiveNatListRowSlot
        negatedStepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        negatedQuantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedFinal := compactPAAxiomLeafInactiveNatListRowSlot
        innerDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        sentence := compactPAAxiomLeafInactiveNatListRowSlot
        fvarList := compactPAAxiomLeafInactiveNatListRowSlot
        depthCapture := compactPAAxiomLeafInactiveNatListRowSlot
        fixed := compactPAAxiomLeafInactiveNatListRowSlot
        generated := compactPAAxiomLeafInactiveNatListRowSlot
        route := compactPAAxiomLeafInactiveRouteCoordinates }
    refine ⟨c, ?_⟩
    dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
      CompactNumericVerifierPAAxiomJointLeafRows]
    refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
      hRuleAxiom.2.2.1, hEndpointAxiom⟩
    exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
      Or.inl (Or.inl ⟨hendpoint, hjointRule⟩)⟩
  · rcases hsymbolEndpoint with
      ⟨hendpoint, hpaTag, harity, hsymbolCode⟩
    have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hEndpointAxiom hRuleAxiom.2.2.1
    have hjointRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
        tokens.length gammaBoundary Gamma.length candidateSlot.start
        candidateSlot.finish candidateSlot.count symbolEndpoint.paTag
        symbolEndpoint.arity symbolEndpoint.symbolCode
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (Gamma, (candidateTokens, certificateTokens)))) := by
      simpa [certificateTokens, hpaTag, harity, hsymbolCode] using hfixedRule
    let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
      { endpointTable := endpointTable
        endpointWidth := endpointWidth
        endpointTokenCount := endpointTokenCount
        ruleTable := ruleTable
        ruleWidth := width
        ruleTokenCount := tokens.length
        inputStart := inputStart
        inputFinish := inputFinish
        endpointAxiomStart := endpointAxiomStart
        endpointAxiomFinish := endpointAxiomFinish
        formulaStart := 0
        formulaFinish := 0
        suffixStart := suffixStart
        suffixFinish := suffixFinish
        proofTag := 1
        certificateTag := 1
        gammaStart := gammaStart
        gammaFinish := gammaFinish
        gammaBoundary := gammaBoundary
        gammaCount := Gamma.length
        gammaBoundarySize := Nat.size gammaBoundary
        candidate := candidateSlot
        ruleAxiom := ruleAxiom
        resultBool := compactAdditiveBoolTag
          (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
        depth := 0
        fixedEndpoint := fixedEndpoint
        symbolEndpoint := symbolEndpoint
        inductionEndpoint := compactPAAxiomJointInactiveInductionEndpoint
        body := compactPAAxiomLeafInactiveNatListRowSlot
        zeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openZeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openSuccessorWitness := compactPAAxiomLeafInactiveNatListRowSlot
        captureOne := compactPAAxiomLeafInactiveNatListRowSlot
        empty := compactPAAxiomLeafInactiveNatListRowSlot
        base := compactPAAxiomLeafInactiveNatListRowSlot
        negatedBase := compactPAAxiomLeafInactiveNatListRowSlot
        stepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepSuccessor := compactPAAxiomLeafInactiveNatListRowSlot
        negatedStepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        negatedQuantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedFinal := compactPAAxiomLeafInactiveNatListRowSlot
        innerDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        sentence := compactPAAxiomLeafInactiveNatListRowSlot
        fvarList := compactPAAxiomLeafInactiveNatListRowSlot
        depthCapture := compactPAAxiomLeafInactiveNatListRowSlot
        fixed := compactPAAxiomLeafInactiveNatListRowSlot
        generated := compactPAAxiomLeafInactiveNatListRowSlot
        route := compactPAAxiomLeafInactiveRouteCoordinates }
    refine ⟨c, ?_⟩
    dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
      CompactNumericVerifierPAAxiomJointLeafRows]
    refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
      hRuleAxiom.2.2.1, hEndpointAxiom⟩
    exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
      Or.inl (Or.inr ⟨hendpoint, hjointRule⟩)⟩

set_option maxHeartbeats 2000000 in
private theorem exists_inductionCanonicalJoint
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
      Gamma candidate (PAAxiomCertificate.induction body) c := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := 22 :: bodyTokens
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let ruleTable := compactFixedWidthTableCode width tokens
  let resultBool := compactAdditiveBoolTag
    (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
  let gammaStart := (compactPackedChunkPrefix chunks 39).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let ruleAxiom := compactPackedNatListSlot chunks 37 certificateTokens
  let bodySlot := compactPackedNatListSlot chunks 0 data.body
  let zeroWitness := compactPackedNatListSlot chunks 1 data.zeroWitness
  let openZeroWitness := compactPackedNatListSlot chunks 2 data.openZeroWitness
  let openSuccessorWitness :=
    compactPackedNatListSlot chunks 3 data.openSuccessorWitness
  let captureOne := compactPackedNatListSlot chunks 4 data.captureOne
  let empty := compactPackedNatListSlot chunks 5 data.empty
  let base := compactPackedNatListSlot chunks 6 data.base
  let negatedBase := compactPackedNatListSlot chunks 7 data.negatedBase
  let stepZero := compactPackedNatListSlot chunks 10 data.stepZero
  let stepSuccessor := compactPackedNatListSlot chunks 13 data.stepSuccessor
  let negatedStepZero :=
    compactPackedNatListSlot chunks 14 data.negatedStepZero
  let stepDisjunction :=
    compactPackedNatListSlot chunks 15 data.stepDisjunction
  let quantifiedStep := compactPackedNatListSlot chunks 16 data.quantifiedStep
  let negatedQuantifiedStep :=
    compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep
  let quantifiedFinal :=
    compactPackedNatListSlot chunks 18 data.quantifiedFinal
  let innerDisjunction :=
    compactPackedNatListSlot chunks 19 data.innerDisjunction
  let sentence := compactPackedNatListSlot chunks 20 data.sentence
  let fvarList := compactPackedNatListSlot chunks 21 data.fvarList
  let depthCapture := compactPackedNatListSlot chunks 22 data.depthCapture
  let fixed := compactPackedNatListSlot chunks 23 data.fixed
  let generated := compactPackedNatListSlot chunks 24 data.generated
  let candidateSlot := compactPackedNatListSlot chunks 38 candidateTokens
  have hchunksLength : chunks.length = 40 := by
    simp [chunks, compactInductionPAAxiomRuleCheckChunks,
      compactInductionPAAxiomRuleCheckExtraChunks,
      compactGuardedInductionRouteChunks]
  have hGammaLayout : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma := by
    simpa [ruleTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 39 Gamma
        (by omega)
        (by
          rw [← List.getI_eq_getElem chunks (by omega)]
          simp [chunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaWitness : CompactAdditiveNatListListWitnessRows ruleTable width
      tokens.length gammaStart Gamma.length gammaFinish gammaBoundary
        (Nat.size gammaBoundary) :=
    ⟨hGammaStructure,
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hGammaElementRows,
      rfl, by simpa using hGammaSize⟩
  have slotCanonical (index : Nat) (values : List Nat)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode values) :
      CompactPackedNatListSlotCanonical ruleTable width tokens.length
        (compactPackedNatListSlot chunks index values) values := by
    simpa [ruleTable, width, tokens] using
      compactPackedNatListSlot_canonical chunks index values hindex hchunk
  have hBody : CompactPackedNatListSlotCanonical ruleTable width tokens.length
      bodySlot bodyTokens := by
    apply slotCanonical 0 bodyTokens (by omega)
    rw [show chunks[0] = chunks.getI 0 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, bodyTokens]
  have hRuleAxiom : CompactPackedNatListSlotCanonical ruleTable width
      tokens.length ruleAxiom certificateTokens := by
    apply slotCanonical 37 certificateTokens (by omega)
    rw [show chunks[37] = chunks.getI 37 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, certificateTokens]
  have hCandidate : CompactPackedNatListSlotCanonical ruleTable width
      tokens.length candidateSlot candidateTokens := by
    apply slotCanonical 38 candidateTokens (by omega)
    rw [show chunks[38] = chunks.getI 38 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, candidateTokens]
  rcases exists_compactCanonicalInductionPAAxiomRuleCheck body candidate Gamma with
    ⟨canonicalGammaBoundary, route, hcanonicalRule⟩
  have hcanonicalRule' : CompactAdditiveInductionPAAxiomRuleCheck ruleTable
      width tokens.length canonicalGammaBoundary Gamma.length resultBool
      ruleAxiom bodySlot zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidateSlot data.depth route := by
    simpa [CompactCanonicalInductionPAAxiomRuleCheck, bodyTokens,
      candidateTokens, certificateTokens, data, chunks, tokens, width,
      ruleTable, resultBool, ruleAxiom, bodySlot, zeroWitness,
      openZeroWitness, openSuccessorWitness, captureOne, empty, base,
      negatedBase, stepZero, stepSuccessor, negatedStepZero,
      stepDisjunction, quantifiedStep, negatedQuantifiedStep,
      quantifiedFinal, innerDisjunction, sentence, fvarList, depthCapture,
      fixed, generated, candidateSlot] using hcanonicalRule
  have hrule : CompactAdditiveInductionPAAxiomRuleCheck ruleTable width
      tokens.length gammaBoundary Gamma.length resultBool ruleAxiom bodySlot
      zeroWitness openZeroWitness openSuccessorWitness captureOne empty base
      negatedBase stepZero stepSuccessor negatedStepZero stepDisjunction
      quantifiedStep negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence fvarList depthCapture fixed generated candidateSlot data.depth
      route :=
    (compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
      (resultBoolValue := resultBool) body candidate hcanonicalRule'.2.1
      hcanonicalRule'.1 hGammaElementRows hBody.2.2.1
      hCandidate.2.2.1).2 (by
        simp [resultBool, bodyTokens, candidateTokens, certificateTokens,
          compactPAAxiomCertificateTokens])
  have hformulaParser : compactFormulaTokenParser 1 bodyTokens = some [] := by
    simpa [bodyTokens] using compactFormulaTokenParser_canonical_append body []
  rcases exists_compactCertificateNodeInductionPAEndpointGraph_of_results_with_inputLayout
      bodyTokens [] hformulaParser with
    ⟨endpointTable, endpointWidth, endpointTokenCount, inputStart, inputFinish,
      endpointAxiomStart, endpointAxiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, inductionEndpoint, hinput, hendpoint⟩
  rcases inductionEndpoint_sound_certificate hendpoint with
    ⟨parsedBody, decodedInput, decodedSuffix, hdecodedInput,
      hEndpointParsedAxiom, _hdecodedSuffix, hparser⟩
  have hinputEq : decodedInput = (1 :: 22 :: bodyTokens) :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedInput hinput).1.symm
  subst decodedInput
  have hpaParser : compactPAAxiomCertificateTokenParser certificateTokens =
      some [] := by
    simpa [certificateTokens, bodyTokens, compactPAAxiomCertificateTokens]
      using compactPAAxiomCertificateTokenParser_canonical_append
        (PAAxiomCertificate.induction body) []
  have hparserExpected : compactStructuralCertificateNodeParser
      (1 :: 22 :: bodyTokens) =
      some (1, (certificateTokens, [])) := by
    simp [compactStructuralCertificateNodeParser, certificateTokens,
      hpaParser, consumedTokenPrefix]
  rw [hparserExpected] at hparser
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
  have hcertificateEq : compactPAAxiomCertificateTokens
      (PAAxiomCertificate.induction parsedBody) = certificateTokens := by
    simpa using hparser.1.symm
  have hEndpointAxiom : CompactAdditiveNatListDirectLayout endpointTable
      endpointWidth endpointTokenCount endpointAxiomStart endpointAxiomFinish
        certificateTokens := by
    simpa [hcertificateEq] using hEndpointParsedAxiom
  have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hEndpointAxiom hRuleAxiom.2.2.1
  let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
    { endpointTable := endpointTable
      endpointWidth := endpointWidth
      endpointTokenCount := endpointTokenCount
      ruleTable := ruleTable
      ruleWidth := width
      ruleTokenCount := tokens.length
      inputStart := inputStart
      inputFinish := inputFinish
      endpointAxiomStart := endpointAxiomStart
      endpointAxiomFinish := endpointAxiomFinish
      formulaStart := formulaStart
      formulaFinish := formulaFinish
      suffixStart := suffixStart
      suffixFinish := suffixFinish
      proofTag := 1
      certificateTag := 1
      gammaStart := gammaStart
      gammaFinish := gammaFinish
      gammaBoundary := gammaBoundary
      gammaCount := Gamma.length
      gammaBoundarySize := Nat.size gammaBoundary
      candidate := candidateSlot
      ruleAxiom := ruleAxiom
      resultBool := resultBool
      depth := data.depth
      fixedEndpoint := compactPAAxiomJointInactiveFixedEndpoint
      symbolEndpoint := compactPAAxiomJointInactiveSymbolEndpoint
      inductionEndpoint := inductionEndpoint
      body := bodySlot
      zeroWitness := zeroWitness
      openZeroWitness := openZeroWitness
      openSuccessorWitness := openSuccessorWitness
      captureOne := captureOne
      empty := empty
      base := base
      negatedBase := negatedBase
      stepZero := stepZero
      stepSuccessor := stepSuccessor
      negatedStepZero := negatedStepZero
      stepDisjunction := stepDisjunction
      quantifiedStep := quantifiedStep
      negatedQuantifiedStep := negatedQuantifiedStep
      quantifiedFinal := quantifiedFinal
      innerDisjunction := innerDisjunction
      sentence := sentence
      fvarList := fvarList
      depthCapture := depthCapture
      fixed := fixed
      generated := generated
      route := route }
  refine ⟨c, ?_⟩
  dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
    CompactNumericVerifierPAAxiomJointLeafRows]
  refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
    hRuleAxiom.2.2.1, ?_⟩
  · exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
      Or.inr ⟨hendpoint, hrule⟩⟩
  · simpa [certificateTokens, bodyTokens, compactPAAxiomCertificateTokens]
      using hEndpointAxiom

set_option maxHeartbeats 3000000 in
theorem CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
      Gamma candidate certificate c := by
  rcases fixedPAAxiomCertificate_or_induction certificate with
    hfixed | ⟨body, rfl⟩
  · exact exists_fixedCanonicalJoint Gamma candidate certificate hfixed
  · exact exists_inductionCanonicalJoint Gamma candidate body

theorem compactNumericVerifierPAAxiomJointLeafRowsDef_converse
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    ∃ c, compactNumericVerifierPAAxiomJointLeafRowsDef.val.Evalb
        (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c) /\
      CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c := by
  rcases CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical
      Gamma candidate certificate with ⟨c, hcanonical⟩
  exact ⟨c,
    compactNumericVerifierPAAxiomJointLeafRowsDef_spec c |>.2 hcanonical.1,
    hcanonical⟩

#print axioms compactNumericVerifierPAAxiomJointLeafRowsDef_spec
#print axioms compactNumericVerifierPAAxiomJointLeafRowsDef_sigmaZero
#print axioms CompactNumericVerifierPAAxiomJointLeafRows.sound
#print axioms compactNumericVerifierPAAxiomJointLeafRowsDef_converse

end FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

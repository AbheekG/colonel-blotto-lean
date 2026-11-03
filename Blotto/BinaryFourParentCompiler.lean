import Blotto.BinaryFourParameters
import Blotto.BinaryThreeSpecCompiler
import Blotto.BinaryThreeSpecWork
import Blotto.RationalFourOverlapCompiler
import Blotto.RationalFourGluingHeight

/-! The gluing branch's two native three-variable parents and 81-slot overlap
descriptor are produced from the original six stored Boolean words. Parameter
table extraction, unordered parent ordering/swaps and overlap evaluation are
actual native code. Source admissibility and branch premise remain explicit;
the distinct small reflected/nested branch is not represented by this gluing
compiler. No parent descriptor refinement oracle is supplied. -/

namespace Blotto.BinaryFourParentCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

def firstInput (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : BinaryThreeInputCompiler.Input :=
  ⟨parameters.read 2,input.u,input.v,parameters.read 1,Constant.one.word⟩
def secondInput (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : BinaryThreeInputCompiler.Input :=
  ⟨parameters.read 3,parameters.read 1,input.w,input.ell,input.p⟩

theorem firstInput_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) :
    (firstInput input (BinaryFourParameters.prepare input)).Canonical :=
  ⟨BinaryFourParameters.prepare_canonical input h 2,h.2.1,h.2.2.1,
    BinaryFourParameters.prepare_canonical input h 1,Constant.word_canonical .one⟩
theorem secondInput_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) :
    (secondInput input (BinaryFourParameters.prepare input)).Canonical :=
  ⟨BinaryFourParameters.prepare_canonical input h 3,BinaryFourParameters.prepare_canonical input h 1,
    h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

theorem firstInput_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    BinaryThreeSpecCompiler.Refines (firstInput input (BinaryFourParameters.prepare input)) (source.gluingFirstSpec hcase) := by
  rw [source.gluingFirstSpec_refines]
  refine ⟨?_,hR.2.1,hR.2.2.1,?_,Constant.word_value .one⟩
  · exact BinaryFourParameters.prepare_value input source hC hR 2
  · exact BinaryFourParameters.prepare_value input source hC hR 1

theorem secondInput_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    BinaryThreeSpecCompiler.Refines (secondInput input (BinaryFourParameters.prepare input)) (source.gluingSecondSpec hcase) := by
  rw [source.gluingSecondSpec_refines]
  refine ⟨?_,?_,hR.2.2.2.1,hR.2.2.2.2.1,hR.2.2.2.2.2⟩
  · exact BinaryFourParameters.prepare_value input source hC hR 3
  · exact BinaryFourParameters.prepare_value input source hC hR 1

def firstParent (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 :=
  BinaryThreeSpecCompiler.descriptor (firstInput input parameters)
def secondParent (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 :=
  BinaryThreeSpecCompiler.descriptor (secondInput input parameters)

theorem firstParent_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    (firstParent input (BinaryFourParameters.prepare input)).Refines (source.overlapData hcase).first :=
  BinaryThreeSpecCompiler.descriptor_refines _ _ (firstInput_canonical input hC) (firstInput_refines input source hC hR hcase)
theorem secondParent_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    (secondParent input (BinaryFourParameters.prepare input)).Refines (source.overlapData hcase).second :=
  BinaryThreeSpecCompiler.descriptor_refines _ _ (secondInput_canonical input hC) (secondInput_refines input source hC hR hcase)

def descriptor (input : BinaryFourParameters.Input) : BinaryStoredOverlapEnvironment.Segment 4 81 :=
  let parameters := BinaryFourParameters.prepare input
  let first := firstParent input parameters
  let second := secondParent input parameters
  BinaryStoredOverlapEnvironment.compileDescriptor first second (parameters.read 1) input.B

theorem descriptor_canonical (input : BinaryFourParameters.Input) (h : input.Canonical) : (descriptor input).Canonical :=
  BinaryStoredOverlapEnvironment.compileDescriptor_canonical _ _ _ _
    (BinaryThreeSpecCompiler.descriptor_canonical _ (firstInput_canonical input h))
    (BinaryThreeSpecCompiler.descriptor_canonical _ (secondInput_canonical input h))
    (BinaryFourParameters.prepare_canonical input h 1) h.1

theorem descriptor_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    (descriptor input).Refines (source.compiledRationalGluingDescriptor hcase) := by
  exact BinaryStoredOverlapEnvironment.compileDescriptor_refines _ _ _ _ (source.overlapData hcase) source.B
    (BinaryThreeSpecCompiler.descriptor_canonical _ (firstInput_canonical input hC))
    (BinaryThreeSpecCompiler.descriptor_canonical _ (secondInput_canonical input hC))
    (BinaryFourParameters.prepare_canonical input hC 1) hC.1
    (firstParent_refines input source hC hR hcase) (secondParent_refines input source hC hR hcase)
    (BinaryFourParameters.prepare_value input source hC hR 1) hR.1

-- The branch test is executed on the original six words and exactly recognizes
-- the retained gluing case; false designates the separately uncompiled small case.
def gluingCase (input : BinaryFourParameters.Input) : Bool :=
  BinaryRationalArithmetic.lessEqual
    (BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .sub Constant.one.word input.p) input.ell) input.w

theorem gluingCase_iff (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) : gluingCase input = true ↔ (1-source.p)*source.ell ≤ source.w := by
  have hOne := (Constant.word_canonical .one).1
  have hp := BinaryRationalOpcode.apply_valid .sub Constant.one.word input.p hOne hC.2.2.2.2.2.1
  have hm := BinaryRationalOpcode.apply_valid .mul (BinaryRationalOpcode.apply .sub Constant.one.word input.p) input.ell hp hC.2.2.2.2.1.1
  have he := BinaryRationalArithmetic.lessEqual_iff
    (BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .sub Constant.one.word input.p) input.ell) input.w hm hC.2.2.2.1.1
  rw [BinaryRationalOpcode.apply_value .mul _ _ hp hC.2.2.2.2.1.1,
    BinaryRationalOpcode.apply_value .sub _ _ hOne hC.2.2.2.2.2.1,
    Constant.word_value,hR.2.2.2.2.2,hR.2.2.2.2.1,hR.2.2.2.1] at he
  exact he

def compile (input : BinaryFourParameters.Input) : Option (BinaryStoredOverlapEnvironment.Segment 4 81) :=
  if gluingCase input then some (descriptor input) else none

theorem compile_success (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w) :
    compile input = some (descriptor input) ∧ (descriptor input).Canonical ∧
      (descriptor input).Refines (source.gluingDescriptor hcase) := by
  refine ⟨?_,descriptor_canonical input hC,descriptor_refines input source hC hR hcase⟩
  unfold compile
  rw [ite_eq_left ((gluingCase_iff input source hC hR).mpr hcase)]

theorem compile_small_case (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : source.w < (1-source.p)*source.ell) : compile input = none := by
  unfold compile
  rw [ite_eq_right (fun h => not_le.mpr hcase ((gluingCase_iff input source hC hR).mp h))]

def descriptorWork (input : BinaryFourParameters.Input) : ℕ :=
  let parameters := BinaryFourParameters.prepare input
  let first := firstInput input parameters
  let second := secondInput input parameters
  BinaryFourParameters.prepareWork input + BinaryThreeSpecCompiler.descriptorWork first +
    BinaryThreeSpecCompiler.descriptorWork second +
    BinaryStoredOverlapEnvironment.compileDescriptorWork
      (BinaryThreeSpecCompiler.descriptor first) (BinaryThreeSpecCompiler.descriptor second) (parameters.read 1) input.B

def descriptorWithWork (input : BinaryFourParameters.Input) : BinaryStoredOverlapEnvironment.Segment 4 81 × ℕ :=
  (descriptor input,descriptorWork input)

def parentWorkBound (s : ℕ) : ℕ := BinaryThreeInputCompiler.workBound s + 1000*(2*s+2)^2 +
  108*(4*expressionHeightBudget s 4+3)+220

def workBound (s : ℕ) : ℕ :=
  12*(4*s+3)+2048*BinaryRationalExpression.uniformPrice (expressionHeightBudget s 12)+12344 +
    2*parentWorkBound (expressionHeightBudget s 12) +
    81*(9*(64+32*(4*expressionHeightBudget s 30+3))+
      BinaryOverlapInputPreparation.evaluationWorkBound (expressionHeightBudget s 30)+13094)+3

theorem descriptorWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hcase : (1-source.p)*source.ell ≤ source.w)
    (s : ℕ) (hs : 2 ≤ s) (hFields : source.FieldsHeight s) : descriptorWork input ≤ workBound s := by
  let parameters := BinaryFourParameters.prepare input
  let first := firstInput input parameters
  let second := secondInput input parameters
  have hFC := firstInput_canonical input hC
  have hSC := secondInput_canonical input hC
  have hFR := firstInput_refines input source hC hR hcase
  have hSR := secondInput_refines input source hC hR hcase
  have hs12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hf := BinaryThreeSpecCompiler.descriptorWork_bound first (source.gluingFirstSpec hcase)
    hFC hFR _ hs12 (hFields.gluingFirst_environment hs hcase)
  have hq := BinaryThreeSpecCompiler.descriptorWork_bound second (source.gluingSecondSpec hcase)
    hSC hSR _ hs12 (hFields.gluingSecond_environment hs hcase)
  have hp := BinaryFourParameters.prepareWork_bound input source hC hR s hs hFields.environment
  have hFHeight := RationalThreeSpecCode.descriptor_height (source.gluingFirstSpec hcase)
    (expressionHeightBudget s 12) hs12 (hFields.gluingFirst_environment hs hcase)
  have hSHeight := RationalThreeSpecCode.descriptor_height (source.gluingSecondSpec hcase)
    (expressionHeightBudget s 12) hs12 (hFields.gluingSecond_environment hs hcase)
  rw [expressionHeightBudget_comp] at hFHeight hSHeight
  norm_num only [show 12+18=(30 : ℕ) from rfl] at hFHeight hSHeight
  have hD : RationalHeight source.auxLength (expressionHeightBudget s 30) :=
    (hFields.scalar hs 1).mono (expressionHeightBudget_mono s (by decide : 12≤30))
  have hB := hFields.1.mono (expressionHeightBudget_ge_input s 30)
  have ho := BinaryStoredOverlapEnvironment.compileDescriptorWork_bound
    (BinaryThreeSpecCompiler.descriptor first) (BinaryThreeSpecCompiler.descriptor second)
    (parameters.read 1) input.B (source.overlapData hcase) source.B
    (BinaryThreeSpecCompiler.descriptor_canonical first hFC) (BinaryThreeSpecCompiler.descriptor_canonical second hSC)
    (BinaryFourParameters.prepare_canonical input hC 1) hC.1
    (firstParent_refines input source hC hR hcase) (secondParent_refines input source hC hR hcase)
    (BinaryFourParameters.prepare_value input source hC hR 1) hR.1
    (expressionHeightBudget s 30) (hs.trans (expressionHeightBudget_ge_input s 30)) hFHeight hSHeight hD hB
  unfold descriptorWork
  change BinaryFourParameters.prepareWork input + BinaryThreeSpecCompiler.descriptorWork first +
    BinaryThreeSpecCompiler.descriptorWork second +
      BinaryStoredOverlapEnvironment.compileDescriptorWork (BinaryThreeSpecCompiler.descriptor first)
        (BinaryThreeSpecCompiler.descriptor second) (parameters.read 1) input.B ≤ _
  unfold workBound parentWorkBound
  omega

end Blotto.BinaryFourParentCompiler

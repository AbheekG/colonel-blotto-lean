import Blotto.BinaryNestedFirstConditional
import Blotto.BinaryNestedResidualCompiler
import Blotto.BinaryThreeInputCompiler

/-! Actual stored-word family, translated-uniform and residual tables are the
components of the remaining ordered interior nested regimes. Source conditions
supply erased proof invariants, not runtime descriptor factories. -/

namespace Blotto.BinaryNestedComponents
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryNestedParameters

def familyInput (input : Input) (length : SignedWord) : Input :=
  ⟨input.M,input.a,input.d,input.c,length,(prepare input length).read 5⟩

theorem familyInput_canonical (input : Input) (length : SignedWord) (h : input.Canonical) (hl : CanonicalWord length) :
    (familyInput input length).Canonical :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,hl,prepare_canonical input length h hl 5⟩

theorem familyInput_refines (input : Input) (length : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hl : CanonicalWord length) (hr : input.Refines source)
    (x : ℚ) (hLength : value length = x) (hx : 0 < x) (hxv : x ≤ source.v) :
    (familyInput input length).Refines (source.familyInput x hx hxv) := by
  refine ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hLength,?_⟩
  have he := prepare_value input length source h hl hr 5
  change value ((prepare input length).read 5) = source.familyProbability (value length) at he
  rw [hLength] at he
  exact he

def familyLottery (input : Input) (length : SignedWord) (K : ℕ) (bits : Fin K → Bool) : Segment 3 9 :=
  BinaryNestedFirstConditional.firstProfile (familyInput input length) K bits

theorem familyLottery_canonical (input : Input) (length : SignedWord) (h : input.Canonical) (hl : CanonicalWord length)
    (K : ℕ) (bits : Fin K → Bool) : (familyLottery input length K bits).Canonical :=
  BinaryNestedFirstConditional.firstProfile_canonical _ (familyInput_canonical input length h hl) K bits

theorem familyLottery_refines (input : Input) (length : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hl : CanonicalWord length) (hr : input.Refines source)
    (x : ℚ) (hLength : value length = x) (hx : 0 < x) (hxv : x ≤ source.v) (K : ℕ) (bits : Fin K → Bool) :
    (familyLottery input length K bits).Refines (source.familyLottery x hx hxv K bits) :=
  BinaryNestedFirstConditional.firstProfile_refines _ _ (familyInput_canonical input length h hl)
    (familyInput_refines input length source h hl hr x hLength hx hxv) hxv K bits

def mirror (input : Input) : SignedWord := (prepare input BinaryRationalOpcode.zero).read 6

theorem mirror_canonical (input : Input) (h : input.Canonical) : CanonicalWord (mirror input) :=
  prepare_canonical input _ h ⟨BinaryRationalOpcode.zero_valid,by decide⟩ 6

theorem mirror_value (input : Input) (source : RationalNestedInput) (h : input.Canonical) (hr : input.Refines source) :
    value (mirror input) = source.mirrorLength :=
  prepare_value input _ source h ⟨BinaryRationalOpcode.zero_valid,by decide⟩ hr 6

def secondUniformInput (input : Input) : BinaryThreeInputCompiler.Input :=
  ⟨BinaryRationalOpcode.apply .sub input.M (mirror input),input.a,input.d,
    BinaryRationalOpcode.apply .sub input.t (mirror input),BinaryExpressionCompiler.Constant.one.word⟩

theorem secondUniformInput_canonical (input : Input) (h : input.Canonical) : (secondUniformInput input).Canonical :=
  ⟨BinaryReflectedFourSetup.opcode_canonical .sub _ _ h.1 (mirror_canonical input h),h.2.1,h.2.2.1,
    BinaryReflectedFourSetup.opcode_canonical .sub _ _ h.2.2.2.2.1 (mirror_canonical input h),
    BinaryExpressionCompiler.Constant.word_canonical .one⟩

theorem secondUniformInput_refines (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (htu : source.u ≤ source.t) (hTt : source.mirrorLength < source.t) :
    (secondUniformInput input).Refines (source.secondUniformInput htu hTt) := by
  refine ⟨?_,hr.2.1,hr.2.2.1,?_,?_⟩
  · change value (BinaryRationalOpcode.apply .sub input.M (mirror input)) = source.M - source.mirrorLength
    rw [BinaryRationalOpcode.apply_value .sub _ _ h.1.1 (mirror_canonical input h).1,hr.1,mirror_value input source h hr]
    rfl
  · change value (BinaryRationalOpcode.apply .sub input.t (mirror input)) = source.t - source.mirrorLength
    rw [BinaryRationalOpcode.apply_value .sub _ _ h.2.2.2.2.1.1 (mirror_canonical input h).1,hr.2.2.2.2.1,mirror_value input source h hr]
    rfl
  · exact BinaryExpressionCompiler.Constant.word_value .one

def secondUniformLottery (input : Input) : Segment 3 9 :=
  BinarySegmentAssembly.shiftThird (BinaryThreeInputCompiler.descriptor (secondUniformInput input)) (mirror input)

theorem secondUniformLottery_canonical (input : Input) (h : input.Canonical) : (secondUniformLottery input).Canonical :=
  BinarySegmentAssembly.shiftThird_canonical _ _
    (BinaryThreeInputCompiler.descriptor_canonical _ (secondUniformInput_canonical input h)) (mirror_canonical input h)

theorem secondUniformLottery_refines (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (htu : source.u ≤ source.t) (hTt : source.mirrorLength < source.t) :
    (secondUniformLottery input).Refines (source.secondUniformLottery htu hTt) := by
  have he := BinaryThreeInputCompiler.descriptor_refines _ _ (secondUniformInput_canonical input h)
    (secondUniformInput_refines input source h hr htu hTt)
  have hs := BinarySegmentAssembly.shiftThird_refines _ (mirror input) _
    (BinaryThreeInputCompiler.descriptor_canonical _ (secondUniformInput_canonical input h)) (mirror_canonical input h) he
  simpa only [mirror_value input source h hr,secondUniformLottery,RationalNestedInput.secondUniformLottery] using hs

def residualEnvironment (input : Input) : FixedArrayTable 5 SignedWord :=
  let p := prepare input BinaryRationalOpcode.zero
  FixedArrayTable.ofFn ![p.read 1,p.read 2,BinaryRationalOpcode.apply .sub input.M input.c,p.read 0,input.t]

theorem residualEnvironment_canonical (input : Input) (h : input.Canonical) :
    ∀ j, CanonicalWord ((residualEnvironment input).read j) := by
  have hp := prepare_canonical input BinaryRationalOpcode.zero h ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  intro j
  simp only [residualEnvironment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact hp 1
  · exact hp 2
  · exact BinaryReflectedFourSetup.opcode_canonical .sub _ _ h.1 h.2.2.2.1
  · exact hp 0
  · exact h.2.2.2.2.1

theorem residualEnvironment_refines (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (hvt : source.v < source.t) (htu : source.t < source.u) :
    BinaryRationalExpression.interpretedEnvironment (residualEnvironment input) =
      RationalNestedResidualCode.environment (source.residualInput hvt htu) := by
  have hp := prepare_value input BinaryRationalOpcode.zero source h ⟨BinaryRationalOpcode.zero_valid,by decide⟩ hr
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [BinaryRationalExpression.interpretedEnvironment,residualEnvironment,FixedArrayTable.read_ofFn,
    RationalNestedResidualCode.environment,RationalNestedInput.residualInput]
  fin_cases j
  · exact hp 1
  · exact hp 2
  · change value (BinaryRationalOpcode.apply .sub input.M input.c) = source.M - source.c
    rw [BinaryRationalOpcode.apply_value .sub _ _ h.1.1 h.2.2.2.1.1,hr.1,hr.2.2.2.1]
    rfl
  · exact hp 0
  · exact hr.2.2.2.2.1

def residualLottery (input : Input) : Segment 3 3 := BinaryNestedResidualCompiler.descriptor (residualEnvironment input)

theorem residualLottery_canonical (input : Input) (h : input.Canonical) : (residualLottery input).Canonical :=
  BinaryNestedResidualCompiler.descriptor_canonical _ (residualEnvironment_canonical input h)

theorem residualLottery_refines (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (hvt : source.v < source.t) (htu : source.t < source.u) :
    (residualLottery input).Refines (source.residualInput hvt htu).segmentLottery :=
  BinaryNestedResidualCompiler.descriptor_refines _ _ (fun j => (residualEnvironment_canonical input h j).1)
    (residualEnvironment_refines input source h hr hvt htu)

end Blotto.BinaryNestedComponents

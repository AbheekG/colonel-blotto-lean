import Blotto.BinaryStoredSegmentProgram
import Blotto.BinaryFourSpecSampler
import Blotto.BinaryThreeSpecCompiler
import Blotto.RationalGroupPrograms

/-! Stored group budgets, cached totals and fractional words construct the
actual two/three-group uniform and mixed continuations. Small source promises
are erased certificates; no semantic descriptor is encoded at runtime. -/

namespace Blotto.BinaryGroupInputs
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment

structure UniformInput (m : ℕ) where
  budget : SignedWord
  total : FixedArrayTable m SignedWord

def UniformInput.Canonical {m : ℕ} (input : UniformInput m) : Prop := CanonicalWord input.budget ∧ ∀ g, CanonicalWord (input.total.read g)
def UniformInput.Refines {m : ℕ} (input : UniformInput m) (source : RationalUniformGroupSpec m) : Prop :=
  value input.budget=source.B ∧ ∀ g, value (input.total.read g)=source.length g

def pair (input : UniformInput 2) : Segment 2 1 where
  weight := FixedArrayTable.ofFn (fun _ => BinaryExpressionCompiler.Constant.one.word)
  P := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![BinaryRationalOpcode.zero,input.budget])
  Q := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![input.budget,BinaryRationalOpcode.zero])

theorem pair_canonical (input : UniformInput 2) (hC : input.Canonical) : (pair input).Canonical := by
  have hz : CanonicalWord BinaryRationalOpcode.zero := ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  refine ⟨?_,?_,?_⟩
  · intro slot; rw [pair,FixedArrayTable.read_ofFn]; exact BinaryExpressionCompiler.Constant.word_canonical .one
  · intro slot j; simp only [pair,FixedArrayTable.read_ofFn]; fin_cases j
    · exact hz
    · exact hC.1
  · intro slot j; simp only [pair,FixedArrayTable.read_ofFn]; fin_cases j
    · exact hC.1
    · exact hz

theorem pair_refines (input : UniformInput 2) (source : RationalUniformGroupSpec 2) (hr : input.Refines source) :
    (pair input).Refines (rationalComplementaryPair source.B) := by
  refine ⟨?_,?_,?_⟩
  · intro slot; simp only [pair,FixedArrayTable.read_ofFn,rationalComplementaryPair]; exact BinaryExpressionCompiler.Constant.word_value .one
  · intro slot j; simp only [pair,FixedArrayTable.read_ofFn,rationalComplementaryPair]; fin_cases j
    · exact BinaryRationalOpcode.zero_value
    · exact hr.1
  · intro slot j; simp only [pair,FixedArrayTable.read_ofFn,rationalComplementaryPair]; fin_cases j
    · exact hr.1
    · exact BinaryRationalOpcode.zero_value

def uniformThree (input : UniformInput 3) : BinaryThreeInputCompiler.Input :=
  ⟨input.budget,input.total.read 0,input.total.read 1,input.total.read 2,BinaryExpressionCompiler.Constant.one.word⟩

theorem uniformThree_canonical (input : UniformInput 3) (hC : input.Canonical) : (uniformThree input).Canonical :=
  ⟨hC.1,hC.2 0,hC.2 1,hC.2 2,BinaryExpressionCompiler.Constant.word_canonical .one⟩

theorem uniformThree_refines (input : UniformInput 3) (source : RationalUniformGroupSpec 3) (hr : input.Refines source) :
    BinaryThreeSpecCompiler.Refines (uniformThree input) source.threeInput :=
  ⟨hr.1,hr.2 0,hr.2 1,hr.2 2,BinaryExpressionCompiler.Constant.word_value .one⟩

def uniformLottery {m : ℕ} (input : UniformInput m) (hm : m=2 ∨ m=3) : Segment m 9 := by
  by_cases h2 : m=2
  · subst m
    exact BinarySegmentAssembly.padRight (pair input) 8 0
  · have h3 : m=3 := hm.resolve_left h2
    subst m
    exact BinaryThreeSpecCompiler.descriptor (uniformThree input)

theorem uniformLottery_canonical {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m=2 ∨ m=3) :
    (uniformLottery input hm).Canonical := by
  rcases hm with rfl | rfl
  · exact BinarySegmentAssembly.padRight_canonical _ 8 0 (pair_canonical input hC)
  · exact BinaryThreeSpecCompiler.descriptor_canonical _ (uniformThree_canonical input hC)

theorem uniformLottery_refines {m : ℕ} (input : UniformInput m) (source : RationalUniformGroupSpec m)
    (hC : input.Canonical) (hr : input.Refines source) (hm : m=2 ∨ m=3) :
    (uniformLottery input hm).Refines (source.lottery hm) := by
  rcases hm with rfl | rfl
  · exact BinarySegmentAssembly.padRight_refines _ _ (pair_refines input source hr) 8 0
  · exact BinaryThreeSpecCompiler.descriptor_refines _ _ (uniformThree_canonical input hC) (uniformThree_refines input source hr)

structure MixedInput (m : ℕ) where
  budget : SignedWord
  total : FixedArrayTable m SignedWord
  ell : SignedWord
  probability : SignedWord

def MixedInput.Canonical {m : ℕ} (input : MixedInput m) : Prop := CanonicalWord input.budget ∧
  (∀ g, CanonicalWord (input.total.read g)) ∧ CanonicalWord input.ell ∧ CanonicalWord input.probability

def MixedInput.Refines {m : ℕ} (input : MixedInput m) (source : RationalMixedGroupSpec m) : Prop :=
  value input.budget=source.B ∧ (∀ g, value (input.total.read g)=source.length g) ∧ value input.ell=source.ell ∧ value input.probability=source.p

def mixedThree (input : MixedInput 2) : BinaryThreeInputCompiler.Input :=
  ⟨input.budget,input.total.read 0,input.total.read 1,input.ell,input.probability⟩

theorem mixedThree_canonical (input : MixedInput 2) (hC : input.Canonical) : (mixedThree input).Canonical :=
  ⟨hC.1,hC.2.1 0,hC.2.1 1,hC.2.2.1,hC.2.2.2⟩

theorem mixedThree_refines (input : MixedInput 2) (source : RationalMixedGroupSpec 2) (hr : input.Refines source) :
    BinaryThreeSpecCompiler.Refines (mixedThree input) source.threeInput := ⟨hr.1,hr.2.1 0,hr.2.1 1,hr.2.2.1,hr.2.2.2⟩

def mixedFour (input : MixedInput 3) : BinaryFourSpecSampler.Input := ⟨input.budget,input.total,input.ell,input.probability⟩

theorem mixedFour_canonical (input : MixedInput 3) (hC : input.Canonical) : (mixedFour input).Canonical := hC

theorem mixedFour_refines (input : MixedInput 3) (source : RationalMixedGroupSpec 3) (hr : input.Refines source) :
    (mixedFour input).Refines source.fourInput := hr

end Blotto.BinaryGroupInputs

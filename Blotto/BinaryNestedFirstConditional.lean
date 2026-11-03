import Blotto.BinaryNestedParameters
import Blotto.BinaryThreeDescriptorCompiler
import Blotto.BinaryDyadicMidpoint

/-! Actual stored-word first-case conditional descriptors retain the positive
geometry and zero-probability corner of the original nested algorithm. The
outer midpoint is constructed directly from its Boolean bits. -/

namespace Blotto.BinaryNestedFirstConditional
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryNestedParameters

def corner (input : Input) (x : SignedWord) : Segment 3 9 where
  weight := FixedArrayTable.ofFn (fun slot => if slot = 0 then BinaryExpressionCompiler.Constant.one.word else BinaryRationalOpcode.zero)
  P := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![BinaryRationalOpcode.zero,input.d,x])
  Q := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![input.a,BinaryRationalOpcode.zero,x])

theorem corner_canonical (input : Input) (x : SignedWord) (h : input.Canonical) (hx : CanonicalWord x) :
    (corner input x).Canonical := by
  have h0 : CanonicalWord BinaryRationalOpcode.zero := ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [corner,FixedArrayTable.read_ofFn]
    split_ifs
    · exact BinaryExpressionCompiler.Constant.word_canonical .one
    · exact h0
  · intro slot field
    simp only [corner,FixedArrayTable.read_ofFn]
    fin_cases field
    · exact h0
    · exact h.2.2.1
    · exact hx
  · intro slot field
    simp only [corner,FixedArrayTable.read_ofFn]
    fin_cases field
    · exact h.2.1
    · exact h0
    · exact hx

def descriptor (input : Input) (x : SignedWord) : Segment 3 9 :=
  if !BinaryRationalArithmetic.lessEqual ((prepare input x).read 4) BinaryRationalOpcode.zero then
    BinarySegmentAssembly.shiftThird (BinaryThreeDescriptorCompiler.descriptor (geometry input x)) x
  else corner input x

theorem descriptor_canonical (input : Input) (x : SignedWord) (h : input.Canonical) (hx : CanonicalWord x) :
    (descriptor input x).Canonical := by
  unfold descriptor
  split
  · exact BinarySegmentAssembly.shiftThird_canonical _ x
      (BinaryThreeDescriptorCompiler.descriptor_canonical _ (geometry_canonical input x h hx)) hx
  · exact corner_canonical input x h hx

theorem positive_iff (input : Input) (x : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hx : CanonicalWord x) (hr : input.Refines source) :
    (!BinaryRationalArithmetic.lessEqual ((prepare input x).read 4) BinaryRationalOpcode.zero) = true ↔
      0 < source.conditionalProbability (value x) := by
  have he := BinaryRationalArithmetic.lessEqual_iff ((prepare input x).read 4) BinaryRationalOpcode.zero
    (prepare_canonical input x h hx 4).1 BinaryRationalOpcode.zero_valid
  rw [prepare_value input x source h hx hr 4,BinaryRationalOpcode.zero_value] at he
  have hValue : values source (value x) 4 = source.conditionalProbability (value x) := rfl
  rw [hValue] at he
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  exact (not_congr he).trans not_le

theorem descriptor_refines (input : Input) (x : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hx : CanonicalWord x) (hr : input.Refines source) (htv : source.t ≤ source.v)
    (hs : 0 ≤ value x ∧ value x ≤ source.t) :
    (descriptor input x).Refines (source.firstConditionalLottery htv (value x) hs) := by
  have he := positive_iff input x source h hx hr
  unfold descriptor RationalNestedInput.firstConditionalLottery
  by_cases hp : 0 < source.conditionalProbability (value x)
  · rw [ite_eq_left (he.mpr hp),dite_eq_left hp]
    have hc := BinaryThreeDescriptorCompiler.descriptor_canonical (geometry input x) (geometry_canonical input x h hx)
    have hg := BinaryThreeDescriptorCompiler.descriptor_refines (geometry input x) (source.firstGeometry htv (value x) hs hp)
      (fun j => (geometry_canonical input x h hx j).1) (geometry_refines input x source h hx hr htv hs hp)
    rw [RationalThreeGeometryCode.compiledLottery_eq] at hg
    exact BinarySegmentAssembly.shiftThird_refines _ x _ hc hx hg
  · rw [ite_eq_right (fun h' => hp (he.mp h')),dite_eq_right hp]
    refine ⟨?_,?_,?_⟩
    · intro slot
      simp only [corner,FixedArrayTable.read_ofFn]
      split_ifs
      · exact BinaryExpressionCompiler.Constant.word_value .one
      · exact BinaryRationalOpcode.zero_value
    · intro slot field
      simp only [corner,FixedArrayTable.read_ofFn]
      fin_cases field
      · exact BinaryRationalOpcode.zero_value
      · exact hr.2.2.1
      · rfl
    · intro slot field
      simp only [corner,FixedArrayTable.read_ofFn]
      fin_cases field
      · exact hr.2.1
      · exact BinaryRationalOpcode.zero_value
      · rfl

def midpointLocation (input : Input) (K : ℕ) (bits : Fin K → Bool) : SignedWord :=
  (prepare input (BinaryDyadicMidpoint.sample K bits)).read 3

theorem midpointLocation_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    CanonicalWord (midpointLocation input K bits) :=
  prepare_canonical input _ h (BinaryDyadicMidpoint.sample_canonical K bits) 3

theorem midpointLocation_value (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (K : ℕ) (bits : Fin K → Bool) :
    value (midpointLocation input K bits) = source.midpointLocation K bits := by
  have he := prepare_value input (BinaryDyadicMidpoint.sample K bits) source h (BinaryDyadicMidpoint.sample_canonical K bits) hr 3
  change value (midpointLocation input K bits) = source.location (value (BinaryDyadicMidpoint.sample K bits)) at he
  rw [BinaryDyadicMidpoint.sample_value] at he
  exact he

def firstProfile (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 9 :=
  descriptor input (midpointLocation input K bits)

theorem firstProfile_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) :
    (firstProfile input K bits).Canonical :=
  descriptor_canonical input _ h (midpointLocation_canonical input h K bits)

theorem firstProfile_refines (input : Input) (source : RationalNestedInput)
    (h : input.Canonical) (hr : input.Refines source) (htv : source.t ≤ source.v) (K : ℕ) (bits : Fin K → Bool) :
    (firstProfile input K bits).Refines
      (source.firstConditionalLottery htv (source.midpointLocation K bits) (source.midpointLocation_bounds K bits)) := by
  have hx := midpointLocation_value input source h hr K bits
  have hs : 0 ≤ value (midpointLocation input K bits) ∧ value (midpointLocation input K bits) ≤ source.t := by
    rw [hx]
    exact source.midpointLocation_bounds K bits
  have he := descriptor_refines input _ source h (midpointLocation_canonical input h K bits) hr htv hs
  simpa only [hx,firstProfile] using he

end Blotto.BinaryNestedFirstConditional

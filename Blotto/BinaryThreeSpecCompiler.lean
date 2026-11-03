import Blotto.BinaryThreeInputCompiler
import Blotto.RationalThreeSpec

/-! Unordered three-variable Boolean words are ordered by the verified native
comparison, compiled by the actual ordered producer, then restored by a stored
coordinate swap. The original zero/regular regime branches are retained. -/

namespace Blotto.BinaryThreeSpecCompiler
open BinaryRationalNormalization BinaryRationalEncoding

def ordered (input : BinaryThreeInputCompiler.Input) : BinaryThreeInputCompiler.Input :=
  if BinaryRationalArithmetic.lessEqual input.a input.d then input else
    ⟨input.B,input.d,input.a,input.c,input.p⟩

theorem ordered_canonical (input : BinaryThreeInputCompiler.Input) (h : input.Canonical) :
    (ordered input).Canonical := by
  unfold ordered
  split
  · exact h
  · exact ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

def Refines (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec) : Prop :=
  value input.B = source.B ∧ value input.a = source.a ∧ value input.d = source.d ∧
    value input.c = source.c ∧ value input.p = source.p

theorem comparison (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : Refines input source) :
    BinaryRationalArithmetic.lessEqual input.a input.d = true ↔ source.a ≤ source.d := by
  have he := BinaryRationalArithmetic.lessEqual_iff input.a input.d hC.2.1.1 hC.2.2.1.1
  rw [hR.2.1,hR.2.2.1] at he
  exact he

theorem ordered_refines (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : Refines input source) : (ordered input).Refines source.orderedInput := by
  have hc := comparison input source hC hR
  unfold ordered
  split
  · rename_i h
    have ho := hc.mp h
    exact ⟨hR.1,by simpa only [RationalThreeSpec.orderedInput,min_eq_left ho] using hR.2.1,
      by simpa only [RationalThreeSpec.orderedInput,max_eq_right ho] using hR.2.2.1,hR.2.2.2.1,hR.2.2.2.2⟩
  · rename_i h
    have ho : source.d ≤ source.a := le_of_not_ge (fun he => h (hc.mpr he))
    exact ⟨hR.1,by simpa only [RationalThreeSpec.orderedInput,min_eq_right ho] using hR.2.2.1,
      by simpa only [RationalThreeSpec.orderedInput,max_eq_left ho] using hR.2.1,hR.2.2.2.1,hR.2.2.2.2⟩

def swap (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : BinaryStoredOverlapEnvironment.Segment 3 9 where
  weight := segment.weight
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(segment.P.read slot).read 1,
    (segment.P.read slot).read 0,(segment.P.read slot).read 2])
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(segment.Q.read slot).read 1,
    (segment.Q.read slot).read 0,(segment.Q.read slot).read 2])

theorem swap_canonical (segment : BinaryStoredOverlapEnvironment.Segment 3 9) (h : segment.Canonical) :
    (swap segment).Canonical := by
  refine ⟨h.1,?_,?_⟩
  · intro slot j
    rw [swap,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    fin_cases j <;> exact h.2.1 _ _
  · intro slot j
    rw [swap,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    fin_cases j <;> exact h.2.2 _ _

def descriptor (input : BinaryThreeInputCompiler.Input) : BinaryStoredOverlapEnvironment.Segment 3 9 :=
  let result := BinaryThreeInputCompiler.descriptor (ordered input)
  if BinaryRationalArithmetic.lessEqual input.a input.d then result else swap result

theorem descriptor_canonical (input : BinaryThreeInputCompiler.Input) (h : input.Canonical) :
    (descriptor input).Canonical := by
  have hc := BinaryThreeInputCompiler.descriptor_canonical (ordered input) (ordered_canonical input h)
  unfold descriptor
  split
  · exact hc
  · exact swap_canonical _ hc

theorem descriptor_refines (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : Refines input source) :
    (descriptor input).Refines source.segmentLottery := by
  have hc := comparison input source hC hR
  have he := BinaryThreeInputCompiler.descriptor_refines (ordered input) source.orderedInput
    (ordered_canonical input hC) (ordered_refines input source hC hR)
  unfold descriptor RationalThreeSpec.segmentLottery
  dsimp only
  by_cases ho : source.a ≤ source.d
  · rw [ite_eq_left (hc.mpr ho),ite_eq_left ho]
    exact he
  · rw [ite_eq_right (fun h => ho (hc.mp h)),ite_eq_right ho]
    constructor
    · exact he.1
    · constructor
      · intro slot j
        unfold swap
        rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
        fin_cases j <;> exact he.2.1 _ _
      · intro slot j
        unfold swap
        rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
        fin_cases j <;> exact he.2.2 _ _

end Blotto.BinaryThreeSpecCompiler

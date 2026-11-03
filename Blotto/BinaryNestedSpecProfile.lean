import Blotto.BinaryNestedProfileCompiler
import Blotto.BinaryNestedTerminalInput
import Blotto.BinaryThreeSpecCompiler

/-! Stored Boolean nested-spec profiles cover q=0, q=1, interior mixtures and
both coordinate orders. Their exact 18-slot table is the original source
profile; this is the terminal table constructor, before categorical execution. -/

namespace Blotto.BinaryNestedSpecProfile
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment
open BinaryNestedParameters BinaryNestedTerminalInput

def swap {k : ℕ} (table : Segment 3 k) : Segment 3 k where
  weight := table.weight
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(table.P.read slot).read 1,(table.P.read slot).read 0,(table.P.read slot).read 2])
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(table.Q.read slot).read 1,(table.Q.read slot).read 0,(table.Q.read slot).read 2])

theorem swap_canonical {k : ℕ} (table : Segment 3 k) (h : table.Canonical) : (swap table).Canonical := by
  refine ⟨h.1,?_,?_⟩
  · intro slot field
    simp only [swap,FixedArrayTable.read_ofFn]
    fin_cases field <;> exact h.2.1 _ _
  · intro slot field
    simp only [swap,FixedArrayTable.read_ofFn]
    fin_cases field <;> exact h.2.2 _ _

theorem swap_refines {k : ℕ} (table : Segment 3 k) (source : RationalSegmentLottery 3 k) (h : table.Refines source) :
    (swap table).Refines source.swapFirst := by
  refine ⟨h.1,?_,?_⟩
  · intro slot field
    simp only [swap,FixedArrayTable.read_ofFn,RationalSegmentLottery.swapFirst]
    fin_cases field <;> exact h.2.1 _ _
  · intro slot field
    simp only [swap,FixedArrayTable.read_ofFn,RationalSegmentLottery.swapFirst]
    fin_cases field <;> exact h.2.2 _ _

def longInput (input : Input) : BinaryThreeInputCompiler.Input :=
  ⟨input.M,input.a,input.d,input.c,BinaryExpressionCompiler.Constant.one.word⟩
def shortInput (input : Input) : BinaryThreeInputCompiler.Input :=
  ⟨input.M,input.a,input.d,input.t,BinaryExpressionCompiler.Constant.one.word⟩

theorem longInput_canonical (input : Input) (h : input.Canonical) : (longInput input).Canonical :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,BinaryExpressionCompiler.Constant.word_canonical .one⟩
theorem shortInput_canonical (input : Input) (h : input.Canonical) : (shortInput input).Canonical :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,BinaryExpressionCompiler.Constant.word_canonical .one⟩

theorem longInput_refines (input : Input) (source : RationalNestedSpec) (hr : InputRefinesSpec input source) (hq : source.q=0) :
    BinaryThreeSpecCompiler.Refines (longInput input) (source.longInput hq) :=
  ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,BinaryExpressionCompiler.Constant.word_value .one⟩
theorem shortInput_refines (input : Input) (source : RationalNestedSpec) (hr : InputRefinesSpec input source) (hq : source.q=1) :
    BinaryThreeSpecCompiler.Refines (shortInput input) (source.shortInput hq) :=
  ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.2.1,BinaryExpressionCompiler.Constant.word_value .one⟩

def qZero (input : Input) : Bool := BinaryRationalArithmetic.lessEqual input.q BinaryRationalOpcode.zero
def qOne (input : Input) : Bool := BinaryRationalArithmetic.lessEqual BinaryExpressionCompiler.Constant.one.word input.q

theorem qZero_iff (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source) :
    qZero input = true ↔ source.q = 0 := by
  rw [qZero,BinaryRationalArithmetic.lessEqual_iff _ _ h.2.2.2.2.2.1 BinaryRationalOpcode.zero_valid,hr.2.2.2.2.2,BinaryRationalOpcode.zero_value]
  exact ⟨fun he => le_antisymm he source.q_nonneg,fun he => he.le⟩

theorem qOne_iff (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source) :
    qOne input = true ↔ source.q = 1 := by
  rw [qOne,BinaryRationalArithmetic.lessEqual_iff _ _ (BinaryExpressionCompiler.Constant.word_canonical .one).1 h.2.2.2.2.2.1,
    BinaryExpressionCompiler.Constant.word_value,hr.2.2.2.2.2]
  exact ⟨fun he => le_antisymm source.q_le he,fun he => he.symm.le⟩

def profile (input : Input) (K : ℕ) (bits : Fin K → Bool) : Segment 3 18 :=
  if qZero input then BinarySegmentAssembly.padRight (BinaryThreeSpecCompiler.descriptor (longInput input)) 9 0
  else if qOne input then BinarySegmentAssembly.padRight (BinaryThreeSpecCompiler.descriptor (shortInput input)) 9 0
  else
    let table := BinaryNestedProfileCompiler.profile (sortedInput input) K bits
    if ordered input then table else swap table

theorem profile_canonical (input : Input) (h : input.Canonical) (K : ℕ) (bits : Fin K → Bool) : (profile input K bits).Canonical := by
  have hInterior := BinaryNestedProfileCompiler.profile_canonical (sortedInput input) (sortedInput_canonical input h) K bits
  unfold profile
  split
  · exact BinarySegmentAssembly.padRight_canonical _ 9 0 (BinaryThreeSpecCompiler.descriptor_canonical _ (longInput_canonical input h))
  · split
    · exact BinarySegmentAssembly.padRight_canonical _ 9 0 (BinaryThreeSpecCompiler.descriptor_canonical _ (shortInput_canonical input h))
    · split
      · exact hInterior
      · exact swap_canonical _ hInterior

theorem profile_refines (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) (bits : Fin K → Bool) : (profile input K bits).Refines (source.profile K bits) := by
  have hZero := qZero_iff input source h hr
  have hOne := qOne_iff input source h hr
  have hOrder := ordered_iff input source h hr
  unfold profile RationalNestedSpec.profile
  by_cases hq0 : source.q=0
  · rw [ite_eq_left (hZero.mpr hq0),dite_eq_left hq0]
    exact BinarySegmentAssembly.padRight_refines _ _
      (BinaryThreeSpecCompiler.descriptor_refines _ _ (longInput_canonical input h) (longInput_refines input source hr hq0)) 9 0
  · rw [ite_eq_right (fun hg => hq0 (hZero.mp hg)),dite_eq_right hq0]
    by_cases hq1 : source.q=1
    · rw [ite_eq_left (hOne.mpr hq1),dite_eq_left hq1]
      exact BinarySegmentAssembly.padRight_refines _ _
        (BinaryThreeSpecCompiler.descriptor_refines _ _ (shortInput_canonical input h) (shortInput_refines input source hr hq1)) 9 0
    · rw [ite_eq_right (fun hg => hq1 (hOne.mp hg)),dite_eq_right hq1]
      dsimp only
      have he := BinaryNestedProfileCompiler.profile_refines _ _ (sortedInput_canonical input h)
        (sortedInput_refines input source h hr (lt_of_le_of_ne source.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne source.q_le hq1)) K bits
      by_cases had : source.a ≤ source.d
      · rw [ite_eq_left (hOrder.mpr had),ite_eq_left had]
        exact he
      · rw [ite_eq_right (fun hg => had (hOrder.mp hg)),ite_eq_right had]
        exact swap_refines _ _ he

end Blotto.BinaryNestedSpecProfile

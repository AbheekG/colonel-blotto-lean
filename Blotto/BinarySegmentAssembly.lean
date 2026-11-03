import Blotto.BinaryReflectedFourSetup
import Blotto.RationalLotteryAssembly
import Blotto.RationalLotterySwap

/-! Stored Boolean segment tables assemble the exact nested descriptors by
padding, binary mixtures, translation and coordinate swaps. Padding retains
feasible endpoints; arithmetic uses the verified stored-word opcodes. -/

namespace Blotto.BinarySegmentAssembly
open BinaryRationalNormalization BinaryStoredOverlapEnvironment

abbrev Segment := BinaryStoredOverlapEnvironment.Segment

def padRight {n k : ℕ} (table : Segment n k) (m : ℕ) (fallback : Fin k) : Segment n (k + m) where
  weight := FixedArrayTable.ofFn (Fin.addCases table.weight.read (fun _ => BinaryRationalOpcode.zero))
  P := FixedArrayTable.ofFn (Fin.addCases table.P.read (fun _ => table.P.read fallback))
  Q := FixedArrayTable.ofFn (Fin.addCases table.Q.read (fun _ => table.Q.read fallback))

theorem padRight_canonical {n k : ℕ} (table : Segment n k) (m : ℕ) (fallback : Fin k) (h : table.Canonical) :
    (padRight table m fallback).Canonical := by
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [padRight,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.1 j
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using (show BinaryRationalEncoding.CanonicalWord BinaryRationalOpcode.zero from ⟨BinaryRationalOpcode.zero_valid,by decide⟩)
  · intro slot field
    simp only [padRight,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.1 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.1 fallback field
  · intro slot field
    simp only [padRight,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.2 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.2 fallback field

theorem padRight_refines {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (h : table.Refines source) (m : ℕ) (fallback : Fin k) :
    (padRight table m fallback).Refines (source.padRight m fallback) := by
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [padRight,FixedArrayTable.read_ofFn,RationalSegmentLottery.padRight]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.1 j
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using BinaryRationalOpcode.zero_value
  · intro slot field
    simp only [padRight,FixedArrayTable.read_ofFn,RationalSegmentLottery.padRight]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.1 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.1 fallback field
  · intro slot field
    simp only [padRight,FixedArrayTable.read_ofFn,RationalSegmentLottery.padRight]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.2 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using h.2.2 fallback field

def binary {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m) : Segment n (k + m) where
  weight := FixedArrayTable.ofFn (Fin.addCases (fun j => BinaryRationalOpcode.apply .mul p (first.weight.read j))
    (fun j => BinaryRationalOpcode.apply .mul (BinaryRationalOpcode.apply .sub BinaryExpressionCompiler.Constant.one.word p) (second.weight.read j)))
  P := FixedArrayTable.ofFn (Fin.addCases first.P.read second.P.read)
  Q := FixedArrayTable.ofFn (Fin.addCases first.Q.read second.Q.read)

theorem binary_canonical {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m)
    (hp : BinaryRationalEncoding.CanonicalWord p) (hFirst : first.Canonical) (hSecond : second.Canonical) :
    (binary p first second).Canonical := by
  have hComplement := BinaryReflectedFourSetup.opcode_canonical .sub BinaryExpressionCompiler.Constant.one.word p
    (BinaryExpressionCompiler.Constant.word_canonical .one) hp
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [binary,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using BinaryReflectedFourSetup.opcode_canonical .mul p _ hp (hFirst.1 j)
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using BinaryReflectedFourSetup.opcode_canonical .mul _ _ hComplement (hSecond.1 j)
  · intro slot field
    simp only [binary,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hFirst.2.1 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hSecond.2.1 j field
  · intro slot field
    simp only [binary,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hFirst.2.2 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hSecond.2.2 j field

theorem binary_refines {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m)
    (hp : BinaryRationalEncoding.CanonicalWord p) (hFirst : first.Canonical) (hSecond : second.Canonical)
    (sourceFirst : RationalSegmentLottery n k) (sourceSecond : RationalSegmentLottery n m)
    (hrFirst : first.Refines sourceFirst) (hrSecond : second.Refines sourceSecond) (prob : ℚ)
    (hrp : value p = prob) (hUnit : 0 ≤ prob ∧ prob ≤ 1) :
    (binary p first second).Refines (RationalSegmentLottery.binary prob hUnit sourceFirst sourceSecond) := by
  have hComplement := BinaryRationalOpcode.apply_valid .sub BinaryExpressionCompiler.Constant.one.word p (BinaryExpressionCompiler.Constant.word_canonical .one).1 hp.1
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [binary,FixedArrayTable.read_ofFn,RationalSegmentLottery.binary]
    refine Fin.addCases ?_ ?_ slot
    · intro j
      simp only [Fin.addCases_left]
      rw [BinaryRationalOpcode.apply_value .mul _ _ hp.1 (hFirst.1 j).1,hrp,hrFirst.1 j]
      rfl
    · intro j
      simp only [Fin.addCases_right]
      rw [BinaryRationalOpcode.apply_value .mul _ _ hComplement (hSecond.1 j).1,
        BinaryRationalOpcode.apply_value .sub _ _ (BinaryExpressionCompiler.Constant.word_canonical .one).1 hp.1,
        (BinaryExpressionCompiler.Constant.word_value .one),hrp,hrSecond.1 j]
      rfl
  · intro slot field
    simp only [binary,FixedArrayTable.read_ofFn,RationalSegmentLottery.binary]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hrFirst.2.1 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hrSecond.2.1 j field
  · intro slot field
    simp only [binary,FixedArrayTable.read_ofFn,RationalSegmentLottery.binary]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hrFirst.2.2 j field
    · intro j; simpa only [Fin.addCases_left,Fin.addCases_right] using hrSecond.2.2 j field

def shiftThird {k : ℕ} (table : Segment 3 k) (s : SignedWord) : Segment 3 k where
  weight := table.weight
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(table.P.read slot).read 0,
    (table.P.read slot).read 1,BinaryRationalOpcode.apply .add ((table.P.read slot).read 2) s])
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(table.Q.read slot).read 0,
    (table.Q.read slot).read 1,BinaryRationalOpcode.apply .add ((table.Q.read slot).read 2) s])

theorem shiftThird_canonical {k : ℕ} (table : Segment 3 k) (s : SignedWord)
    (h : table.Canonical) (hs : BinaryRationalEncoding.CanonicalWord s) : (shiftThird table s).Canonical := by
  refine ⟨h.1,?_,?_⟩
  · intro slot field
    simp only [shiftThird,FixedArrayTable.read_ofFn]
    fin_cases field
    · exact h.2.1 slot 0
    · exact h.2.1 slot 1
    · exact BinaryReflectedFourSetup.opcode_canonical .add _ _ (h.2.1 slot 2) hs
  · intro slot field
    simp only [shiftThird,FixedArrayTable.read_ofFn]
    fin_cases field
    · exact h.2.2 slot 0
    · exact h.2.2 slot 1
    · exact BinaryReflectedFourSetup.opcode_canonical .add _ _ (h.2.2 slot 2) hs

theorem shiftThird_refines {k : ℕ} (table : Segment 3 k) (s : SignedWord) (source : RationalSegmentLottery 3 k)
    (h : table.Canonical) (hs : BinaryRationalEncoding.CanonicalWord s) (hr : table.Refines source) :
    (shiftThird table s).Refines (source.shiftThird (value s)) := by
  refine ⟨hr.1,?_,?_⟩
  · intro slot field
    simp only [shiftThird,FixedArrayTable.read_ofFn,RationalSegmentLottery.shiftThird]
    fin_cases field
    · exact hr.2.1 slot 0
    · exact hr.2.1 slot 1
    · change value (BinaryRationalOpcode.apply .add ((table.P.read slot).read 2) s) = source.P slot 2 + value s
      rw [BinaryRationalOpcode.apply_value .add _ _ (h.2.1 slot 2).1 hs.1,hr.2.1 slot 2]
      rfl
  · intro slot field
    simp only [shiftThird,FixedArrayTable.read_ofFn,RationalSegmentLottery.shiftThird]
    fin_cases field
    · exact hr.2.2 slot 0
    · exact hr.2.2 slot 1
    · change value (BinaryRationalOpcode.apply .add ((table.Q.read slot).read 2) s) = source.Q slot 2 + value s
      rw [BinaryRationalOpcode.apply_value .add _ _ (h.2.2 slot 2).1 hs.1,hr.2.2 slot 2]
      rfl

end Blotto.BinarySegmentAssembly

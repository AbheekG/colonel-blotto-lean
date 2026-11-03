import Blotto.GeneralPaperStoredMidpointAssembly

/-! A loaded bit count drives fresh collection; the actual padded list is
materialized once and decoded by balanced merges over its actual array size.
The zero high bit changes neither rank nor the number of fresh bit calls. -/
namespace Blotto.GeneralPaperStoredFreshDecoder
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

structure Result (S : Type*) where
  value : ℕ
  state : S
  reads : ℕ
  work : ℕ

def run {S : Type*} (model : RationalCostModel) (A count : ℕ) (next : S → Bool × S) (state : S) : Result S :=
  let collected := GeneralPaperStoredFreshCollect.collect model A next count [] state
  let buffer := PaperListReferenceArray.run (fun w => w) A collected.bits
  let decoded := GeneralPaperBalancedBitDecoder.run (fun w => w) A buffer.1 0 buffer.1.size
  ⟨decoded.value,collected.state,collected.reads,collected.work + buffer.2 + decoded.work + 128 * (A + 1)⟩

theorem data {S : Type*} (model : RationalCostModel) (A count : ℕ) (next : S → Bool × S) (state : S) :
    (run model A count next state).value =
      BinaryBigEndian.littleValue (GeneralPaperStoredFreshCollect.collect model A next count [] state).bits := by
  simp only [run,GeneralPaperBalancedBitDecoder.data,PaperListReferenceArray.data,List.size_toArray]
  exact (BinaryBigEndian.littleValue_decode _).symm

theorem reads {S : Type*} (model : RationalCostModel) (A count : ℕ) (next : S → Bool × S) (state : S) :
    (run model A count next state).reads = count := GeneralPaperStoredFreshCollect.reads model A next count [] state

theorem work {S : Type*} (model : RationalCostModel) (A count : ℕ) (next : S → Bool × S) (state : S) :
    (run model A count next state).work = GeneralPaperStoredFreshCollect.price model A count 0 +
      (PaperListReferenceArray.run (fun w => w) A (GeneralPaperStoredFreshCollect.collect model A next count [] state).bits).2 +
      (GeneralPaperBalancedBitDecoder.run (fun w => w) A
        (GeneralPaperStoredFreshCollect.collect model A next count [] state).bits.toArray 0 (count + 1)).work + 128 * (A + 1) := by
  simp only [run,GeneralPaperStoredFreshCollect.work,List.length_nil,PaperListReferenceArray.data,List.size_toArray,
    GeneralPaperStoredFreshCollect.length,Nat.add_zero]

theorem source (model : RationalCostModel) (A count : ℕ) (fresh : Fin count → Bool) :
    (run model A count GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).value = (balancedBitIndex count fresh).val ∧
      (run model A count GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model A count GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = count := by
  have hCollect := GeneralPaperStoredFreshCollect.data model A GeneralPaperBooleanFreshWord.nextList
    (List.replicate count ()) [] (List.ofFn fresh)
  rw [List.length_replicate] at hCollect
  have hList := GeneralPaperBooleanFreshWord.collect_list (List.replicate count ()) (List.ofFn fresh) [] [] (by simp)
  simp only [List.reverse_nil,List.nil_append,List.append_nil] at hList
  have hBits := hCollect.1.trans hList.1
  refine ⟨?_,hCollect.2.trans hList.2,reads model A count _ _⟩
  rw [data,hBits,BinaryWordHighBit.littleValue_append]
  simp only [BinaryBigEndian.littleValue,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero]
  rw [GeneralPaperBooleanFreshWord.list_value,balancedBitIndex_eq]

end Blotto.GeneralPaperStoredFreshDecoder

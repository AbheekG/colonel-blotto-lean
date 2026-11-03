import Blotto.GeneralPaperRankBits

/-! A bounded-position lookup wraps the priced loop, preserving its native
work/probe fields. The size is the retained array size, not a repeated source
constructor. Clamping, metadata arithmetic and return writes are priced.
-/
namespace Blotto.GeneralPaperRankLookupPrice
open GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

structure Lookup (n : ℕ) where
  position : Fin (n+1)
  work : ℕ
  probes : ℕ

def specification {n : ℕ} (depth : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ) : Lookup n :=
  let result := GeneralPaperRankSearch.run values cut depth depth 0 n
  ⟨⟨min result.rank n,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,result.work+8,result.probes⟩

def run {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W depth : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ) : Lookup n × ℕ :=
  let result := GeneralPaperRankExecution.run bits primitive W values cut depth depth 0 n
  (⟨⟨min result.1.rank n,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,result.1.work+8,result.1.probes⟩,
    result.2+GeneralPaperIntegerWordPrice.compare primitive result.1.rank n+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) result.1.work 8+64*W)

theorem data {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W depth : ℕ) (values : FixedArrayTable n ℕ)
    (cut : ℕ) (hSize : n<2^depth) : (run bits primitive W depth values cut).1=specification depth values cut := by
  simp only [run,specification,GeneralPaperRankExecutionData.data bits primitive W values cut depth depth 0 n (Nat.zero_le _) (Nat.le_refl _) hSize]

theorem bit_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W depth V : ℕ)
    (values : FixedArrayTable n ℕ) (cut : ℕ) (hSize : n<2^depth) (hCut : cut≤V) (hValues : ∀ i,values.read i≤V) :
    (run true primitive W depth values cut).2≤1024*(depth+1)*(W+primitive (width depth V)) := by
  let N := magnitude n depth V
  let L := width depth V
  let result := GeneralPaperRankExecution.run true primitive W values cut depth depth 0 n
  have hData := GeneralPaperRankExecutionData.data true primitive W values cut depth depth 0 n (Nat.zero_le _) (Nat.le_refl _) hSize
  have hRank : result.1.rank≤n := by rw [hData]; exact GeneralPaperRankReturnPrice.rank_le_hi values cut depth depth 0 n (Nat.zero_le _) (Nat.le_refl _) hSize
  have hWork : result.1.work≤depth*(12*depth+34)+8 := by rw [hData]; exact GeneralPaperRankSearch.run_work _ _ _ _ _ _
  have hN := basic n depth V
  have hWord := word_bound n depth V hSize
  have hMeta : result.1.work+8≤64*(depth+1)^2 := by nlinarith only [hWork,Nat.zero_le depth]
  have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono result.1.rank n L
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp only [N]; omega : result.1.rank≤N)) 1).trans hWord)
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp only [N]; omega : n≤N)) 1).trans hWord)
  have hm := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) result.1.work 8 N
    (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by dsimp only [N]; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have h := GeneralPaperRankBits.work primitive hMono W values cut depth V depth 0 n
    (Nat.zero_le _) (Nat.le_refl _) hSize (Nat.le_refl _) hCut hValues
  change result.2≤512*(depth+1)*(W+primitive L) at h
  change _≤2*primitive L at hm
  change result.2+GeneralPaperIntegerWordPrice.compare primitive result.1.rank n+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) result.1.work 8+64*W≤1024*(depth+1)*(W+primitive L)
  nlinarith only [h,hc,hm,Nat.zero_le depth]

theorem arithmetic_work {n : ℕ} (depth : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ) :
    (run false (fun _ => 1) 1 depth values cut).2≤512*(depth+1)^2+67 := by
  have h := GeneralPaperRankArithmetic.work values cut depth depth 0 n
  change (GeneralPaperRankExecution.run false (fun _ => 1) 1 values cut depth depth 0 n).2+1+2+64≤_
  nlinarith only [h]

end Blotto.GeneralPaperRankLookupPrice

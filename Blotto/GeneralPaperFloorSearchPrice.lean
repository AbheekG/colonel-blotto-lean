import Blotto.GeneralPaperRankLookupPrice
import Blotto.GeneralPaperFloorSearch

/-! The retained rank loop supplies the floor label. Subtraction, clamping,
native work annotations and return controls are charged. The unit path uses
the bounded arithmetic midpoint; only the bit path uses integer halving. -/
namespace Blotto.GeneralPaperFloorSearchPrice
open GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W depth : ℕ)
    (values : FixedArrayTable n ℕ) (hN : 0<n) (cut : ℕ) : GeneralPaperFloorSearch.Result n × ℕ :=
  let found := GeneralPaperRankLookupPrice.run bits primitive W depth values cut
  (⟨⟨min (found.1.position.val-1) (n-1),by have := Nat.min_le_right (found.1.position.val-1) (n-1); omega⟩,
      found.1.work+8⟩,
    found.2+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) found.1.position.val 1+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) n 1+
      GeneralPaperIntegerWordPrice.compare primitive (found.1.position.val-1) (n-1)+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) found.1.work 8+64*W)

theorem data {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W depth : ℕ)
    (values : FixedArrayTable n ℕ) (hN : 0<n) (cut : ℕ) (hSize : n<2^depth) :
    (run bits primitive W depth values hN cut).1=GeneralPaperFloorSearch.lookup values hN depth cut := by
  have hr := GeneralPaperRankReturnPrice.rank_le_hi values cut depth depth 0 n
    (Nat.zero_le _) (Nat.le_refl _) hSize
  simp only [run,GeneralPaperRankLookupPrice.data bits primitive W depth values cut hSize,
    GeneralPaperRankLookupPrice.specification,GeneralPaperFloorSearch.lookup,Nat.min_eq_left hr]

theorem bit_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W depth V : ℕ)
    (values : FixedArrayTable n ℕ) (hN : 0<n) (cut : ℕ) (hSize : n<2^depth)
    (hCut : cut≤V) (hValues : ∀ i,values.read i≤V) :
    (run true primitive W depth values hN cut).2≤2048*(depth+1)*(W+primitive (width depth V)) := by
  let found := GeneralPaperRankLookupPrice.run true primitive W depth values cut
  let N := magnitude n depth V
  let L := width depth V
  have hData := GeneralPaperRankLookupPrice.data true primitive W depth values cut hSize
  have hRank : found.1.position.val≤n := Nat.le_of_lt_succ found.1.position.isLt
  have hWork : found.1.work≤depth*(12*depth+34)+16 := by
    rw [hData]
    exact Nat.add_le_add_right (GeneralPaperRankSearch.run_work values cut depth depth 0 n) 8
  have hN := basic n depth V
  have hWord := word_bound n depth V hSize
  have hMeta : found.1.work+8≤64*(depth+1)^2 := by nlinarith only [hWork,Nat.zero_le depth]
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have a := p (fun a b => a-b) found.1.position.val 1 (by dsimp only [N]; omega)
    (by dsimp only [N]; omega) (by dsimp only [N]; omega)
  have b := p (fun a b => a-b) n 1 (by dsimp only [N]; omega)
    (by dsimp only [N]; omega) (by dsimp only [N]; omega)
  have c := GeneralPaperIntegerWordPrice.compare_le primitive hMono (found.1.position.val-1) (n-1) L
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp only [N]; omega : found.1.position.val-1≤N)) 1).trans hWord)
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp only [N]; omega : n-1≤N)) 1).trans hWord)
  have d := p (fun a b => a+b) found.1.work 8 (by dsimp only [N]; omega)
    (by dsimp only [N]; omega) (by dsimp only [N]; omega)
  have h := GeneralPaperRankLookupPrice.bit_work primitive hMono W depth V values cut hSize hCut hValues
  change found.2≤1024*(depth+1)*(W+primitive L) at h
  change found.2+_+_+_+_+64*W≤2048*(depth+1)*(W+primitive L)
  nlinarith only [h,a,b,c,d,Nat.zero_le depth]

theorem arithmetic_work {n : ℕ} (depth : ℕ) (values : FixedArrayTable n ℕ) (hN : 0<n) (cut : ℕ) :
    (run false (fun _ => 1) 1 depth values hN cut).2≤512*(depth+1)^2+138 := by
  have h := GeneralPaperRankLookupPrice.arithmetic_work depth values cut
  change (GeneralPaperRankLookupPrice.run false (fun _ => 1) 1 depth values cut).2+2+2+1+2+64≤_
  omega

end Blotto.GeneralPaperFloorSearchPrice

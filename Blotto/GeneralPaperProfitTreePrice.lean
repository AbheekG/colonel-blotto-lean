import Blotto.GeneralPaperProfitTreeExecution

/-! Complete tree-construction prices. Exact dyadic spans bound split
counters at every subtree. Reference W remains explicit. The real-RAM
halving path contributes a height factor; balanced recursion pays it only
at the nodes where it executes. -/
namespace Blotto.GeneralPaperProfitTreePrice
open GeneralPaperProfitTreeExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem span_word (height H : ℕ) (h : height≤H) :
    1+binaryWordWidth (2^height+1)≤GeneralPaperTreeHalfPrice.width H := by
  have hp := GeneralPaperNatPowerOperands.power_width 2 height
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (2^height) 1
  have h2 : binaryWordWidth 2=2 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  rw [h2] at hp
  unfold GeneralPaperTreeHalfPrice.width GeneralPaperRankOperands.width
  omega

theorem height_word (height H : ℕ) (h : height≤H) :
    1+binaryWordWidth (height+2)≤GeneralPaperTreeHalfPrice.width H := by
  have hw := GeneralPaperInitializerControlCounters.word_le_self (height+2)
  unfold GeneralPaperTreeHalfPrice.width GeneralPaperRankOperands.width
  omega

theorem width_mono (height H : ℕ) (h : height≤H) :
    GeneralPaperTreeHalfPrice.width height≤GeneralPaperTreeHalfPrice.width H := by
  unfold GeneralPaperTreeHalfPrice.width GeneralPaperRankOperands.width
  omega

theorem build_bit_work {R : Type} {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W H height span : ℕ) (zero : GeneralPaperOrderedProfitTreeBuild.WeightedField R K)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K)) (hHeight : height≤H) (hSpan : span=2^height) :
    (build true primitive W zero height span input).2≤
      1024*2^height*(height+1)*(W+primitive (GeneralPaperTreeHalfPrice.width H)) := by
  let P := primitive (GeneralPaperTreeHalfPrice.width H)
  let C := W+P
  induction height generalizing span input with
  | zero =>
    have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono 0 0 (GeneralPaperTreeHalfPrice.width H)
      ((Nat.add_le_add_left (binaryWordWidth_mono (show 0≤0+2 by omega)) 1).trans (height_word 0 H (Nat.zero_le _)))
      ((Nat.add_le_add_left (binaryWordWidth_mono (show 0≤0+2 by omega)) 1).trans (height_word 0 H (Nat.zero_le _)))
    change GeneralPaperIntegerWordPrice.compare primitive 0 0+64*W≤1024*2^0*(0+1)*C
    change _≤P at hc
    dsimp only [C]
    omega
  | succ height ih =>
    have hd := GeneralPaperTreeHalfPrice.data true primitive W height span hSpan
    have hh := GeneralPaperTreeHalfPrice.bit_work primitive hMono W height span hSpan
    have hp := hMono (width_mono height H (by omega))
    have hc := GeneralPaperPricedListSplit.control_work primitive hMono W (height+1) (height+1) (Nat.le_refl _)
    have hcPrice := hMono (height_word height H (by omega))
    have hs := GeneralPaperPricedListSplit.work primitive hMono W (2^height) (2^height) input (Nat.le_refl _)
    have hsPrice := hMono (span_word height H (by omega))
    have hl := ih (2^height) (GeneralPaperPricedListSplit.run primitive W (2^height) input).1.1 (by omega) rfl
    have hr := ih (2^height) (GeneralPaperPricedListSplit.run primitive W (2^height) input).1.2 (by omega) rfl
    rw [build]
    dsimp only
    rw [hd]
    change _≤1024*2^(height+1)*(height+1+1)*C
    change _≤1024*2^height*(height+1)*C at hl hr
    change primitive (GeneralPaperTreeHalfPrice.width height)≤P at hp
    change primitive (1+binaryWordWidth (height+1+1))≤P at hcPrice
    change primitive (1+binaryWordWidth (2^height+1))≤P at hsPrice
    have ht : 1≤2^height := Nat.one_le_two_pow
    have hh' : (GeneralPaperTreeHalfPrice.run true primitive W height span).2≤10*P+128*W := by omega
    have hc' : GeneralPaperPricedListSplit.control primitive W (height+1)≤4*P+64*W := by omega
    have hs' := hs.trans (Nat.mul_le_mul_left (2^height+1)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hsPrice) (64*W)))
    have hw := Nat.mul_le_mul_right W ht
    have hP := Nat.mul_le_mul_right P ht
    rw [pow_succ]
    dsimp only [C] at hl hr ⊢
    nlinarith only [hh',hc',hs',hl,hr,hw,hP,Nat.zero_le (2^height*W),Nat.zero_le (2^height*P)]

theorem build_arithmetic_work {R : Type} {K : ℕ} (height span : ℕ)
    (zero : GeneralPaperOrderedProfitTreeBuild.WeightedField R K)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K)) (hSpan : span=2^height) :
    (build false (fun _ => 1) 1 zero height span input).2≤1024*2^height*(height+1)^2 := by
  induction height generalizing span input with
  | zero => change 65≤1024*2^0*(0+1)^2; norm_num
  | succ height ih =>
    have hd := GeneralPaperTreeHalfPrice.data false (fun _ => 1) 1 height span hSpan
    have hh := GeneralPaperTreeHalfPrice.arithmetic_work height span
    have hs := GeneralPaperPricedListSplit.arithmetic_work (2^height) input
    have hl := ih (2^height) (GeneralPaperPricedListSplit.run (fun _ => 1) 1 (2^height) input).1.1 rfl
    have hr := ih (2^height) (GeneralPaperPricedListSplit.run (fun _ => 1) 1 (2^height) input).1.2 rfl
    rw [build]
    dsimp only
    rw [hd,hh]
    change (12*height+172)+_+_+_+67+128≤_
    have ht : 1≤2^height := Nat.one_le_two_pow
    rw [pow_succ]
    nlinarith only [hs,hl,hr,ht,Nat.zero_le (2^height*height),Nat.zero_le height]

end Blotto.GeneralPaperProfitTreePrice

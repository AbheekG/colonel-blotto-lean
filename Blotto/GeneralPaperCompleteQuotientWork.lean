import Blotto.GeneralPaperQuotientControlPrice

/-! One affine remainder invariant bounds all reached rational operands.
Counter prices are included in the same recurrence, in both machine models.
-/
namespace Blotto.GeneralPaperCompleteQuotientWork
open GeneralPaperCompleteQuotientPrice GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem rational_width (A t depth : ℕ) : 1+2*heightBudget A t depth≤width A t depth := by
  unfold width
  omega

theorem step_bound (depth W P r doubled compare controls selected : ℕ)
    (hr : r≤(depth+1)*(16*P+64*W)) (hd : doubled≤2*P) (hc : compare≤P)
    (hControl : controls≤6*P) (hs : selected≤4*P) :
    r+doubled+compare+controls+64*W+selected≤(depth+1+1)*(16*P+64*W) := by
  nlinarith only [hr,hd,hc,hControl,hs]

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W : ℕ) (x a : ℚ) (ha : 0<a)
    (depth A t : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^depth) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    (run price W x a depth).2≤(depth+1)*(16*price (width A t depth)+64*W) := by
  induction depth generalizing a t with
  | zero =>
    have h0 := hMono (constant_word A t 0 0 (by omega))
    have h2 := hMono (constant_word A t 0 2 (by omega))
    have hXW := hMono ((rationalWordWidth_of_height hX).trans
      (show 1+2*A≤width A t 0 by unfold width heightBudget; omega))
    change price (GeneralPaperNaturalPrimitivePrice.word 0)≤_ at h0
    change price (GeneralPaperNaturalPrimitivePrice.word 2)≤_ at h2
    change price (GeneralPaperNaturalPrimitivePrice.word 0)+price (GeneralPaperNaturalPrimitivePrice.word 2)+
      price (rationalWordWidth x)+32*W≤_
    nlinarith only [h0,h2,hXW]
  | succ depth ih =>
    have hCap' : x<(2*a)*(2:ℚ)^depth := by rw [pow_succ] at hCap; nlinarith only [hCap]
    have hRec := ih (a:=2*a) (t:=t+2) (by positivity) hCap' (doubled_height a t hA)
    rw [width_step] at hRec
    let L := width A t (depth+1)
    have hOld : rationalWordWidth a≤L := (rationalWordWidth_of_height hA).trans
      (by dsimp [L,width,heightBudget]; omega)
    have hTwo : rationalWordWidth (2:ℚ)≤L := by
      have h : RationalHeight 2 2 := by norm_num [RationalHeight]
      exact (rationalWordWidth_of_height h).trans (by dsimp [L,width,heightBudget]; omega)
    have hDouble : rationalWordWidth (2*a)≤L := (rationalWordWidth_of_height (doubled_height a t hA)).trans
      (by dsimp [L,width,heightBudget]; omega)
    have hHigher : rationalWordWidth (GeneralPaperBoundedQuotient.run x (2*a) depth).remainder≤L :=
      (rationalWordWidth_of_height (higher_remainder_common x a ha depth A t hx hCap hX hA)).trans
        (rational_width A t (depth+1))
    have hMul := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 a L hTwo hOld hDouble
    have hCompare := hMono (show RationalExpression.pairWidth a (GeneralPaperBoundedQuotient.run x (2*a) depth).remainder≤L
      from max_le hOld hHigher)
    have hControl := GeneralPaperQuotientControlPrice.control_work price hMono x a A t depth
    have hIncrement := GeneralPaperQuotientControlPrice.selected_quotient_work price hMono x a A t depth
    have hCurrent := remainder_common x a ha (depth+1) A t hx hCap hX hA
    rw [GeneralPaperCompleteQuotientPrice.run]
    simp only [data]
    split
    · rename_i hBit
      have hOut : rationalWordWidth ((GeneralPaperBoundedQuotient.run x (2*a) depth).remainder-a)≤L := by
        simp only [GeneralPaperBoundedQuotient.run,ite_eq_left hBit] at hCurrent
        exact (rationalWordWidth_of_height hCurrent).trans (rational_width A t (depth+1))
      have hSub := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a-b) _ a L hHigher hOld hOut
      have hSelected : selectedCost price a (GeneralPaperBoundedQuotient.run x (2*a) depth)≤4*price L := by
        unfold selectedCost
        change _≤2*price L at hIncrement
        omega
      exact step_bound depth W (price L) _ _ _ _ _ hRec hMul hCompare hControl hSelected
    · have h := step_bound depth W (price L) _ _ _ _ 0 hRec hMul hCompare hControl (Nat.zero_le _)
      simpa only [Nat.add_zero] using h

theorem arithmetic_work (x a : ℚ) (depth : ℕ) : (run (fun _ => 1) 1 x a depth).2≤80*(depth+1) := by
  induction depth generalizing a with
  | zero => change 35≤80; omega
  | succ depth ih =>
    have hr := ih (2*a)
    rw [GeneralPaperCompleteQuotientPrice.run]
    split
    · change (run (fun _ => 1) 1 x (2*a) depth).2+77≤80*(depth+1+1)
      omega
    · change (run (fun _ => 1) 1 x (2*a) depth).2+73≤80*(depth+1+1)
      omega

theorem same_data (price : ℕ → ℕ) (W : ℕ) (x a : ℚ) (depth : ℕ) :
    (run price W x a depth).1=(run (fun _ => 1) 1 x a depth).1 := by rw [data,data]

end Blotto.GeneralPaperCompleteQuotientWork

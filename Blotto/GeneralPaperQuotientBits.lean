import Blotto.GeneralPaperQuotientHeight

/-! Actual operand bit prices for the arithmetic-only bounded quotient.
The source control word W must cover constructed counters and references;
the rational prices and writes below use actual reduced operand lengths.
-/
namespace Blotto.GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 1500000

def primitivePrice (model : RationalCostModel) (a b : ℚ) : ℕ :=
  model.rat (RationalExpression.pairWidth a b)

theorem primitivePrice_le (model : RationalCostModel) (a b : ℚ) (H : ℕ)
    (ha : rationalWordWidth a≤H) (hb : rationalWordWidth b≤H) : primitivePrice model a b≤model.rat H :=
  model.monotone (max_le ha hb)

def runWithBits (model : RationalCostModel) (W : ℕ) (x a : ℚ) : ℕ → Result × ℕ
  | 0 => (⟨0,x,2⟩,2*W+rationalWordWidth x)
  | w+1 =>
      let doubled := 2*a
      let higher := runWithBits model W x doubled w
      let common := higher.2+64*W+primitivePrice model 2 a+rationalWordWidth doubled+
        primitivePrice model a higher.1.remainder
      if a≤higher.1.remainder then
        (⟨2*higher.1.quotient+1,higher.1.remainder-a,higher.1.work+12⟩,
          common+primitivePrice model higher.1.remainder a+rationalWordWidth (higher.1.remainder-a))
      else
        (⟨2*higher.1.quotient,higher.1.remainder,higher.1.work+12⟩,
          common+rationalWordWidth higher.1.remainder)

theorem run_data (model : RationalCostModel) (W : ℕ) (x a : ℚ) (w : ℕ) :
    (runWithBits model W x a w).1=run x a w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    simp only [runWithBits,ih,run]
    split <;> rfl

def bitProfile (model : RationalCostModel) (W A t w : ℕ) : ℕ :=
  (w+1)*(64*W+6*model.rat (1+2*heightBudget A t w))

theorem run_bit_work (model : RationalCostModel) (W : ℕ) (x a : ℚ) (ha : 0<a) (w A t : ℕ)
    (hx : 0≤x) (hCap : x<a*(2:ℚ)^w) (hX : RationalHeight x A) (hA : RationalHeight a t) :
    (runWithBits model W x a w).2≤bitProfile model W A t w := by
  induction w generalizing a t with
  | zero =>
    have hw := (rationalWordWidth_of_height (hX.mono (show A≤heightBudget A t 0 by unfold heightBudget; omega))).trans
      (model.word_le _)
    simp only [runWithBits,bitProfile,Nat.zero_add,Nat.one_mul]
    omega
  | succ w ih =>
    have hc : x<(2*a)*(2:ℚ)^w := by rw [pow_succ] at hCap; nlinarith only [hCap]
    have hd := doubled_height a t hA
    have hRec := ih (a:=2*a) (t:=t+2) (by positivity) hc hd
    unfold bitProfile at hRec ⊢
    rw [budget_step] at hRec
    let B := heightBudget A t (w+1)
    let H := 1+2*B
    let P := model.rat H
    have hOld : rationalWordWidth a≤H :=
      rationalWordWidth_of_height (hA.mono (by dsimp only [H,B,heightBudget]; omega))
    have hTwo : rationalWordWidth (2:ℚ)≤H := by
      have h2 : RationalHeight 2 2 := by norm_num [RationalHeight]
      exact rationalWordWidth_of_height (h2.mono (by dsimp only [H,B,heightBudget]; omega))
    have hDouble : rationalWordWidth (2*a)≤P :=
      (rationalWordWidth_of_height (hd.mono (by dsimp only [B,heightBudget]; omega))).trans (model.word_le H)
    have hHigher := rationalWordWidth_of_height (higher_remainder_common x a ha w A t hx hCap hX hA)
    have hHigherCopy : rationalWordWidth (run x (2*a) w).remainder≤P := hHigher.trans (model.word_le H)
    have hMul := primitivePrice_le model 2 a H hTwo hOld
    have hCompare := primitivePrice_le model a (run x (2*a) w).remainder H hOld hHigher
    have hSubtract := primitivePrice_le model (run x (2*a) w).remainder a H hHigher hOld
    have hCurrent := remainder_common x a ha (w+1) A t hx hCap hX hA
    unfold runWithBits
    dsimp only
    simp only [run_data]
    split
    · rename_i hBit
      have hOut : rationalWordWidth ((run x (2*a) w).remainder-a)≤P := by
        simp only [run,ite_eq_left hBit] at hCurrent
        exact (rationalWordWidth_of_height hCurrent).trans (model.word_le H)
      change (runWithBits model W x (2*a) w).2+64*W+primitivePrice model 2 a+rationalWordWidth (2*a)+
        primitivePrice model a (run x (2*a) w).remainder+primitivePrice model (run x (2*a) w).remainder a+
          rationalWordWidth ((run x (2*a) w).remainder-a)≤_
      change (runWithBits model W x (2*a) w).2≤(w+1)*(64*W+6*P) at hRec
      change _≤(w+1+1)*(64*W+6*P)
      nlinarith only [hRec,hMul,hDouble,hCompare,hSubtract,hOut]
    · rename_i _hBit
      change (runWithBits model W x (2*a) w).2+64*W+primitivePrice model 2 a+rationalWordWidth (2*a)+
        primitivePrice model a (run x (2*a) w).remainder+rationalWordWidth (run x (2*a) w).remainder≤_
      change (runWithBits model W x (2*a) w).2≤(w+1)*(64*W+6*P) at hRec
      change _≤(w+1+1)*(64*W+6*P)
      nlinarith only [hRec,hMul,hDouble,hCompare,hHigherCopy]

end Blotto.GeneralPaperBoundedQuotient

import Blotto.GeneralPaperActualSummaryArrays

/-! The bit midpoint divides one constructed integer sum by two. The
separate unit implementation retains bounded real division. Only quotient
and native work metadata are needed by the rank loop, so no unused rational
remainder is constructed in the bit implementation.
-/
namespace Blotto.GeneralPaperRankMidpointPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

structure Result where
  quotient : ℕ
  work : ℕ

def specification (depth lo hi : ℕ) : Result :=
  let found := GeneralPaperRankMidpoint.midpoint depth lo hi
  ⟨found.quotient,found.work⟩

def run (bits : Bool) (primitive : ℕ → ℕ) (W depth lo hi : ℕ) : Result × ℕ :=
  if bits then
    let sum := lo+hi
    (⟨sum/2,12*depth+2⟩,
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) lo hi+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) sum 2+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 12 depth+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (12*depth) 2+64*W)
  else
    let found := GeneralPaperRankMidpoint.midpoint depth lo hi
    (⟨found.quotient,found.work⟩,found.work+80)

theorem data (bits : Bool) (primitive : ℕ → ℕ) (W n depth lo hi : ℕ)
    (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    (run bits primitive W depth lo hi).1=specification depth lo hi := by
  cases bits
  · rfl
  · have hCap : lo+hi<2*2^depth := by omega
    have hq := GeneralPaperFastConstructedDivision.quotient_data (lo+hi) 2 depth (by decide) hCap
    have hNative : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient=(lo+hi)/2 := by
      simpa only [GeneralPaperRankMidpoint.midpoint,Nat.cast_add,Nat.cast_ofNat] using hq
    simp only [run,ite_true,specification,hNative,GeneralPaperRankMidpoint.midpoint_work]

theorem work_field (bits : Bool) (primitive : ℕ → ℕ) (W depth lo hi : ℕ) :
    (run bits primitive W depth lo hi).1.work=12*depth+2 := by
  cases bits <;> simp only [run,Bool.false_eq_true,ite_false,ite_true,GeneralPaperRankMidpoint.midpoint_work]

theorem arithmetic_work (depth lo hi : ℕ) : (run false (fun _ => 1) 1 depth lo hi).2=12*depth+82 := by
  simp only [run,Bool.false_eq_true,ite_false,GeneralPaperRankMidpoint.midpoint_work]

end Blotto.GeneralPaperRankMidpointPrice

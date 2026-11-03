import Blotto.GeneralPaperOrderedDPAggregatePrice

/-! Root labels use native integer order and keep the higher label. Index
prices are distinct from exact rational resource comparisons. -/
namespace Blotto.GeneralPaperRootPickPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {J : ℕ} (index : ℕ → ℕ) (W : ℕ) : Option (Fin J) → Option (Fin J) → Option (Fin J) × ℕ
  | none,b => (b,64*W)
  | a,none => (a,64*W)
  | some a,some b => (if a≤b then some b else some a,
    GeneralPaperIntegerWordPrice.compare index a.val b.val+64*W)

theorem data {J : ℕ} (index : ℕ → ℕ) (W : ℕ) (a b : Option (Fin J)) :
    (run index W a b).1=GeneralPaperOrderedProfitRoot.pick a b := by
  cases a <;> cases b <;> rfl

theorem work {J : ℕ} (index : ℕ → ℕ) (W A : ℕ) (a b : Option (Fin J))
    (hIndex : ∀ i : Fin J,index (1+binaryWordWidth i.val)≤A) : (run index W a b).2≤A+64*W := by
  cases a with
  | none => change 64*W≤_; omega
  | some a =>
    cases b with
    | none => change 64*W≤_; omega
    | some b =>
      have hc : GeneralPaperIntegerWordPrice.compare index a.val b.val≤A := by
        unfold GeneralPaperIntegerWordPrice.compare GeneralPaperNaturalPrimitivePrice.word
        by_cases h : 1+binaryWordWidth a.val≤1+binaryWordWidth b.val
        · rw [max_eq_right h]; exact hIndex b
        · rw [max_eq_left (by omega : 1+binaryWordWidth b.val≤1+binaryWordWidth a.val)]; exact hIndex a
      change GeneralPaperIntegerWordPrice.compare index a.val b.val+64*W≤_
      omega

theorem arithmetic_work {J : ℕ} (a b : Option (Fin J)) : (run (fun _ => 1) 1 a b).2≤65 := by
  cases a <;> cases b <;> norm_num [run,GeneralPaperIntegerWordPrice.compare]

end Blotto.GeneralPaperRootPickPrice

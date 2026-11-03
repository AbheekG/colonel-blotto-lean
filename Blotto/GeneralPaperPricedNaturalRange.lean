import Blotto.GeneralPaperProfitOrderPrice

/-! A countdown range constructor. Consing onto the accumulated suffix
avoids copying an already built prefix. Its output is the ordinary range.
-/
namespace Blotto.GeneralPaperPricedNaturalRange
set_option autoImplicit false

def into (W : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | 0, tail => (tail,2*W)
  | n+1, tail =>
    let earlier := into W n (n::tail)
    (earlier.1,earlier.2+32*W)

theorem into_data (W n : ℕ) (tail : List ℕ) :
    (into W n tail).1=List.range n++tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [into,ih,List.range_succ,List.append_assoc,List.singleton_append]

theorem into_work (W n : ℕ) (tail : List ℕ) :
    (into W n tail).2=32*n*W+2*W := by
  induction n generalizing tail with
  | zero => simp only [into,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ n ih => simp only [into,ih]; ring

def run (W n : ℕ) : List ℕ × ℕ := into W n []

theorem data (W n : ℕ) : (run W n).1=List.range n := by
  rw [run,into_data,List.append_nil]

theorem work (W n : ℕ) : (run W n).2=32*n*W+2*W := into_work W n []

end Blotto.GeneralPaperPricedNaturalRange

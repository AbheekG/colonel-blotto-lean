import Blotto.GeneralPaperBasisAppendIndex

/-! A literal tail-accumulator integer dot product for indexed vector and
matrix readers. Its unit profile covers at most three indexed reads, one
integer multiplication/addition and loop control per coordinate.
-/
namespace Blotto.GeneralPaperBasisIntegerDot
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  value : ℤ
  work : ℕ

def loop {i : Type*} (f g : i → ℤ) : List i → ℤ → ℕ → Result
  | [],a,spent => ⟨a,spent+2⟩
  | j::rest,a,spent => loop f g rest (a+f j*g j) (spent+12)

theorem loop_data {i : Type*} (f g : i → ℤ) (xs : List i) (a : ℤ) (spent : ℕ) :
    (loop f g xs a spent).value=a+(xs.map (fun j => f j*g j)).sum ∧
      (loop f g xs a spent).work=spent+12*xs.length+2 := by
  induction xs generalizing a spent with
  | nil => simp only [loop,List.map_nil,List.sum_nil,add_zero,List.length_nil,Nat.mul_zero,and_self]
  | cons j rest ih =>
    have hh := ih (a+f j*g j) (spent+12)
    simp only [loop,List.map_cons,List.sum_cons,List.length_cons]
    exact ⟨by rw [hh.1]; ring,by rw [hh.2]; omega⟩

def run {n : ℕ} (f g : Fin n → ℤ) : Result :=
  let result := loop f g (List.finRange n) 0 0
  ⟨result.value,result.work+4*n+4⟩

theorem run_value {n : ℕ} (f g : Fin n → ℤ) : (run f g).value=∑ j,f j*g j := by
  have hh := (loop_data f g (List.finRange n) 0 0).1
  change (loop f g (List.finRange n) 0 0).value=_
  simpa only [zero_add,←List.ofFn_eq_map,List.sum_ofFn] using hh

theorem run_work {n : ℕ} (f g : Fin n → ℤ) : (run f g).work=16*n+6 := by
  have hh := (loop_data f g (List.finRange n) 0 0).2
  change (loop f g (List.finRange n) 0 0).work+4*n+4=_
  simp only [List.length_finRange] at hh
  omega

end Blotto.GeneralPaperBasisIntegerDot

import Blotto.GeneralPaperSourceDyadicEquilibrium

/-! One literal streaming pass checks every original static constraint at
a stored rational point. This list has 3d+T rows, never high-tuple rows.
The arithmetic counter includes sparse evaluation and list construction.
-/
namespace Blotto.GeneralPaperFinalStaticCheck
open RationalOrderCell GeneralPaperStaticRayRows
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  accepted : Bool
  work : ℕ

def loop {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) :
    List (StaticIndex T m K) → Bool → ℕ → Result
  | [],accepted,spent => ⟨accepted,spent+2⟩
  | i::rest,accepted,spent =>
    let evaluated := GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i
    loop labels x rest (accepted && decide (evaluated.1.intercept≤0)) (spent+evaluated.2+8)

def run {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) : Result :=
  let result := loop labels x (enumerate T m K) true 0
  ⟨result.accepted,result.work+64*(m+m*(K-1)+T+1)⟩

theorem loop_accepted {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ)
    (is : List (StaticIndex T m K)) (accepted : Bool) (spent : ℕ) :
    (loop labels x is accepted spent).accepted=true ↔ accepted=true ∧
      ∀ i∈is,(GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).1.intercept≤0 := by
  induction is generalizing accepted spent with
  | nil => simp only [loop,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
  | cons i rest ih =>
    rw [loop,ih]
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.mem_cons,forall_eq_or_imp,and_assoc]

theorem loop_work {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ)
    (is : List (StaticIndex T m K)) (accepted : Bool) (spent : ℕ) :
    (loop labels x is accepted spent).work=spent+
      (is.map (fun i => (GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).2+8)).sum+2 := by
  induction is generalizing accepted spent with
  | nil => simp only [loop,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons i rest ih => rw [loop,ih,List.map_cons,List.sum_cons]; omega

end Blotto.GeneralPaperFinalStaticCheck

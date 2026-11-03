import Blotto.GeneralPaperRayMinimumSound

/-! Actual static ray scan over all original boxes, adjacent orders and
retained budgets. Sparse term evaluation and one streaming minimum produce
the exact endpoint/blocker. Row-construction overhead is included in the
arithmetic counter; high-score tuple constraints are not enumerated.
-/
namespace Blotto.GeneralPaperStaticRayScan
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows GeneralPaperRayAffine
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

def generation {T m K : ℕ} : StaticIndex T m K → ℕ
  | .inl _ => 16
  | .inr (.inl _) => 32
  | .inr (.inr _) => 16*m+32

def evaluate {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ) (i : StaticIndex T m K) :
    Affine × ℕ :=
  let r := GeneralPaperRaySparseEvaluation.evaluate (row labels i) x w
  (r.1,r.2+generation i)

def scan {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ) :
    GeneralPaperRayMinimum.Result (StaticIndex T m K) :=
  GeneralPaperRayMinimum.scan (evaluate labels x w) (enumerate T m K)

def charge {T m K : ℕ} : StaticIndex T m K → ℕ
  | .inl _ => 70
  | .inr (.inl _) => 98
  | .inr (.inr _) => 28*m+74

theorem evaluate_charge {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ)
    (i : StaticIndex T m K) : (evaluate labels x w i).2+32≤charge i := by
  change (GeneralPaperRaySparseEvaluation.evaluate (row labels i) x w).2+generation i+32≤_
  rw [GeneralPaperRaySparseEvaluation.evaluate_work]
  rcases i with ⟨v,b⟩|⟨j,l⟩|i
  · cases b <;> norm_num [row,constraints,embed,generation,charge]
  · have hl := rawRow_order_length (fun _ => 0) j (orderLeft l) (orderRight l)
    change 12*(rawRow (fun _ => 0) (.inl (j,orderLeft l,orderRight l))).terms.length+10+32+32≤98
    omega
  · have hl := rawRow_sum_length (fun _ => 0) (labels i) 0
    change 12*(rawRow (fun _ => 0) (.inr (labels i,0))).terms.length+10+(16*m+32)+32≤28*m+74
    omega

theorem charge_sum (T m K : ℕ) : ((enumerate T m K).map charge).sum=238*(m*(K-1))+T*(28*m+74) := by
  have hb (vs : List (Variable m K)) : (vs.flatMap (fun _ => [70,70])).sum=140*vs.length := by
    induction vs with
    | nil => rfl
    | cons v rest ih =>
      simp only [List.flatMap_cons,List.sum_append,List.sum_cons,List.sum_nil,List.length_cons,ih]
      omega
  simp [enumerate,boxes,orders,budgets,charge,List.map_flatMap,Function.comp_def,hb,variableList_length]
  omega

theorem scan_work {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ) :
    (scan labels x w).work≤238*(m*(K-1))+T*(28*m+74)+2 := by
  have hs := GeneralPaperRayMinimum.scan_work (evaluate labels x w) (enumerate T m K)
  have hl : ((enumerate T m K).map (fun i => (evaluate labels x w i).2+32)).sum≤((enumerate T m K).map charge).sum :=
    List.sum_le_sum (fun i hi => evaluate_charge labels x w i)
  rw [charge_sum] at hl
  change (scan labels x w).work=_ at hs
  omega

theorem scan_work_linear {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ) :
    (scan labels x w).work≤238*(m*(K-1))+102*(m*T)+2 := by
  have hs := scan_work labels x w
  nlinarith only [hs,show 1≤m by omega]

end Blotto.GeneralPaperStaticRayScan

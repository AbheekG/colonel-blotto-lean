import Blotto.GeneralPaperExactScoreTuples

/-! The actual stored exact-score DP computes h_* using a strict budget
test. Every score 0..S is represented; scores above h_* are not truncated.
The exponential tuple set occurs only in the proved reference specification.
-/
namespace Blotto.GeneralPaperComputedThreshold
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperDictionary GeneralPaperStrictScore
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

def acceptedScore {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K)))
    (budget : ℚ) (s : Fin (S+1)) : ℕ :=
  match table.read s with
  | none => 0
  | some chosen => if chosen.cost<budget then s.val else 0

def scanThreshold {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : ℕ :=
  Finset.univ.sup (acceptedScore table budget)

def table {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    FixedArrayTable (S+1) (Option (Selection K)) := run S (fields (score v S) d.anchor)

def compute {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) : ℕ :=
  let stored := table d v S
  scanThreshold stored budget

theorem scanThreshold_le {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    scanThreshold table budget ≤ S := by
  apply Finset.sup_le
  intro s _
  unfold acceptedScore
  split
  · omega
  · split <;> omega

theorem totalScore_le {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K)
    (labels : Fin m → Fin K) : totalScore v S labels ≤ S := by
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have hEach (j : Fin m) : (score v S j (labels j):ℝ) ≤ (S:ℝ)*v.values.weight j := by
    have hIndex : ((labels j).val+1:ℝ) ≤ (K:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (labels j).isLt)
    have hRatio := (div_le_one hk).mpr hIndex
    have hp : 0 ≤ (S:ℝ)*v.values.weight j := mul_nonneg (Nat.cast_nonneg _) (v.values.positive j).le
    have h := mul_le_mul_of_nonneg_left hRatio hp
    exact (score_bounds v S j (labels j)).1.trans (by simpa only [mul_one] using h)
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hEach j)
  rw [← Finset.mul_sum,v.values.normalized,mul_one] at hSum
  have hCast : (∑ j,(score v S j (labels j):ℝ))=(totalScore v S labels:ℝ) := by simp only [totalScore,Nat.cast_sum]
  rw [hCast] at hSum
  exact_mod_cast hSum

theorem compute_eq_reference {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (budget : ℚ) : compute d budget v S=threshold d budget v S := by
  have hb (s : Fin (S+1)) : Best (Fits (fields (score v S) d.anchor) s.val) ((table d v S).read s) :=
    run_best S _ s
  apply Nat.le_antisymm
  · change scanThreshold (table d v S) budget ≤ _
    apply Finset.sup_le
    intro s _
    cases he : (table d v S).read s with
    | none => simp only [acceptedScore,he]; exact Nat.zero_le _
    | some chosen =>
      by_cases hc : chosen.cost<budget
      · simp only [acceptedScore,he,ite_eq_left hc]
        have hh := hb s
        rw [he] at hh
        obtain ⟨labels,hs,hCost,_⟩ := tuple_of_fits (score v S) d.anchor s.val chosen hh.1
        change totalScore v S labels=s.val at hs
        change rationalCost d labels=chosen.cost at hCost
        have hMember : labels ∈ slackTuples d budget := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          rw [hCost]
          exact hc
        rw [← hs]
        exact Finset.le_sup hMember
      · simp only [acceptedScore,he,ite_eq_right hc]
        exact Nat.zero_le _
  · change (slackTuples d budget).sup (totalScore v S) ≤ scanThreshold (table d v S) budget
    apply Finset.sup_le
    intro labels hMember
    have hCost := (Finset.mem_filter.mp hMember).2
    have hCap := totalScore_le v S hK labels
    let s : Fin (S+1) := ⟨totalScore v S labels,by omega⟩
    let witness : Selection K := ⟨rationalCost d labels,List.ofFn labels⟩
    have hFits : Fits (fields (score v S) d.anchor) s.val witness := fits_of_tuple _ _ labels
    have hh := hb s
    cases he : (table d v S).read s with
    | none =>
      rw [he] at hh
      exact (hh witness hFits).elim
    | some chosen =>
      rw [he] at hh
      have hc : chosen.cost<budget := (hh.2 witness hFits).trans_lt hCost
      have hRoot : acceptedScore (table d v S) budget s ≤ scanThreshold (table d v S) budget :=
        Finset.le_sup (Finset.mem_univ s)
      simpa only [acceptedScore,he,ite_eq_left hc,s] using hRoot

theorem compute_le {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) :
    compute d budget v S ≤ S := scanThreshold_le _ _

theorem computed_lower {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hBalanced : Balanced d) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hOrder : ∀ j,Monotone (d.anchor j)) (hNonnegative : ∀ j l,0 ≤ d.anchor j l)
    (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) (budget : ℚ) (hBudget : 0<budget) :
    (compute d budget v S:ℝ)/(S:ℝ) ≤ security v.values (budget:ℝ) (law d hT).law := by
  rw [compute_eq_reference d v S hK]
  exact threshold_lower d hT hK hBalanced v S hS hOrder hNonnegative hZero budget hBudget

theorem computed_witness {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (budget : ℚ) (hBudget : 0<budget) (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) :
    ∃ chosen labels,
      (table d v S).read ⟨compute d budget v S,Nat.lt_succ_of_le (compute_le d budget v S)⟩=some chosen ∧
      rationalCost d labels<budget ∧ totalScore v S labels=compute d budget v S ∧
      rationalCost d labels=chosen.cost ∧ List.ofFn labels=chosen.labels := by
  obtain ⟨labels,hCost,hScore⟩ := threshold_attained d budget v S (slack_nonempty d hK budget hBudget hZero)
  rw [← compute_eq_reference d v S hK] at hScore
  let s : Fin (S+1) := ⟨compute d budget v S,Nat.lt_succ_of_le (compute_le d budget v S)⟩
  let witness : Selection K := ⟨rationalCost d labels,List.ofFn labels⟩
  have hFits : Fits (fields (score v S) d.anchor) s.val witness := by
    change Fits _ (compute d budget v S) _
    rw [hScore]
    exact fits_of_tuple _ _ labels
  have hBest : Best (Fits (fields (score v S) d.anchor) s.val) ((table d v S).read s) := run_best S _ s
  cases he : (table d v S).read s with
  | none => rw [he] at hBest; exact (hBest witness hFits).elim
  | some chosen =>
    rw [he] at hBest
    obtain ⟨out,hs,hc,hl⟩ := tuple_of_fits (score v S) d.anchor s.val chosen hBest.1
    change rationalCost d out=chosen.cost at hc
    refine ⟨chosen,out,rfl,?_,hs,hc,hl⟩
    rw [hc]
    exact (hBest.2 witness hFits).trans_lt hCost

end Blotto.GeneralPaperComputedThreshold

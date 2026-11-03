import Blotto.GeneralPaperPoorZeroGeometry

/-! Maximum tuple score and its executed arithmetic version. The runtime
computes m top-label scores with the bounded quotient, never enumerating
whole tuples or calling the reference floor primitive.
-/
namespace Blotto.GeneralPaperScoreMaximum
open GeneralPaperDictionary GeneralPaperStrictScore
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

def maximum {m : ℕ} (v : RationalFieldSelector m) (S : ℕ) : ℕ := ∑ j,⌊(S:ℚ)*v.weight j⌋₊

def topLabel (K : ℕ) (hK : 0<K) : Fin K := ⟨K-1,by omega⟩

theorem score_upper {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (j : Fin m) (l : Fin K) :
    score v S j l≤⌊(S:ℚ)*v.weight j⌋₊ := by
  unfold score
  apply Nat.floor_mono
  have hk : (0:ℚ)<K := by exact_mod_cast hK
  have hl : (l.val+1:ℚ)≤K := by exact_mod_cast Nat.succ_le_of_lt l.isLt
  have hh := mul_le_mul_of_nonneg_left ((div_le_one hk).mpr hl)
    (mul_nonneg (Nat.cast_nonneg S) (v.positive j).le)
  simpa only [mul_one] using hh

theorem score_top {m : ℕ} (v : RationalFieldSelector m) (S K : ℕ) (hK : 0<K) (j : Fin m) :
    score v S j (topLabel K hK)=⌊(S:ℚ)*v.weight j⌋₊ := by
  have hk : (K:ℚ)≠0 := by exact_mod_cast hK.ne'
  have hl : ((topLabel K hK).val+1:ℚ)=(K:ℚ) := by
    exact_mod_cast (show (topLabel K hK).val+1=K by change K-1+1=K; omega)
  unfold score
  rw [hl,div_self hk,mul_one]

theorem total_le {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (labels : Fin m → Fin K) :
    totalScore v S labels≤maximum v S :=
  Finset.sum_le_sum (fun j _ => score_upper v S hK j (labels j))

def run {m K : ℕ} (depth : ℕ) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) : ℕ :=
  ∑ j,(GeneralPaperScoreMatrixWork.scoreRun depth v S j (topLabel K hK)).1

theorem run_data {m K : ℕ} (depth : ℕ) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^depth) :
    run (K := K) depth v S hK=maximum v S := by
  simp only [run,GeneralPaperScoreMatrixWork.score_data depth v S hK hCap,score_top,maximum]

theorem all_slack_threshold {T m K : ℕ} (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K)
    (budget : ℚ) (hAll : ∀ labels : Fin m → Fin K,rationalCost d labels<budget) :
    threshold d budget v S=maximum v S := by
  apply le_antisymm
  · unfold threshold
    exact Finset.sup_le (fun labels _ => total_le v S hK labels)
  · have ht : (fun _ : Fin m => topLabel K hK)∈slackTuples d budget :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAll _⟩
    have hh : totalScore v S (fun _ : Fin m => topLabel K hK)≤threshold d budget v S := Finset.le_sup ht
    simpa only [totalScore,score_top,maximum] using hh

end Blotto.GeneralPaperScoreMaximum

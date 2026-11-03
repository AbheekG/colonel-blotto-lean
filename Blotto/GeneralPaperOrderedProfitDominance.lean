import Blotto.GeneralPaperOrderedProfitTreeBounds
import Blotto.GeneralPaperProfitMergeDomain

/-! The actual streamed balanced DP retains, for every actual subtree
tuple, a state with no larger resource tag and the selected multiplicative
profit factor. The positive-merge domain is proved before its rounding step.
-/
namespace Blotto.GeneralPaperOrderedProfitDominance
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperOrderedMinimum
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitRetention
open GeneralPaperProfitRetentionFactor GeneralPaperProfitRationalRound GeneralPaperOrderedProfitTreeBounds GeneralPaperProfitMergeDomain
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

theorem retained_dominance {K h : ℕ} (q w B H : ℕ) (tree : Tree R K h)
    (hQ : 0<q) (hWidth : 4*(H+1)≤w) (hExponent : 4*q≤2^B) :
    h≤H → BoundedProfit q tree → ∀ labels cost P, Realizes tree labels cost P →
      ∃ label chosen, (run (prepare q w B) tree).table.read label=some chosen ∧ chosen.cost≤cost ∧
        factor w^(h+1)*profit q P≤value q w B label := by
  have hW : 0<w := by omega
  have hFactor := factor_nonnegative w hW
  induction tree with
  | leaf field =>
    intro _ hBound labels cost P hRealizes
    obtain ⟨a,rfl,rfl,rfl⟩ := hRealizes
    obtain ⟨chosen,hRead,hCost⟩ := leaf_retained (prepare q w B) field a
    refine ⟨(GeneralPaperProfitGridRound.leaf (prepare q w B) (field.read a).1).label,chosen,hRead,hCost,?_⟩
    have hHigh := hBound [a] (field.read a).2 (field.read a).1 ⟨a,rfl,rfl,rfl⟩
    by_cases hZero : (field.read a).1=0
    · simpa only [hZero,profit,Nat.cast_zero,zero_div,mul_zero] using
        value_nonnegative q w B (GeneralPaperProfitGridRound.leaf (prepare q w B) 0).label
    · simpa only [Nat.zero_add,pow_one] using GeneralPaperProfitRationalRound.leaf_relative q w B (field.read a).1 hQ hW
        (positive_leaf_domain q B _ hExponent (by omega)) hHigh
  | @node h left right ihl ihr =>
    intro hHeight hBound labels cost P hRealizes
    obtain ⟨ll,lc,lp,rr,rc,rp,hl,hr,rfl,rfl,rfl⟩ := hRealizes
    have hLeft := left_bound left right hBound rr rc rp hr
    have hRight := right_bound left right hBound ll lc lp hl
    obtain ⟨i,a,ha,hca,hpa⟩ := ihl (by omega) hLeft ll lc lp hl
    obtain ⟨j,b,hb,hcb,hpb⟩ := ihr (by omega) hRight rr rc rp hr
    let S := (prepare q w B).numerators.read i+(prepare q w B).numerators.read j
    have hSum : factor w^(h+1)*profit q (lp+rp)≤(S:ℚ)/(denominator w B:ℚ) := by
      calc
        _ = factor w^(h+1)*profit q lp+factor w^(h+1)*profit q rp := by rw [profit_add]; ring
        _ ≤ value q w B i+value q w B j := add_le_add hpa hpb
        _ = _ := (sum_values q w B i j).symm
    have hUpper : S≤2*denominator w B := pair_sum_bound left right hQ hBound i j a b ha hb
    obtain ⟨chosen,hRead,hCost⟩ := merge_retained (prepare q w B)
      (run (prepare q w B) left).table (run (prepare q w B) right).table i j a b ha hb
    refine ⟨(GeneralPaperProfitGridRound.merge (prepare q w B) S).label,chosen,hRead,hCost.trans (add_le_add hca hcb),?_⟩
    by_cases hZero : lp+rp=0
    · simpa only [hZero,profit,Nat.cast_zero,zero_div,mul_zero] using
        value_nonnegative q w B (GeneralPaperProfitGridRound.merge (prepare q w B) S).label
    · have hLower := positive_merge_domain q w B H (h+1) (lp+rp) S hQ hWidth hExponent (by omega) (by omega) hSum
      have hRound := GeneralPaperProfitRationalRound.merge_relative q w B S hW hLower hUpper
      calc
        _ = factor w*(factor w^(h+1)*profit q (lp+rp)) := by rw [pow_succ]; ring
        _ ≤ factor w*((S:ℚ)/(denominator w B:ℚ)) := mul_le_mul_of_nonneg_left hSum hFactor
        _ ≤ _ := hRound

end Blotto.GeneralPaperOrderedProfitDominance

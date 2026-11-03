import Blotto.GeneralPaperOrderedProfitDominance

/-! The actual highest-feasible root and predecessor reconstruction achieve
the selected balanced-grid approximation. This proves the optimizer contract
on actual nonnegative fixed-denominator input profits and exact resource tags;
the source's physical catalogue and full cost model must still instantiate it.
-/
namespace Blotto.GeneralPaperOrderedProfitApproximation
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperOrderedMinimum
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitRetention
open GeneralPaperProfitRetentionFactor GeneralPaperProfitRationalRound GeneralPaperOrderedProfitTreeBounds GeneralPaperOrderedProfitDominance
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

theorem solve_selected {K h q w B : ℕ} (tree : Tree R K h) (budget : R)
    (label : Fin (prepare q w B).size) (output : List (Fin K))
    (hSolve : GeneralPaperOrderedProfitRoot.solve (prepare q w B) tree budget=some (label,output)) :
    GeneralPaperOrderedProfitRoot.select (run (prepare q w B) tree).table budget=some label := by
  cases hs : GeneralPaperOrderedProfitRoot.select (run (prepare q w B) tree).table budget with
  | none => simp [GeneralPaperOrderedProfitRoot.solve,hs] at hSolve
  | some chosen =>
    cases hd : decode (run (prepare q w B) tree) chosen with
    | none => simp [GeneralPaperOrderedProfitRoot.solve,hs,hd] at hSolve
    | some labels =>
      have he : (chosen,labels)=(label,output) := by
        simpa only [GeneralPaperOrderedProfitRoot.solve,hs,hd,Option.map_some,Option.some.injEq] using hSolve
      have hl := congrArg Prod.fst he
      simpa only [hs] using congrArg (fun i => some i) hl

theorem selected_relative {K h q w B : ℕ} (tree : Tree R K h) (budget : R)
    (hQ : 0<q) (hWidth : 4*(h+1)≤w) (hExponent : 4*q≤2^B) (hBound : BoundedProfit q tree)
    (label : Fin (prepare q w B).size)
    (hSelect : GeneralPaperOrderedProfitRoot.select (run (prepare q w B) tree).table budget=some label)
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes tree labels cost P) (hBudget : cost≤budget) :
    factor w^(h+1)*profit q P≤value q w B label := by
  obtain ⟨i,chosen,hRead,hCost,hProfit⟩ := retained_dominance q w B h tree hQ hWidth hExponent le_rfl hBound labels cost P hRealizes
  have hi := GeneralPaperOrderedProfitRoot.select_maximal _ budget label hSelect i ⟨chosen,hRead,hCost.trans hBudget⟩
  exact hProfit.trans (value_mono q w B i label hi)

theorem solve_relative {K h q w B : ℕ} (tree : Tree R K h) (budget : R)
    (hQ : 0<q) (hWidth : 4*(h+1)≤w) (hExponent : 4*q≤2^B) (hBound : BoundedProfit q tree)
    (label : Fin (prepare q w B).size) (output : List (Fin K))
    (hSolve : GeneralPaperOrderedProfitRoot.solve (prepare q w B) tree budget=some (label,output))
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes tree labels cost P) (hBudget : cost≤budget) :
    ∃ outCost outProfit, Realizes tree output outCost outProfit ∧ outCost≤budget ∧
      factor w^(h+1)*profit q P≤profit q outProfit := by
  obtain ⟨outCost,outProfit,hOut,hCost,hCross⟩ := GeneralPaperOrderedProfitRoot.solve_sound tree budget label output hSolve
  have he := selected_relative tree budget hQ hWidth hExponent hBound label (solve_selected tree budget label output hSolve)
    labels cost P hRealizes hBudget
  exact ⟨outCost,outProfit,hOut,hCost,he.trans (cross_value_le_profit q w B outProfit hQ (by omega) label hCross)⟩

theorem additive_from_relative (q w h P outP : ℕ) (hQ : 0<q) (hW : 0<w) (hP : P≤2*q)
    (hRelative : factor w^(h+1)*profit q P≤profit q outP) :
    profit q P-profit q outP≤2*((h+1:ℕ):ℚ)/(w:ℚ) := by
  have hq : (0:ℚ)<q := by exact_mod_cast hQ
  have hTwo : profit q P≤2 := by
    unfold profit
    apply (div_le_iff₀ hq).mpr
    exact_mod_cast hP
  have hg := factor_power_gap w (h+1) hW
  have hm := mul_le_mul_of_nonneg_right hg (profit_nonnegative q P)
  have hf : (0:ℚ)≤((h+1:ℕ):ℚ)/(w:ℚ) := by positivity
  have ht := mul_le_mul_of_nonneg_left hTwo hf
  calc
    _ ≤ (((h+1:ℕ):ℚ)/(w:ℚ))*2 := by nlinarith only [hm,hRelative,ht]
    _ = _ := by ring

theorem accuracy_half (w h : ℕ) (alpha : ℚ) (hW : 0<w) (hAccuracy : 4*((h+1:ℕ):ℚ)≤alpha*w) :
    2*((h+1:ℕ):ℚ)/(w:ℚ)≤alpha/2 := by
  have hw : (0:ℚ)<w := by exact_mod_cast hW
  apply (div_le_iff₀ hw).mpr
  linarith only [hAccuracy]

theorem optimizer_guarantee {K h q w B : ℕ} (tree : Tree R K h) (budget : R) (alpha : ℚ)
    (hQ : 0<q) (hWidth : 4*(h+1)≤w) (hExponent : 4*q≤2^B) (hBound : BoundedProfit q tree)
    (hAccuracy : 4*((h+1:ℕ):ℚ)≤alpha*w)
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes tree labels cost P) (hBudget : cost≤budget) :
    ∃ label output outCost outProfit,
      GeneralPaperOrderedProfitRoot.solve (prepare q w B) tree budget=some (label,output) ∧
      Realizes tree output outCost outProfit ∧ outCost≤budget ∧ profit q P-profit q outProfit≤alpha/2 := by
  obtain ⟨label,output,hSolve⟩ := feasible_success tree labels cost budget P hRealizes hBudget
  obtain ⟨outCost,outProfit,hOut,hCost,hRel⟩ := solve_relative tree budget hQ hWidth hExponent hBound label output hSolve labels cost P hRealizes hBudget
  have hW : 0<w := by omega
  exact ⟨label,output,outCost,outProfit,hSolve,hOut,hCost,
    (additive_from_relative q w h P outProfit hQ hW (hBound labels cost P hRealizes) hRel).trans
      (accuracy_half w h alpha hW hAccuracy)⟩

end Blotto.GeneralPaperOrderedProfitApproximation

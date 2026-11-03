import Blotto.GeneralPaperPaddedProfitRows

/-! The executed prepared optimizer returns a sized row for exactly the real
fields. Its approximation compares with every complete budget-feasible row,
with no tree-realization witness assumed of that comparator. Zero padding is
an internal implementation detail and contributes no resource or true profit.
-/
namespace Blotto.GeneralPaperOrderedRowOptimizer
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBounds
open GeneralPaperOrderedProfitTreeBuild GeneralPaperOrderedProfitRows GeneralPaperPaddedProfitRows
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

def resource {K : ℕ} (input : List (WeightedField R K)) (row : FixedArrayTable input.length (Fin K)) : R :=
  (resources (input.map Prod.fst) (List.ofFn row.read)).sum

def trueProfit {K : ℕ} (input : List (WeightedField R K)) (row : FixedArrayTable input.length (Fin K)) : ℕ :=
  (profits (input.map Prod.fst) (List.ofFn row.read)).sum

def tree {K : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (input : List (WeightedField R K)) :
    Tree R K prepared.parameters.height := build prepared.parameters.height (pad prepared.parameters.height input)

def optimize {K : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (input : List (WeightedField R K)) (budget : R) :
    Option (FixedArrayTable input.length (Fin K)) :=
  (GeneralPaperOrderedProfitRoot.solve prepared.grid (tree prepared input) budget).bind
    (fun result => GeneralPaperRowPrefix.trim input.length result.2)

theorem selected_guarantee {K : ℕ} (m lambda k Qv : ℕ) (hQv : 0<Qv) (hK : 0<K)
    (input : List (WeightedField R K)) (hFields : input.length≤m) (budget : R)
    (hBound : BoundedProfit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
      (tree (GeneralPaperProfitParameters.prepare m lambda k Qv) input))
    (comparator : FixedArrayTable input.length (Fin K)) (hBudget : resource input comparator≤budget) :
    ∃ output, optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) input budget=some output ∧
      resource input output≤budget ∧
      GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf (trueProfit input comparator)-
        GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf (trueProfit input output)≤
          (GeneralPaperSourceParameters.prepare k).eta/2 := by
  let height := (GeneralPaperProfitParameters.parameters m lambda k Qv).height
  have hFit : input.length≤2^height := by
    have he := GeneralPaperProfitParameters.covers_fields m lambda k Qv
    rw [GeneralPaperProfitParameters.leaf_count_spec] at he
    exact hFields.trans he
  let labels := List.ofFn comparator.read++List.replicate (2^height-input.length) (⟨0,hK⟩:Fin K)
  have hLength : labels.length=2^height := by
    simp only [labels,List.length_append,List.length_ofFn,List.length_replicate]
    omega
  have hTake : labels.take input.length=List.ofFn comparator.read := by
    simpa only [List.length_ofFn] using (List.take_left (l₁ := List.ofFn comparator.read) (l₂ := List.replicate (2^height-input.length) (⟨0,hK⟩:Fin K)))
  obtain ⟨cost,P,hRealizes⟩ := realizes_complete (tree (GeneralPaperProfitParameters.prepare m lambda k Qv) input) labels hLength
  obtain ⟨hc,hp⟩ := realizes_trim height input hFit labels cost P hRealizes
  rw [hTake] at hc hp
  have hCompCost : resource input comparator=cost := hc
  have hCompProfit : trueProfit input comparator=P := hp
  obtain ⟨label,chosen,outCost,outProfit,hSolve,hOut,hCost,hProfit⟩ :=
    GeneralPaperOrderedSelectedProfitGuarantee.selected_guarantee m lambda k Qv hQv
      (tree (GeneralPaperProfitParameters.prepare m lambda k Qv) input) budget hBound labels cost P hRealizes
      (by rw [←hCompCost]; exact hBudget)
  have hOutputLength := realizes_length _ chosen outCost outProfit hOut
  obtain ⟨output,hTrim⟩ := GeneralPaperRowPrefix.trim_success input.length chosen (by rw [hOutputLength]; exact hFit)
  obtain ⟨hOutputCost,hOutputProfit⟩ := realizes_trim height input hFit chosen outCost outProfit hOut
  have hRowCost : resource input output=outCost := by
    dsimp only [resource]
    rw [GeneralPaperRowPrefix.trim_ofFn _ _ _ hTrim]
    exact hOutputCost
  have hRowProfit : trueProfit input output=outProfit := by
    dsimp only [trueProfit]
    rw [GeneralPaperRowPrefix.trim_ofFn _ _ _ hTrim]
    exact hOutputProfit
  refine ⟨output,?_,?_,?_⟩
  · change GeneralPaperOrderedProfitRoot.solve _ _ _=some (label,chosen) at hSolve
    simp only [optimize,hSolve,Option.bind_some]
    exact hTrim
  · rw [hRowCost]
    exact hCost
  · rw [hCompProfit,hRowProfit]
    exact hProfit

end Blotto.GeneralPaperOrderedRowOptimizer

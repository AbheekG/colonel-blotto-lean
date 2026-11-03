import Blotto.GeneralPaperSelectedSortStorage

/-! The internal selected sort of the actual native crossing pipeline.
Filtering supplies its literal input; original pair/budget batches derive
the bounds. Filter/deduplication frames and parent owners are separate. -/
namespace Blotto.GeneralPaperCrossingSortStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 2800000

def window (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let filtered := GeneralPaperPricedCrossingPasses.filterRun model.rat W lo hi points
  GeneralPaperSelectedSortStorage.window model W rationalWordWidth
    (GeneralPaperPricedCrossingPasses.leRun model.rat) (lo::hi::filtered.1)

def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperSelectedSortStorage.profile model W (1+2*R) (model.rat (1+2*R)) (n+2)

theorem bounded (model : RationalCostModel) (W n R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ q∈points,RationalHeight q R) : window model W lo hi points≤profile model W n R := by
  let filtered := GeneralPaperPricedCrossingPasses.filterRun model.rat W lo hi points
  let input := lo::hi::filtered.1
  have hLen : input.length≤n+2 := by
    have hf := List.length_filter_le (fun t => decide (lo≤t ∧ t≤hi)) points
    dsimp only [input,filtered]
    rw [GeneralPaperPricedCrossingPasses.filter_data]
    simp only [List.length_cons]
    omega
  have hInput : ∀ q∈input,rationalWordWidth q≤1+2*R := by
    intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · rw [he]; exact rationalWordWidth_of_height hl
    · rcases List.mem_cons.mp hq with he|hq
      · rw [he]; exact rationalWordWidth_of_height hh
      · have hFilter : q∈points.filter (fun t => decide (lo≤t ∧ t≤hi)) := by
          simpa only [filtered,GeneralPaperPricedCrossingPasses.filter_data] using hq
        exact rationalWordWidth_of_height (hp q (List.mem_filter.mp hFilter).1)
  exact GeneralPaperSelectedSortStorage.bounded model W (1+2*R) (model.rat (1+2*R)) (n+2)
    rationalWordWidth (GeneralPaperPricedCrossingPasses.leRun model.rat) input hLen hInput
    (fun a ha b hb => GeneralPaperPricedCrossingPasses.le_work model.rat model.monotone a b (1+2*R) (hInput a ha) (hInput b hb))

theorem stage_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    window model W lo hi (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1≤
      profile model W ((S+1)*(K*K)) (width D E m X V P) := by
  have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1.length≤(S+1)*(K*K) := by
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  apply bounded model W _ _ lo hi _ hLen hl hh
  intro q hq
  rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
  exact GeneralPaperRayUniformSize.stage_roots hD hE hn field previous hf hp q hq

theorem budget_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : GeneralPaperRayAffineScoreStep.Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table)
    (h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    window model W lo hi (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1≤
      profile model W (S+1) (width D E m X V P) := by
  have hLen : (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1.length≤S+1 := by
    rw [GeneralPaperBudgetCrossingPrice.data]
    exact GeneralPaperRayBudgetCrossings.batch_length table h beta
  apply bounded model W _ _ lo hi _ hLen hl hh
  intro q hq
  rw [GeneralPaperBudgetCrossingPrice.data] at hq
  exact GeneralPaperRayUniformSize.budget_roots hD hE hn table hp h beta hb q hq

end Blotto.GeneralPaperCrossingSortStorage

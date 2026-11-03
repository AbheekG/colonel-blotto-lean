import Blotto.GeneralPaperMeasuredLeafRecordLifetime

/-! Complete actual Boolean-cache measurement: denominator words,
variable-length labelled rows, empty-payload ruler cells and the enclosing
record joins. Native samplers in both bits modes derive positivity and
capacity internally. The borrowed prepared cache belongs to the enclosing
source owner; this is the measurement pass, not cache creation. -/
namespace Blotto.GeneralPaperMeasuredBooleanPlanLifetime
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredRecordPlanLifetime
open GeneralPaperMeasuredLeafRecordLifetime
open GeneralPaperEqualMeasuredLeafPlans
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def window {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) : ℕ :=
  sequenceWindow S A [(word model S A c.denominator,wordWindow model S A c.denominator),
    (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (row model S A) c.rows,
      GeneralPaperMeasuredListPlanLifetime.window model S A 2 32 (row model S A) (rowWindow model S A) c.rows),
    (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (unit S) c.ruler,
      GeneralPaperMeasuredListPlanLifetime.window model S A 2 32 (unit S) (fun x => constantWindow S (unit S x)) c.ruler),
    (reserve model S A 64,referencesWindow model S A 0 0 64)]

theorem good {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) (hA : 0 < A) :
    Good model S A 690 (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A c) (window model S A c) := by
  have hRows := GeneralPaperMeasuredListPlanLifetime.run_good model S A 140 2 32 (row model S A)
    (rowWindow model S A) c.rows hA (by decide) (by decide) (by decide) (by decide)
    (fun x _ => row_good model S A x hA)
  have hRuler := GeneralPaperMeasuredListPlanLifetime.run_good model S A 2 2 32 (unit S)
    (fun x => constantWindow S (unit S x)) c.ruler hA (by decide) (by decide) (by decide) (by decide)
    (fun _ _ => empty_good model S A hA)
  have h := sequence_good model S A 164
    [(word model S A c.denominator,wordWindow model S A c.denominator),
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (row model S A) c.rows,
        GeneralPaperMeasuredListPlanLifetime.window model S A 2 32 (row model S A) (rowWindow model S A) c.rows),
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (unit S) c.ruler,
        GeneralPaperMeasuredListPlanLifetime.window model S A 2 32 (unit S) (fun x => constantWindow S (unit S x)) c.ruler),
      (reserve model S A 64,referencesWindow model S A 0 0 64)] hA (by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact mono model S A 38 164 _ _ (word_good model S A c.denominator hA) (by decide)
    · exact hRows
    · exact mono model S A 26 164 _ _ hRuler (by decide)
    · exact mono model S A 4 164 _ _ (reserve_good model S A 64 hA (by decide) (by decide)) (by decide))
  simpa only [GeneralPaperEqualMeasuredRetainedPlan.boolean,window,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

def bound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) : ℕ :=
  ((GeneralPaperEqualMeasuredRetainedPlan.boolean model S A c).sizes.sum + 1) * 690 *
    GeneralPaperMeasuredPlanLifetimeAlgebra.unit model S A (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A c).work

theorem window_bound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) (hA : 0 < A)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A c).sizes.sum < 2 ^ A) :
    window model S A c ≤ bound model S A c := (good model S A c hA).2 _ hCap le_rfl

theorem sampler_area {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source.categorical).sizes.sum ≤
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum := by
  simp only [GeneralPaperEqualMeasuredRetainedPlan.sampler,GeneralPaperMeasuredBlockPlan.sequence_sum,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem native_grouped {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    window model S source.address source.categorical ≤ bound model S source.address source.categorical := by
  dsimp only
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact window_bound model S _ _ hA ((sampler_area model S _ _).trans_lt hCap)

end Blotto.GeneralPaperMeasuredBooleanPlanLifetime

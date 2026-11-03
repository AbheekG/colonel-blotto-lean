import Blotto.GeneralPaperMeasuredArrayPlanLifetime

/-! Complete actual nested matrix, segment, prepared-cache and sampler
measurement lifetimes. All array/list/record children discharge their
conditions from actual source fields; original precision stays additive.
These are observers of measurement, not recomputation of source caches. -/
namespace Blotto.GeneralPaperMeasuredRetainedPlanLifetime
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredRecordPlanLifetime
open GeneralPaperMeasuredLeafRecordLifetime
open GeneralPaperEqualMeasuredLeafPlans
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def matrixWindow {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedArrayTable r (FixedArrayTable m ℚ)) : ℕ :=
  GeneralPaperMeasuredArrayPlanLifetime.window model S A
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S))
    (GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rationalWindow model S)) x

theorem matrix_good {m r : ℕ} (model : RationalCostModel) (S A : ℕ)
    (x : FixedArrayTable r (FixedArrayTable m ℚ)) (hA : 0 < A) :
    Good model S A 68 (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x) (matrixWindow model S A x) := by
  apply GeneralPaperMeasuredArrayPlanLifetime.good model S A 36 _ _ x hA
  intro i
  exact GeneralPaperMeasuredArrayPlanLifetime.good model S A 4 _ _ (x.read i) hA
    (fun j => rational_good model S A ((x.read i).read j) hA)

def segmentsWindow {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : PreparedSegmentDescriptor l) : ℕ :=
  sequenceWindow S A [
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) x.weights,GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rationalWindow model S) x.weights),
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x.left,matrixWindow model S A x.left),
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x.right,matrixWindow model S A x.right),
    (reserve model S A 32,referencesWindow model S A 0 0 32)]

theorem segments_good {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : PreparedSegmentDescriptor l) (hA : 0 < A) :
    Good model S A 306 (GeneralPaperEqualMeasuredRetainedPlan.segments model S A x) (segmentsWindow model S A x) := by
  have h := sequence_good model S A 68 [
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) x.weights,GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rationalWindow model S) x.weights),
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x.left,matrixWindow model S A x.left),
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A x.right,matrixWindow model S A x.right),
    (reserve model S A 32,referencesWindow model S A 0 0 32)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · exact mono model S A 36 68 _ _ (GeneralPaperMeasuredArrayPlanLifetime.good model S A 4 _ _ x.weights hA (fun j => rational_good model S A (x.weights.read j) hA)) (by decide)
    · exact matrix_good model S A x.left hA
    · exact matrix_good model S A x.right hA
    · exact mono model S A 4 68 _ _ (reserve_good model S A 32 hA (by decide) (by decide)) (by decide)
    )
  simpa only [GeneralPaperEqualMeasuredRetainedPlan.segments,segmentsWindow,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

def preparedWindow {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  sequenceWindow S A [
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (route model S A) x.routes.table,GeneralPaperMeasuredArrayPlanLifetime.window model S A (route model S A) (routeWindow model S A) x.routes.table),
    (GeneralPaperEqualMeasuredRetainedPlan.segments model S A x.segments,segmentsWindow model S A x.segments),
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) x.counts,GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) x.counts),
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) [x.D,x.rangeBits,x.midpointBits,x.midpointCount],GeneralPaperMeasuredListPlanLifetime.window model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) [x.D,x.rangeBits,x.midpointBits,x.midpointCount]),
    (GeneralPaperMeasuredBlockPlan.rational model S x.budget,rationalWindow model S x.budget),
    (reserve model S A 64,referencesWindow model S A 0 0 64)]

theorem prepared_good {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A) :
    Good model S A 1886 (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A x) (preparedWindow model S A x) := by
  have h := sequence_good model S A 306 [
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (route model S A) x.routes.table,GeneralPaperMeasuredArrayPlanLifetime.window model S A (route model S A) (routeWindow model S A) x.routes.table),
    (GeneralPaperEqualMeasuredRetainedPlan.segments model S A x.segments,segmentsWindow model S A x.segments),
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) x.counts,GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) x.counts),
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) [x.D,x.rangeBits,x.midpointBits,x.midpointCount],GeneralPaperMeasuredListPlanLifetime.window model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) [x.D,x.rangeBits,x.midpointBits,x.midpointCount]),
    (GeneralPaperMeasuredBlockPlan.rational model S x.budget,rationalWindow model S x.budget),
    (reserve model S A 64,referencesWindow model S A 0 0 64)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
    · exact mono model S A 82 306 _ _ (GeneralPaperMeasuredArrayPlanLifetime.good model S A 50 _ _ x.routes.table hA (fun j => route_good model S A (x.routes.table.read j) hA)) (by decide)
    · exact segments_good model S A x.segments hA
    · exact mono model S A 36 306 _ _ (GeneralPaperMeasuredArrayPlanLifetime.good model S A 4 _ _ x.counts hA (fun j => natural_good model S A (x.counts.read j) hA)) (by decide)
    · exact mono model S A 28 306 _ _ (GeneralPaperMeasuredListPlanLifetime.run_good model S A 4 1 32 _ _ _ hA (by decide) (by decide) (by decide) (by decide) (fun value _ => natural_good model S A value hA)) (by decide)
    · exact mono model S A 4 306 _ _ (rational_good model S A x.budget hA) (by decide)
    · exact mono model S A 4 306 _ _ (reserve_good model S A 64 hA (by decide) (by decide)) (by decide)
    )
  simpa only [GeneralPaperEqualMeasuredRetainedPlan.prepared,preparedWindow,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

def samplerWindow {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  sequenceWindow S A [
    (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A x.prepared,preparedWindow model S A x.prepared),
    (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A x.categorical,GeneralPaperMeasuredBooleanPlanLifetime.window model S A x.categorical),
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) [x.exponent,x.address],GeneralPaperMeasuredListPlanLifetime.window model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) [x.exponent,x.address]),
    (reserve model S A 64,referencesWindow model S A 0 0 64)]

theorem sampler_good {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < A) :
    Good model S A 7578 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A x) (samplerWindow model S A x) := by
  have h := sequence_good model S A 1886 [
    (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A x.prepared,preparedWindow model S A x.prepared),
    (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A x.categorical,GeneralPaperMeasuredBooleanPlanLifetime.window model S A x.categorical),
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) [x.exponent,x.address],GeneralPaperMeasuredListPlanLifetime.window model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) [x.exponent,x.address]),
    (reserve model S A 64,referencesWindow model S A 0 0 64)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · exact prepared_good model S A x.prepared hA
    · exact mono model S A 690 1886 _ _ (GeneralPaperMeasuredBooleanPlanLifetime.good model S A x.categorical hA) (by decide)
    · exact mono model S A 28 1886 _ _ (GeneralPaperMeasuredListPlanLifetime.run_good model S A 4 1 32 _ _ _ hA (by decide) (by decide) (by decide) (by decide) (fun value _ => natural_good model S A value hA)) (by decide)
    · exact mono model S A 4 1886 _ _ (reserve_good model S A 64 hA (by decide) (by decide)) (by decide)
    )
  simpa only [GeneralPaperEqualMeasuredRetainedPlan.sampler,samplerWindow,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

def samplerBound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (x : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S A x).sizes.sum + 1) * 7578 *
    GeneralPaperMeasuredPlanLifetimeAlgebra.unit model S A (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A x).work

theorem native_grouped {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    samplerWindow model S source.address source ≤ samplerBound model S source.address source := by
  dsimp only
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact (sampler_good model S _ _ hA).2 _ hCap le_rfl

end Blotto.GeneralPaperMeasuredRetainedPlanLifetime

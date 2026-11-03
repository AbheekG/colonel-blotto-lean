import Blotto.GeneralPaperEqualMeasuredLeafPlans

/-! Complete executed field-size plans of the retained grouped sampler.
Every rational/natural/list length is measured from its actual stored field.
Exact sums identify all array/list/record reference headers and payloads with
the previously checked complete encoded ownership; no cache is recomputed. -/
namespace Blotto.GeneralPaperEqualMeasuredRetainedPlan
open GeneralPaperMeasuredBlockPlan GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def matrix {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedArrayTable r (FixedArrayTable m ℚ)) : Plan :=
  GeneralPaperMeasuredArrayBlockPlan.array model S A
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (rational model S)) x

theorem matrix_sum {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (matrix model S A x).sizes.sum = arrayFootprint A (arrayFootprint A rationalWordWidth) x := by
  apply GeneralPaperMeasuredArrayBlockPlan.array_sum
  intro i
  apply GeneralPaperMeasuredArrayBlockPlan.array_sum
  intro j
  rw [rational_data]
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]

def segments {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (x : PreparedSegmentDescriptor l) : Plan :=
  sequence S [GeneralPaperMeasuredArrayBlockPlan.array model S A (rational model S) x.weights,
    matrix model S A x.left,matrix model S A x.right,reserve model S A 32]

theorem segments_sum {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (x : PreparedSegmentDescriptor l) : (segments model S A x).sizes.sum = segmentFoot A x := by
  have hw := GeneralPaperMeasuredArrayBlockPlan.array_sum model S A (rational model S) rationalWordWidth x.weights
    (by intro i; rw [rational_data]; simp only [List.sum_cons,List.sum_nil,Nat.add_zero])
  simp only [segments,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hw,matrix_sum,reserve_sum,Nat.add_zero]
  unfold segmentFoot
  omega

def prepared {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l) : Plan :=
  sequence S [GeneralPaperMeasuredArrayBlockPlan.array model S A (route model S A) p.routes.table,
    segments model S A p.segments,
    GeneralPaperMeasuredArrayBlockPlan.array model S A (natural model S) p.counts,
    GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (natural model S) [p.D,p.rangeBits,p.midpointBits,p.midpointCount],
    rational model S p.budget,reserve model S A 64]

theorem prepared_sum {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l) :
    (prepared model S A p).sizes.sum = preparedFoot A p := by
  have hr := GeneralPaperMeasuredArrayBlockPlan.array_sum model S A (route model S A) (routeFoot A) p.routes.table
    (fun i => route_sum model S A _)
  have hc := GeneralPaperMeasuredArrayBlockPlan.array_sum model S A (natural model S) natBits p.counts
    (by intro i; rw [natural_data]; simp only [List.sum_cons,List.sum_nil,Nat.add_zero])
  simp only [prepared,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hr,hc,segments_sum,
    GeneralPaperMeasuredListBlockPlan.fields_sum,rational_data,reserve_sum,Nat.add_zero]
  unfold preparedFoot
  omega

def boolean {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) : Plan :=
  sequence S [word model S A c.denominator,
    GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (row model S A) c.rows,
    GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (unit S) c.ruler,reserve model S A 64]

theorem boolean_sum {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (S A : ℕ)
    (c : GeneralPaperEqualBooleanCache.Cache p) : (boolean model S A c).sizes.sum = cacheFoot A c := by
  have hr := GeneralPaperMeasuredListBlockPlan.linked_sum model S A (row model S A)
    (fun x => natBits x.1.val + wordFoot A x.2 + 16 * A) c.rows (fun x _ => row_sum model S A x)
  have hu := GeneralPaperMeasuredListBlockPlan.linked_sum model S A (unit S) (fun _ : Unit => 0) c.ruler
    (by intro x _; rfl)
  simp only [boolean,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,word_sum,hr,hu,reserve_sum,Nat.add_zero]
  unfold cacheFoot
  omega

def sampler {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (a : GeneralPaperEqualStoredBitSampler.Sampler G l) : Plan :=
  sequence S [prepared model S A a.prepared,boolean model S A a.categorical,
    GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (natural model S) [a.exponent,a.address],reserve model S A 64]

theorem sampler_sum {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A : ℕ) (a : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    (sampler model S A a).sizes.sum = GeneralPaperEqualRetainedStorage.footprint A a := by
  simp only [sampler,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,prepared_sum,boolean_sum,
    GeneralPaperMeasuredListBlockPlan.fields_sum,reserve_sum,Nat.add_zero]
  unfold GeneralPaperEqualRetainedStorage.footprint
  omega

end Blotto.GeneralPaperEqualMeasuredRetainedPlan

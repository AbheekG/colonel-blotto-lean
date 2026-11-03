import Blotto.GeneralPaperSignedTailEpochError

/-! Prepare strict and weak CDF query ranks at a and a+1. Both counts are
rounded separately and read the same unsigned-block prefix total.
-/
namespace Blotto.GeneralPaperCDFPairPlan
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def shiftCuts {m : ℕ} (shift : ℕ) (queries : FixedArrayTable m ℕ) : FixedArrayTable m ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun q => (queries.read q+shift,12))

theorem shift_read {m : ℕ} (shift : ℕ) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (shiftCuts shift queries).1.read q=queries.read q+shift := by
  rw [shiftCuts,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem shift_work {m : ℕ} (shift : ℕ) (queries : FixedArrayTable m ℕ) : (shiftCuts shift queries).2=54*m+18 := by
  rw [shiftCuts,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

structure Plan (k m : ℕ) where
  lower : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
  upper : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
  work : ℕ

def prepare {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) : Plan k m :=
  let lowerCuts := shiftCuts 0 queries
  let upperCuts := shiftCuts 1 queries
  let lower := GeneralPaperRankCache.build k summary lowerCuts.1
  let upper := GeneralPaperRankCache.build k summary upperCuts.1
  ⟨lower.1,upper.1,lowerCuts.2+upperCuts.2+lower.2+upper.2+16⟩

structure Pair where
  lower : ℕ
  upper : ℕ
  work : ℕ

def evaluate {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : Pair :=
  let lower := GeneralPaperRankedCDFQuery.cached k preparedPrefix plan.lower q
  let upper := GeneralPaperRankedCDFQuery.cached k preparedPrefix plan.upper q
  ⟨lower.quotient,upper.quotient,lower.work+upper.work+8⟩

theorem evaluate_lower {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k preparedPrefix (prepare k summary queries) q).lower=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (queries.read q) := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedCDFQuery.cached_count,shift_read,Nat.add_zero]

theorem evaluate_upper {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k preparedPrefix (prepare k summary queries) q).upper=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (queries.read q+1) := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedCDFQuery.cached_count,shift_read]

theorem evaluate_bounds {m : ℕ} (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k (GeneralPaperEpochPrefixArray.build values) (prepare k summary queries) q).lower≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
    (evaluate k (GeneralPaperEpochPrefixArray.build values) (prepare k summary queries) q).upper≤(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [evaluate_lower,evaluate_upper]
  exact ⟨GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _,GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _⟩

theorem prepare_work {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) : (prepare k summary queries).work≤2*m*((35+k)*(12*(35+k)+34)+120)+88 := by
  have hl := GeneralPaperRankCache.build_work k summary (shiftCuts 0 queries).1
  have hu := GeneralPaperRankCache.build_work k summary (shiftCuts 1 queries).1
  change (shiftCuts 0 queries).2+(shiftCuts 1 queries).2+_+_+16≤_
  rw [shift_work,shift_work]
  nlinarith

theorem evaluate_work {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : (evaluate k preparedPrefix plan q).work=24*(30+k)+92 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperRankedCDFQuery.cached_work,GeneralPaperRankedCDFQuery.cached_work]
  omega

end Blotto.GeneralPaperCDFPairPlan

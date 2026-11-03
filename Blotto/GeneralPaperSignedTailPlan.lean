import Blotto.GeneralPaperOrderedIntervals

/-! Prepare two native rank tables for per-sign tail intervals. The
positive cuts are a,U and the negative cuts U+a,2*U. Both are evaluated
against the same complete signed-block prefix array and denominator.
-/
namespace Blotto.GeneralPaperSignedTailPlan
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def cutValue {m : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) (i : Fin (m+1)) : ℕ :=
  if h : i.val<m then
    let a := queries.read ⟨i.val,h⟩
    if negative then U+a else a
  else if negative then 2*U else U

def cutBuild {m : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) : FixedArrayTable (m+1) ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (cutValue U negative queries i,12))

theorem positive_low {m : ℕ} (U : ℕ) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (cutBuild U false queries).1.read q.castSucc=queries.read q := by
  rw [cutBuild,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp only [cutValue,Fin.val_castSucc,q.isLt,dif_pos,Bool.false_eq_true,ite_false]

theorem positive_high {m : ℕ} (U : ℕ) (queries : FixedArrayTable m ℕ) :
    (cutBuild U false queries).1.read (Fin.last m)=U := by
  rw [cutBuild,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp only [cutValue,Fin.val_last,lt_self_iff_false,dif_neg,Bool.false_eq_true,ite_false,not_false_eq_true]

theorem negative_low {m : ℕ} (U : ℕ) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (cutBuild U true queries).1.read q.castSucc=U+queries.read q := by
  rw [cutBuild,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp only [cutValue,Fin.val_castSucc,q.isLt,dif_pos,ite_true]

theorem negative_high {m : ℕ} (U : ℕ) (queries : FixedArrayTable m ℕ) :
    (cutBuild U true queries).1.read (Fin.last m)=2*U := by
  rw [cutBuild,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp only [cutValue,Fin.val_last,lt_self_iff_false,dif_neg,ite_true,not_false_eq_true]

theorem cut_work {m : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) :
    (cutBuild U negative queries).2=54*(m+1)+18 := by
  rw [cutBuild,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

structure Plan (k m : ℕ) where
  positive : FixedArrayTable (m+1) (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
  negative : FixedArrayTable (m+1) (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
  work : ℕ

def prepare {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) : Plan k m :=
  let posCuts := cutBuild U false queries
  let negCuts := cutBuild U true queries
  let pos := GeneralPaperRankCache.build k summary posCuts.1
  let neg := GeneralPaperRankCache.build k summary negCuts.1
  ⟨pos.1,neg.1,posCuts.2+negCuts.2+pos.2+neg.2+16⟩

structure Pair where
  positive : ℕ
  negative : ℕ
  work : ℕ

def evaluate {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : Pair :=
  let pos := GeneralPaperIntervalQuery.cached k preparedPrefix plan.positive q.castSucc (Fin.last m)
  let neg := GeneralPaperIntervalQuery.cached k preparedPrefix plan.negative q.castSucc (Fin.last m)
  ⟨pos.quotient,neg.quotient,pos.work+neg.work+8⟩

theorem evaluate_positive {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k preparedPrefix (prepare k U summary queries) q).positive=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (queries.read q) U := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedInterval.cached_count,positive_low,positive_high]

theorem evaluate_negative {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k preparedPrefix (prepare k U summary queries) q).negative=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (U+queries.read q) (2*U) := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedInterval.cached_count,negative_low,negative_high]

theorem prepare_work {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) :
    (prepare k U summary queries).work≤2*(m+1)*((35+k)*(12*(35+k)+34)+120)+88 := by
  have hp := GeneralPaperRankCache.build_work k summary (cutBuild U false queries).1
  have hn := GeneralPaperRankCache.build_work k summary (cutBuild U true queries).1
  change (cutBuild U false queries).2+(cutBuild U true queries).2+_+_+16≤_
  rw [cut_work,cut_work]
  nlinarith

theorem evaluate_work {m : ℕ} (k : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : (evaluate k preparedPrefix plan q).work=24*(30+k)+124 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperIntervalQuery.cached_work,GeneralPaperIntervalQuery.cached_work]
  omega

end Blotto.GeneralPaperSignedTailPlan

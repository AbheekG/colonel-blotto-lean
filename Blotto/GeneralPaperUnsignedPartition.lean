import Blotto.GeneralPaperSignedUpdateReference
import Blotto.GeneralPaperCellRepresentatives

/-! The unsigned block's complete epoch breakpoint input: strict/weak CDF
positions, projected signed-summary successors, and every cached row option.
The signs are projected only to insert thresholds; their weights stay in one
signed block and retain the common denominator.
-/
namespace Blotto.GeneralPaperUnsignedPartition
open GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem project_bound (U code : ℕ) (hCode : code<2*U) : GeneralPaperSignedUpdatePlan.project U code<U := by
  unfold GeneralPaperSignedUpdatePlan.project
  split_ifs <;> omega

def extras {n m : ℕ} (U : ℕ) (signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    FixedArrayTable (n+m) ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    (if h : i.val<n then GeneralPaperSignedUpdatePlan.project U (signedSummary.read ⟨i.val,h⟩)+1
      else options.read ⟨i.val-n,by have := i.isLt; omega⟩,20))

theorem extras_summary {n m : ℕ} (U : ℕ) (signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (r : Fin n) :
    (extras U signedSummary options).1.read ⟨r.val,by omega⟩=
      GeneralPaperSignedUpdatePlan.project U (signedSummary.read r)+1 := by
  rw [extras,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [r.isLt]

theorem extras_option {n m : ℕ} (U : ℕ) (signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (r : Fin m) :
    (extras U signedSummary options).1.read ⟨n+r.val,by omega⟩=options.read r := by
  rw [extras,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [show ¬n+r.val<n by omega]

theorem extras_work {n m : ℕ} (U : ℕ) (signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (extras U signedSummary options).2=62*(n+m)+18 := by
  rw [extras,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

def prepare {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperPreparedPartition.Prepared :=
  GeneralPaperEpochPartition.prepare U cdfSummary (extras U signedSummary options).1

theorem count_bound {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (prepare U cdfSummary signedSummary options).count≤3*n+m+1 := by
  have he := GeneralPaperEpochPartition.count_bound U cdfSummary (extras U signedSummary options).1
  change (prepare U cdfSummary signedSummary options).count≤2*n+(n+m)+1 at he
  omega

theorem covers {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    Covers U (prepare U cdfSummary signedSummary options).intervals := GeneralPaperEpochPartition.covers _ _ _

theorem disjoint {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (prepare U cdfSummary signedSummary options).intervals :=
  GeneralPaperEpochPartition.disjoint _ _ _

theorem projected_test_constant {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (a : Fin n) (hA : signedSummary.read a<2*U) (r : Fin (prepare U cdfSummary signedSummary options).count) (i j : ℕ)
    (hI : Contains (prepare U cdfSummary signedSummary options).intervals r i)
    (hJ : Contains (prepare U cdfSummary signedSummary options).intervals r j) :
    GeneralPaperSignedUpdatePlan.project U (signedSummary.read a)< i ↔
      GeneralPaperSignedUpdatePlan.project U (signedSummary.read a)<j := by
  have hb := project_bound U _ hA
  have he := GeneralPaperEpochPartition.extra_test_constant U cdfSummary (extras U signedSummary options).1
    ⟨a.val,by omega⟩ (by rw [extras_summary]; omega) r i j hI hJ
  rw [extras_summary] at he
  omega

end Blotto.GeneralPaperUnsignedPartition

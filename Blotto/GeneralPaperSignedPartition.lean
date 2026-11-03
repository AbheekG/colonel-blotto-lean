import Blotto.GeneralPaperUnsignedCellConstancy

/-! Signed-family epoch inputs insert the unsigned CDF thresholds in each
sign, both copies of every cached bid, and the sign boundary. This only
duplicates breakpoint codes; the signed learner remains one distribution.
-/
namespace Blotto.GeneralPaperSignedPartition
open GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

def positions {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : FixedArrayTable (2*n) ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    (if h : i.val<n then summary.read ⟨i.val,h⟩ else U+summary.read ⟨i.val-n,by have := i.isLt; omega⟩,20))

theorem position_positive {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (r : Fin n) :
    (positions U summary).1.read ⟨r.val,by omega⟩=summary.read r := by
  rw [positions,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [r.isLt]

theorem position_negative {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (r : Fin n) :
    (positions U summary).1.read ⟨n+r.val,by omega⟩=U+summary.read r := by
  rw [positions,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [show ¬n+r.val<n by omega]

theorem positions_work {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) :
    (positions U summary).2=62*(2*n)+18 := by
  rw [positions,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

def extras {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) : FixedArrayTable (2*m+1) ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i =>
    (if h : i.val<m then options.read ⟨i.val,h⟩
      else if h' : i.val<2*m then U+options.read ⟨i.val-m,by omega⟩ else U,24))

theorem option_positive {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) (r : Fin m) :
    (extras U options).1.read ⟨r.val,by omega⟩=options.read r := by
  rw [extras,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [r.isLt]

theorem option_negative {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) (r : Fin m) :
    (extras U options).1.read ⟨m+r.val,by omega⟩=U+options.read r := by
  rw [extras,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [show ¬m+r.val<m by omega,show m+r.val<2*m by omega]

theorem sign_boundary {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) :
    (extras U options).1.read (Fin.last (2*m))=U := by
  rw [extras,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  simp [show ¬2*m<m by omega]

theorem extras_work {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) : (extras U options).2=66*(2*m+1)+18 := by
  rw [extras,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

def prepare {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperPreparedPartition.Prepared := GeneralPaperEpochPartition.prepare (2*U) (positions U summary).1 (extras U options).1

theorem count_bound {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (prepare U summary options).count≤4*n+2*m+2 := by
  have he := GeneralPaperEpochPartition.count_bound (2*U) (positions U summary).1 (extras U options).1
  change (prepare U summary options).count≤2*(2*n)+(2*m+1)+1 at he
  omega

theorem covers {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    Covers (2*U) (prepare U summary options).intervals := GeneralPaperEpochPartition.covers _ _ _

theorem disjoint {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (prepare U summary options).intervals := GeneralPaperEpochPartition.disjoint _ _ _

theorem sign_constant {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (r : Fin (prepare U summary options).count) (i j : ℕ)
    (hI : Contains (prepare U summary options).intervals r i) (hJ : Contains (prepare U summary options).intervals r j) :
    (i<U ↔ j<U) := by
  have he := GeneralPaperEpochPartition.extra_test_constant (2*U) (positions U summary).1 (extras U options).1
    (Fin.last (2*m)) (by rw [sign_boundary]; omega) r i j hI hJ
  rw [sign_boundary] at he
  omega

theorem weak_project_constant {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (a : Fin n) (hA : summary.read a<U) (r : Fin (prepare U summary options).count) (i j : ℕ)
    (hI : Contains (prepare U summary options).intervals r i) (hJ : Contains (prepare U summary options).intervals r j) :
    summary.read a≤GeneralPaperSignedUpdatePlan.project U i ↔ summary.read a≤GeneralPaperSignedUpdatePlan.project U j := by
  have hs := sign_constant U summary options r i j hI hJ
  by_cases hi : i<U
  · have hj := hs.mp hi
    have he := GeneralPaperEpochPartition.weak_test_constant (2*U) (positions U summary).1 (extras U options).1
      ⟨a.val,by omega⟩ (by rw [position_positive]; omega) r i j hI hJ
    rw [position_positive] at he
    simpa only [GeneralPaperSignedUpdatePlan.project,hi,hj,ite_true] using he
  · have hj : ¬j<U := fun h => hi (hs.mpr h)
    have he := GeneralPaperEpochPartition.weak_test_constant (2*U) (positions U summary).1 (extras U options).1
      ⟨n+a.val,by omega⟩ (by rw [position_negative]; omega) r i j hI hJ
    rw [position_negative] at he
    simp only [GeneralPaperSignedUpdatePlan.project,hi,hj,ite_false]
    omega

theorem bid_project_constant {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (q : Fin m) (hBid : options.read q<U) (r : Fin (prepare U summary options).count) (i j : ℕ)
    (hI : Contains (prepare U summary options).intervals r i) (hJ : Contains (prepare U summary options).intervals r j) :
    options.read q≤GeneralPaperSignedUpdatePlan.project U i ↔ options.read q≤GeneralPaperSignedUpdatePlan.project U j := by
  have hs := sign_constant U summary options r i j hI hJ
  by_cases hi : i<U
  · have hj := hs.mp hi
    have he := GeneralPaperEpochPartition.extra_test_constant (2*U) (positions U summary).1 (extras U options).1
      ⟨q.val,by omega⟩ (by rw [option_positive]; omega) r i j hI hJ
    rw [option_positive] at he
    simpa only [GeneralPaperSignedUpdatePlan.project,hi,hj,ite_true] using he
  · have hj : ¬j<U := fun h => hi (hs.mpr h)
    have he := GeneralPaperEpochPartition.extra_test_constant (2*U) (positions U summary).1 (extras U options).1
      ⟨m+q.val,by omega⟩ (by rw [option_negative]; omega) r i j hI hJ
    rw [option_negative] at he
    simp only [GeneralPaperSignedUpdatePlan.project,hi,hj,ite_false]
    omega

end Blotto.GeneralPaperSignedPartition

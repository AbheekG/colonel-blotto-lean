import Blotto.GeneralPaperBasisSelectedRows

/-! Cache the two integer adjugate/RHS products defining continuation.
The original constants and slopes are used; the initializer N is absent.
-/
namespace Blotto.GeneralPaperBasisAffineData
open GeneralPaperBasisStoredProducts GeneralPaperBasisState
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Data (d : ℕ) where
  constant : Vector d
  slope : Vector d
  determinant : ℤ
  work : ℕ

def rhsRun {d : ℕ} (state : State d d) (useSlope : Bool) : Vector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1
    (fun i => (if useSlope then (state.rows.read i).slope else (state.rows.read i).constant,4))

def prepare {d : ℕ} (state : State d d) : Data d :=
  let c := rhsRun state false
  let s := rhsRun state true
  let ac := mulVecRun state.adjugate c.1
  let bs := mulVecRun state.adjugate s.1
  ⟨ac.1,bs.1,state.determinant,c.2+s.2+ac.2+bs.2+12⟩

theorem rhs_read {d : ℕ} (state : State d d) (useSlope : Bool) (i : Fin d) :
    (rhsRun state useSlope).1.read i=(if useSlope then (state.rows.read i).slope else (state.rows.read i).constant) := by
  simp only [rhsRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem rhs_vector {d : ℕ} (state : State d d) (useSlope : Bool) :
    (rhsRun state useSlope).1.read=(fun i => if useSlope then (state.rows.read i).slope else (state.rows.read i).constant) :=
  funext (rhs_read state useSlope)

theorem constant_read {d : ℕ} (state : State d d) (i : Fin d) :
    (prepare state).constant.read i=(observe state.adjugate).mulVec (fun j => (state.rows.read j).constant) i := by
  simp only [prepare,mulVec_data,rhs_vector,Bool.false_eq_true,ite_false]

theorem slope_read {d : ℕ} (state : State d d) (i : Fin d) :
    (prepare state).slope.read i=(observe state.adjugate).mulVec (fun j => (state.rows.read j).slope) i := by
  simp only [prepare,mulVec_data,rhs_vector,ite_true]

theorem determinant {d : ℕ} (state : State d d) : (prepare state).determinant=state.determinant := rfl

theorem rhs_work {d : ℕ} (state : State d d) (useSlope : Bool) : (rhsRun state useSlope).2≤64*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun i : Fin d => ((if useSlope then (state.rows.read i).slope else (state.rows.read i).constant),4))
  change (rhsRun state useSlope).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  omega

theorem work {d : ℕ} (state : State d d) : (prepare state).work≤512*(d+1)^2 := by
  have hc := rhs_work state false
  have hs := rhs_work state true
  have ha := mulVec_work state.adjugate (rhsRun state false).1
  have hb := mulVec_work state.adjugate (rhsRun state true).1
  change (rhsRun state false).2+(rhsRun state true).2+(mulVecRun state.adjugate (rhsRun state false).1).2+
    (mulVecRun state.adjugate (rhsRun state true).1).2+12≤_
  nlinarith only [hc,hs,ha,hb]

end Blotto.GeneralPaperBasisAffineData

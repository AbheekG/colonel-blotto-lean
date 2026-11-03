import Blotto.GeneralPaperBasisCoordinates

/-! One selected-entry scatter accumulates a literal sparse integer row.
Repeated coordinates add correctly. No dense per-coefficient term scan is
executed; zero initialization plus one sparse pass gives linear work.
-/
namespace Blotto.GeneralPaperBasisCoefficientScatter
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Result (d : ℕ) where
  vector : Vector d
  work : ℕ

def loop {d : ℕ} : List (Fin d × ℤ) → Vector d → ℕ → Result d
  | [],values,spent => ⟨values,spent+2⟩
  | term::rest,values,spent =>
    let updated := values.write term.1 (values.read term.1+term.2)
    loop rest updated (spent+16)

theorem loop_read {d : ℕ} (terms : List (Fin d × ℤ)) (values : Vector d) (spent : ℕ) (i : Fin d) :
    (loop terms values spent).vector.read i=values.read i+RationalOrderCell.coefficientTerms terms i := by
  induction terms generalizing values spent with
  | nil => simp only [loop,RationalOrderCell.coefficientTerms,List.map_nil,List.sum_nil,add_zero]
  | cons term rest ih =>
    rw [loop,ih,FixedArrayTable.read_write]
    change (if i=term.1 then values.read term.1+term.2 else values.read i)+_=
      values.read i+((if term.1=i then term.2 else 0)+RationalOrderCell.coefficientTerms rest i)
    by_cases he : i=term.1
    · subst i
      simp only [ite_true]
      ring
    · have hn : term.1≠i := Ne.symm he
      simp only [he,hn,ite_false,zero_add]

theorem loop_work {d : ℕ} (terms : List (Fin d × ℤ)) (values : Vector d) (spent : ℕ) :
    (loop terms values spent).work=spent+16*terms.length+2 := by
  induction terms generalizing values spent with
  | nil => simp only [loop,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons term rest ih => rw [loop,ih,List.length_cons]; omega

def zeroRun (d : ℕ) : Vector d × ℕ := PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun _ => (0,2))

def run {d : ℕ} (terms : List (Fin d × ℤ)) : Result d :=
  let initial := zeroRun d
  let result := loop terms initial.1 0
  ⟨result.vector,initial.2+result.work+4⟩

theorem run_read {d : ℕ} (terms : List (Fin d × ℤ)) (i : Fin d) :
    (run terms).vector.read i=RationalOrderCell.coefficientTerms terms i := by
  rw [run,loop_read]
  simp only [zeroRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,zero_add]

theorem zero_work (d : ℕ) : (zeroRun d).2≤64*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1 (fun _ : Fin d => ((0:ℤ),2))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (zeroRun d).2≤_ at hh
  omega

theorem run_work {d : ℕ} (terms : List (Fin d × ℤ)) : (run terms).work≤64*(d+1)+16*terms.length+6 := by
  have hh := zero_work d
  change (zeroRun d).2+(loop terms (zeroRun d).1 0).work+4≤_
  rw [loop_work]
  omega

end Blotto.GeneralPaperBasisCoefficientScatter

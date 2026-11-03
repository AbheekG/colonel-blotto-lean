import Blotto.GeneralPaperNaturalPrimitivePrice

/-! Literal additive sparse scatter with every prefix bounded before
cancellation. Selected reads/writes use references; the coefficient addition
and its result use their actual signed integer bit widths.
-/
namespace Blotto.GeneralPaperBasisScatterBits
open GeneralPaperBasisStoredProducts GeneralPaperIntegerPrimitivePrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000

def loop {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) : List (Fin d × ℤ) → Vector d → ℕ → GeneralPaperBasisCoefficientScatter.Result d
  | [],values,spent => ⟨values,spent+2*W⟩
  | term::rest,values,spent =>
    let sum := values.read term.1+term.2
    loop primitive W rest (values.write term.1 sum) (spent+32*W+binary primitive (fun a b => a+b) (values.read term.1) term.2)

theorem loop_data {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (terms : List (Fin d × ℤ)) (values : Vector d) (spent oldSpent : ℕ) :
    (loop primitive W terms values spent).vector=(GeneralPaperBasisCoefficientScatter.loop terms values oldSpent).vector := by
  induction terms generalizing values spent oldSpent with
  | nil => rfl
  | cons t rest ih => exact ih _ _ _

theorem loop_work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W A M : ℕ)
    (terms : List (Fin d × ℤ)) (values : Vector d) (spent : ℕ)
    (hTerms : ∀ t∈terms,t.2.natAbs≤1) (hValues : ∀ i,(values.read i).natAbs≤A) (hMass : A+terms.length≤M) :
    (loop primitive W terms values spent).work≤spent+terms.length*(32*W+2*primitive (1+binaryWordWidth M))+2*W := by
  induction terms generalizing A values spent with
  | nil => simp only [loop,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons t rest ih =>
    have ht := hTerms t List.mem_cons_self
    have hs : (values.read t.1+t.2).natAbs≤A+1 := (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hValues t.1) ht)
    have hNext (i) : ((values.write t.1 (values.read t.1+t.2)).read i).natAbs≤A+1 := by
      rw [FixedArrayTable.read_write]
      split
      · exact hs
      · exact (hValues i).trans (Nat.le_succ _)
    have hp := binary_le primitive hMono (fun a b => a+b) (values.read t.1) t.2 M
      ((hValues t.1).trans (by simp only [List.length_cons] at hMass; omega))
      (ht.trans (by simp only [List.length_cons] at hMass; omega))
      (hs.trans (by simp only [List.length_cons] at hMass; omega))
    have hr := ih (A+1) (values.write t.1 (values.read t.1+t.2))
      (spent+32*W+binary primitive (fun a b => a+b) (values.read t.1) t.2)
      (fun u hu => hTerms u (List.mem_cons_of_mem t hu)) hNext (by simp only [List.length_cons] at hMass; omega)
    change (loop primitive W rest (values.write t.1 (values.read t.1+t.2))
      (spent+32*W+binary primitive (fun a b => a+b) (values.read t.1) t.2)).work≤_
    rw [List.length_cons]
    nlinarith only [hr,hp]

def zeroRun (W d : ℕ) : Vector d × ℕ := PaperIndexedArrayConstruction.run (fun w => w) W (fun _ => (0,2*W))

theorem zero_data (W d : ℕ) : (zeroRun W d).1=(GeneralPaperBasisCoefficientScatter.zeroRun d).1 := by
  simp only [zeroRun,GeneralPaperBasisCoefficientScatter.zeroRun,PaperIndexedArrayConstruction.run_data]

theorem zero_work (W d : ℕ) (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) : (zeroRun W d).2≤64*(d+1)*W := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W (fun _ : Fin d => ((0:ℤ),2*W))
  change (zeroRun W d).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  have hO : 6*W+10*1*binaryWordWidth (d+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (d+1) hO
  nlinarith only [hh,ho,Nat.zero_le (d*W)]

def run {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (terms : List (Fin d × ℤ)) : GeneralPaperBasisCoefficientScatter.Result d :=
  let initial := zeroRun W d
  let returned := loop primitive W terms initial.1 0
  ⟨returned.vector,initial.2+returned.work+8*W⟩

theorem data {d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (terms : List (Fin d × ℤ)) :
    (run primitive W terms).vector=(GeneralPaperBasisCoefficientScatter.run terms).vector := by
  simp only [run,GeneralPaperBasisCoefficientScatter.run,loop_data primitive W terms _ 0 0,zero_data]

theorem work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) (terms : List (Fin d × ℤ)) (hTerms : ∀ t∈terms,t.2.natAbs≤1) :
    (run primitive W terms).work≤256*(d+terms.length+1)*(W+primitive (1+binaryWordWidth terms.length)) := by
  have hz := zero_work W d hW hD
  have hl := loop_work primitive hMono W 0 terms.length terms (zeroRun W d).1 0 hTerms
    (by intro i; simp only [zero_data,GeneralPaperBasisCoefficientScatter.zeroRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,Int.natAbs_zero,le_refl])
    (by omega)
  change (zeroRun W d).2+(loop primitive W terms (zeroRun W d).1 0).work+8*W≤_
  nlinarith only [hz,hl,Nat.zero_le (d*W),Nat.zero_le (terms.length*W),
    Nat.zero_le (d*primitive (1+binaryWordWidth terms.length)),Nat.zero_le (terms.length*primitive (1+binaryWordWidth terms.length))]

end Blotto.GeneralPaperBasisScatterBits

import Blotto.GeneralPaperRepresentativeSortLaw

/-! Materialize sorted rational bid references once per stored row. The
two-level constructor retains complete source rows and never resamples
coordinates. Reference writes do not copy rational payloads. -/
namespace Blotto.GeneralPaperNativeSortedRows
open GeneralPaperNativeRepresentativeSort
set_option autoImplicit false
set_option maxHeartbeats 1800000

def one {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) : FixedArrayTable R ℚ × ℕ :=
  let order := run price index A values
  let stored := PaperIndexedArrayConstruction.run index A (fun a => (values.read (order.1.read a),64*A))
  (stored.1,order.2+stored.2+16*A)

theorem one_data {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) :
    (one price index A values).1=FixedArrayTable.ofFn (fun a => values.read ((GeneralPaperRowSort.order values).read a)) := by
  unfold one
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,data]

theorem one_real {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) (a : Fin R) :
    ((one price index A values).1.read a:ℝ)=GeneralPaperCircleSortedComparison.sorted (fun j => (values.read j:ℝ)) a := by
  rw [one_data,FixedArrayTable.read_ofFn]
  have h := GeneralPaperRepresentativeSortLaw.real_sorted price index A values a
  rw [data] at h
  exact h

def oneProfile (R A P : ℕ) : ℕ := profile R A P+128*(R+1)*A

theorem one_work {R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (values : FixedArrayTable R ℚ) (hValues : ∀ j,rationalWordWidth (values.read j)≤H)
    (hIndex : ∀ i≤R,index (binaryWordWidth (i+1))≤A) :
    (one price index A values).2≤oneProfile R A (price H) := by
  have hSort := work price index hMono A H hA values hValues hIndex
  have hStore := GeneralPaperControlArrayPrice.indexed_work index A (64*A)
    (fun a => (values.read ((run price index A values).1.read a),64*A)) hA hIndex (fun _ => le_rfl)
  change (run price index A values).2+
    (PaperIndexedArrayConstruction.run index A (fun a => (values.read ((run price index A values).1.read a),64*A))).2+16*A≤_
  unfold oneProfile
  nlinarith only [hSort,hStore]

def matrix {T R : ℕ} (price index : ℕ → ℕ) (rowAddress fieldAddress : ℕ)
    (rows : FixedArrayTable T (FixedArrayTable R ℚ)) : FixedArrayTable T (FixedArrayTable R ℚ) × ℕ :=
  PaperIndexedArrayConstruction.run index rowAddress (fun r =>
    let sorted := one price index fieldAddress (rows.read r)
    (sorted.1,sorted.2+64*rowAddress))

theorem matrix_data {T R : ℕ} (price index : ℕ → ℕ) (rowAddress fieldAddress : ℕ)
    (rows : FixedArrayTable T (FixedArrayTable R ℚ)) :
    (matrix price index rowAddress fieldAddress rows).1=FixedArrayTable.ofFn (fun r => (one price index fieldAddress (rows.read r)).1) := by
  unfold matrix
  rw [PaperIndexedArrayConstruction.run_data]

theorem matrix_real {T R : ℕ} (price index : ℕ → ℕ) (rowAddress fieldAddress : ℕ)
    (rows : FixedArrayTable T (FixedArrayTable R ℚ)) (r : Fin T) (a : Fin R) :
    (((matrix price index rowAddress fieldAddress rows).1.read r).read a:ℝ)=
      GeneralPaperCircleSortedComparison.sorted (fun j => ((rows.read r).read j:ℝ)) a := by
  rw [matrix_data,FixedArrayTable.read_ofFn,one_real]

theorem matrix_work {T R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (rowAddress fieldAddress H : ℕ)
    (hRow : 1≤rowAddress) (hField : 1≤fieldAddress) (rows : FixedArrayTable T (FixedArrayTable R ℚ))
    (hValues : ∀ r j,rationalWordWidth ((rows.read r).read j)≤H)
    (hRowIndex : ∀ i≤T,index (binaryWordWidth (i+1))≤rowAddress)
    (hFieldIndex : ∀ i≤R,index (binaryWordWidth (i+1))≤fieldAddress) :
    (matrix price index rowAddress fieldAddress rows).2≤
      T*(oneProfile R fieldAddress (price H)+64*rowAddress)+44*(T+1)*rowAddress := by
  exact GeneralPaperControlArrayPrice.indexed_work index rowAddress _ _ hRow hRowIndex
    (fun r => Nat.add_le_add_right (one_work price index hMono fieldAddress H hField (rows.read r) (hValues r) hFieldIndex) _)

end Blotto.GeneralPaperNativeSortedRows

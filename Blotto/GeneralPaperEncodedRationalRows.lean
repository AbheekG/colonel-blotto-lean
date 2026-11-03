import Blotto.GeneralPaperSourceRowsSharpContract

/-! Owned rational-row arrays and reserved outer row references. All
payload bounds follow from actual native decoded values and array sizes.
These observers are erased; no output census is executed. -/
namespace Blotto.GeneralPaperEncodedRationalRows
open GeneralPaperEncodedReferenceVector GeneralPaperSourceRowsExecution
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def rowFootprint {m : ℕ} (W : ℕ) (values : FixedArrayTable m ℚ) : ℕ :=
  footprint W rationalWordWidth values.data

def rowProfile (W m s : ℕ) : ℕ := m*(1+2*s+W)+64*W

theorem row_bound {m : ℕ} (W s : ℕ) (values : FixedArrayTable m ℚ)
    (h : ∀ j,RationalHeight (values.read j) s) : rowFootprint W values≤rowProfile W m s := by
  have hb := bounded W (1+2*s) rationalWordWidth values.data (by
    intro i
    let j : Fin m := ⟨i.val,i.isLt.trans_eq values.size⟩
    exact rationalWordWidth_of_height (h j))
  simpa only [rowFootprint,rowProfile,values.size] using hb

def tableFootprint {T m : ℕ} (W : ℕ) (values : FixedArrayTable T (FixedArrayTable m ℚ)) : ℕ :=
  reservedFootprint W T (rowFootprint W) values.data

def tableProfile (W T m s : ℕ) : ℕ := T*(rowProfile W m s+W)+64*W

theorem table_bound {T m : ℕ} (W s : ℕ) (values : FixedArrayTable T (FixedArrayTable m ℚ))
    (h : ∀ i j,RationalHeight ((values.read i).read j) s) :
    tableFootprint W values≤tableProfile W T m s := by
  apply reserved_bound W (rowProfile W m s) T (rowFootprint W) values.data (by rw [values.size])
  intro i
  let j : Fin T := ⟨i.val,i.isLt.trans_eq values.size⟩
  exact row_bound W s (values.read j) (h j)

theorem row_prefix {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m) :
    reservedFootprint W m rationalWordWidth (PaperIndexedArrayConstruction.fill (index true)
      (address true W m) (fun j =>
        let bid := GeneralPaperClosedBidExecution.run true model W a (codes.read j)
        (bid.1,bid.2+64*address true W m)) count hc).1≤rowProfile W m (binaryWordWidth a.C) :=
  indexed_reserved_prefix (index true) (address true W m) W (1+2*binaryWordWidth a.C) rationalWordWidth
    (fun j => let bid := GeneralPaperClosedBidExecution.run true model W a (codes.read j)
      (bid.1,bid.2+64*address true W m))
    (fun j => rationalWordWidth_of_height (GeneralPaperClosedBidExecution.height true model W a (codes.read j))) count hc

theorem native_row {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) :
    rowFootprint W (row bits model W a codes).1≤rowProfile W m (binaryWordWidth a.C) :=
  row_bound W _ _ (row_height bits model W a codes)

theorem table_prefix {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count≤T) :
    reservedFootprint W T (rowFootprint W) (fill bits model W a codes B count hc).1.1≤
      tableProfile W T m (binaryWordWidth a.C) := by
  rw [fill_data bits model W 0]
  apply reserved_bound W (rowProfile W m (binaryWordWidth a.C)) T (rowFootprint W) _
    (by rw [Array.size_ofFn]; exact hc)
  intro i
  rw [Array.getElem_ofFn]
  apply row_bound
  intro j
  rw [FixedArrayTable.read_ofFn]
  exact GeneralPaperSourceScoreHeights.decoded_height m 0 a _

theorem returned {T m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) :
    tableFootprint W (run bits model W a codes B).1.1≤tableProfile W T m (binaryWordWidth a.C) := by
  apply table_bound
  intro i j
  rw [data bits model W 0,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  exact GeneralPaperSourceScoreHeights.decoded_height m 0 a _

end Blotto.GeneralPaperEncodedRationalRows

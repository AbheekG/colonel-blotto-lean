import Blotto.GeneralPaperPhysicalBidStorage

/-! The actual physical-row builder reserves rational slots, retains its
caller frames and releases each decoder child before the next coordinate.
Whole-row checking borrows the completed row; only its scalar scan stack
and active primitive scratch remain. The rational response is then released. -/
namespace Blotto.GeneralPaperPhysicalResponseStorage
open GeneralPaperCodeAlphabet GeneralPaperPhysicalResponseExecution GeneralPaperSourceRowsExecution
open GeneralPaperEncodedRationalRows GeneralPaperEncodedReferenceVector GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option maxRecDepth 8192

theorem row_height {m : ℕ} (bits : Bool) (model : RationalCostModel) (W qbar : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (codes : FixedArrayTable m ℕ) (j : Fin m) :
    RationalHeight ((GeneralPaperPhysicalResponseExecution.row bits model W a delta codes).1.read j) (GeneralPaperPhysicalBidStorage.height m qbar a) := by
  rw [GeneralPaperPhysicalResponseExecution.row_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperResponsePhysicalHeights.bid_height _ _ _ (GeneralPaperPhysicalBidExecution.threshold_height a _) delta hd

def rowPrefix {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m) : ℕ :=
  reservedFootprint W m rationalWordWidth (PaperIndexedArrayConstruction.fill (index true) (address true W m)
    (fun j => let bid := GeneralPaperPhysicalBidExecution.run true model W a delta (codes.read j)
      (bid.1,bid.2+64*address true W m)) count hc).1

theorem prefix_bound {m : ℕ} (model : RationalCostModel) (W qbar : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m) :
    rowPrefix model W a delta codes count hc≤rowProfile W m (GeneralPaperPhysicalBidStorage.height m qbar a) :=
  indexed_reserved_prefix (index true) (address true W m) W (1+2*GeneralPaperPhysicalBidStorage.height m qbar a) rationalWordWidth
    (fun j => let bid := GeneralPaperPhysicalBidExecution.run true model W a delta (codes.read j)
      (bid.1,bid.2+64*address true W m))
    (fun j => rationalWordWidth_of_height (GeneralPaperPhysicalBidStorage.returned_height true model W m qbar a delta hd (codes.read j))) count hc

def rowLocal {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count+1≤m) : ℕ :=
  rowPrefix model W a delta codes count (by omega)+rowPrefix model W a delta codes (count+1) hc+
    GeneralPaperPhysicalBidStorage.window model W a delta (codes.read ⟨count,by omega⟩)+256*arrayWord W m

def rowTailProfile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  2*rowProfile W m (GeneralPaperPhysicalBidStorage.height m qbar a)+
    GeneralPaperPhysicalBidStorage.profile model W m qbar t a+256*arrayWord W m

theorem row_local_bound {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (codes : FixedArrayTable m ℕ) (hCode : ∀ j,codes.read j≤8*a.C) (count : ℕ) (hc : count+1≤m) :
    rowLocal model W a delta codes count hc≤rowTailProfile model W m qbar t a := by
  have h0 := prefix_bound model W qbar a delta hd codes count (by omega)
  have h1 := prefix_bound model W qbar a delta hd codes (count+1) hc
  have hb := GeneralPaperPhysicalBidStorage.bounded model W m qbar t a delta hd (codes.read ⟨count,by omega⟩) (hCode _)
  unfold rowLocal rowTailProfile
  omega

def rowPeak {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ) (codes : FixedArrayTable m ℕ) :
    (count : ℕ) → count≤m → ℕ
  | 0,hc => GeneralPaperRowBudgetStorage.frame (arrayWord W m) m 0+rowPrefix model W a delta codes 0 hc+128*arrayWord W m
  | k+1,hk => GeneralPaperRowBudgetStorage.frame (arrayWord W m) m (k+1)+
    max (rowPeak model W a delta codes k (by omega)) (rowLocal model W a delta codes k hk)

def rowPeakProfile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  (m+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W m) m+rowTailProfile model W m qbar t a

theorem row_peak_bound {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (codes : FixedArrayTable m ℕ) (hCode : ∀ j,codes.read j≤8*a.C) (count : ℕ) (hc : count≤m) :
    rowPeak model W a delta codes count hc≤
      (count+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W m) m+rowTailProfile model W m qbar t a := by
  induction count with
  | zero =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W m) m 0 hc
    have hp := prefix_bound model W qbar a delta hd codes 0 hc
    simp only [rowPeak,Nat.zero_add,Nat.one_mul]
    unfold rowTailProfile
    omega
  | succ k ih =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W m) m (k+1) hc
    have hi := ih (by omega)
    have hl := row_local_bound model W qbar t a delta hd codes hCode k hc
    have hm := max_le hi (hl.trans (Nat.le_add_left _ _))
    rw [rowPeak]
    nlinarith only [hf,hm]

def window {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) : ℕ :=
  let decoded := (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1
  GeneralPaperEncodedNatArray.footprint W codes+rationalWordWidth delta+
    max (rowPeak model W a delta codes m le_rfl)
      (rowFootprint W decoded+GeneralPaperRowBudgetStorage.window model (arrayWord W m) decoded B)+
    rowFootprint W decoded+256*arrayWord W m

def profile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  m*(GeneralPaperDecoderControls.operandWidth a.lambda+W)+32*W+
    (1+2*GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C)+
    max (rowPeakProfile model W m qbar t a)
      (rowProfile W m (GeneralPaperPhysicalBidStorage.height m qbar a)+
        GeneralPaperRowBudgetStorage.profile model (arrayWord W m) m (GeneralPaperPhysicalBidStorage.height m qbar a) t)+
    rowProfile W m (GeneralPaperPhysicalBidStorage.height m qbar a)+256*arrayWord W m

theorem bounded {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (codes : FixedArrayTable m ℕ) (hCode : ∀ j,codes.read j≤8*a.C) (B : ℚ) (hB : RationalHeight B t) :
    window model W a delta codes B≤profile model W m qbar t a := by
  have hc := GeneralPaperEncodedNatArray.bounded W (GeneralPaperDecoderControls.operandWidth a.lambda) codes
    (fun j => GeneralPaperDecoderControls.code_word a _ (hCode j))
  have hdelta := rationalWordWidth_of_height hd
  have hp := row_peak_bound model W qbar t a delta hd codes hCode m le_rfl
  have hr := row_bound W (GeneralPaperPhysicalBidStorage.height m qbar a) (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1
    (row_height true model W qbar a delta hd codes)
  have hb := GeneralPaperRowBudgetStorage.bounded model (arrayWord W m) (GeneralPaperPhysicalBidStorage.height m qbar a) t
    (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 (row_height true model W qbar a delta hd codes) B hB
  have hm := max_le_max hp (Nat.add_le_add hr hb)
  unfold window profile rowPeakProfile
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hdelta) hm) hr) _

end Blotto.GeneralPaperPhysicalResponseStorage

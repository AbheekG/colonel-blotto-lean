import Blotto.GeneralPaperRowBudgetStorage

/-! Simultaneous ownership along actual native row/table construction.
Only caller frames accumulate on descent; child payload phases use maxima.
Reserved input/output slots, old/new push views and returned rows are explicit.
All observers are erased analyses of existing data, with no extra pass. -/
namespace Blotto.GeneralPaperSourceRowsStorage
open GeneralPaperCodeAlphabet GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperEncodedRationalRows GeneralPaperEncodedReferenceVector
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def rowPrefix {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m) : ℕ :=
  reservedFootprint W m rationalWordWidth (PaperIndexedArrayConstruction.fill (index true) (address true W m)
    (fun j => let bid := GeneralPaperClosedBidExecution.run true model W a (codes.read j)
      (bid.1,bid.2+64*address true W m)) count hc).1

def rowLocal {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count+1≤m) : ℕ :=
  rowPrefix model W a codes count (by omega)+rowPrefix model W a codes (count+1) hc+
    GeneralPaperClosedBidStorage.window model W a (codes.read ⟨count,by omega⟩)+256*arrayWord W m

def rowTailProfile (model : RationalCostModel) (W m : ℕ) (a : Alphabet) : ℕ :=
  2*rowProfile W m (binaryWordWidth a.C)+GeneralPaperClosedBidStorage.profile model W a+256*arrayWord W m

theorem row_local_bound {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (hCode : ∀ j,codes.read j≤8*a.C) (count : ℕ) (hc : count+1≤m) :
    rowLocal model W a codes count hc≤rowTailProfile model W m a := by
  have h0 := row_prefix model W a codes count (by omega)
  have h1 := row_prefix model W a codes (count+1) hc
  have hd := GeneralPaperClosedBidStorage.bounded model W a (codes.read ⟨count,by omega⟩) (hCode _)
  unfold rowLocal rowTailProfile rowPrefix
  omega

def rowPeak {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (codes : FixedArrayTable m ℕ) :
    (count : ℕ) → count≤m → ℕ
  | 0,hc => GeneralPaperRowBudgetStorage.frame (arrayWord W m) m 0+rowPrefix model W a codes 0 hc+128*arrayWord W m
  | k+1,hk => GeneralPaperRowBudgetStorage.frame (arrayWord W m) m (k+1)+
    max (rowPeak model W a codes k (by omega)) (rowLocal model W a codes k hk)

def rowPeakProfile (model : RationalCostModel) (W m : ℕ) (a : Alphabet) : ℕ :=
  (m+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W m) m+rowTailProfile model W m a

theorem row_peak_bound {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (hCode : ∀ j,codes.read j≤8*a.C) (count : ℕ) (hc : count≤m) :
    rowPeak model W a codes count hc≤
      (count+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W m) m+rowTailProfile model W m a := by
  induction count with
  | zero =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W m) m 0 hc
    have hp := row_prefix model W a codes 0 hc
    simp only [rowPeak,Nat.zero_add,Nat.one_mul]
    unfold rowTailProfile rowPrefix
    omega
  | succ k ih =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W m) m (k+1) hc
    have hi := ih (by omega)
    have hl := row_local_bound model W a codes hCode k hc
    have hm := max_le hi (hl.trans (Nat.le_add_left _ _))
    rw [rowPeak]
    nlinarith only [hf,hm]

def fieldWindow {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (B : ℚ) : ℕ :=
  let decoded := (row true model W a codes).1
  max (rowPeak model W a codes m le_rfl)
    (rowFootprint W decoded+GeneralPaperRowBudgetStorage.window model (arrayWord W m) decoded B)+
      rowFootprint W decoded+128*arrayWord W m

def fieldProfile (model : RationalCostModel) (W m t : ℕ) (a : Alphabet) : ℕ :=
  max (rowPeakProfile model W m a)
    (rowProfile W m (binaryWordWidth a.C)+GeneralPaperRowBudgetStorage.profile model (arrayWord W m)
      m (binaryWordWidth a.C) t)+rowProfile W m (binaryWordWidth a.C)+128*arrayWord W m

theorem field_bound {m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (hB : RationalHeight B t) (hCode : ∀ j,codes.read j≤8*a.C) :
    fieldWindow model W a codes B≤fieldProfile model W m t a := by
  have hp := row_peak_bound model W a codes hCode m le_rfl
  have hr := native_row true model W a codes
  have hb := GeneralPaperRowBudgetStorage.bounded model (arrayWord W m) (binaryWordWidth a.C) t
    (row true model W a codes).1 (row_height true model W a codes) B hB
  have hm := max_le_max hp (Nat.add_le_add hr hb)
  unfold fieldWindow fieldProfile rowPeakProfile
  dsimp only
  omega

def tablePrefix {T m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count≤T) : ℕ :=
  reservedFootprint W T (rowFootprint W) (fill true model W a codes B count hc).1.1

def localWindow {T m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (count : ℕ) (hc : count+1≤T) : ℕ :=
  tablePrefix model W a codes B count (by omega)+tablePrefix model W a codes B (count+1) hc+
    fieldWindow model W a (codes.read ⟨count,by omega⟩) B+256*arrayWord W T

def tailProfile (model : RationalCostModel) (W T m t : ℕ) (a : Alphabet) : ℕ :=
  2*tableProfile W T m (binaryWordWidth a.C)+fieldProfile model W m t a+256*arrayWord W T

theorem local_bound {T m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (hB : RationalHeight B t)
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) (count : ℕ) (hc : count+1≤T) :
    localWindow model W a codes B count hc≤tailProfile model W T m t a := by
  have h0 := table_prefix true model W a codes B count (by omega)
  have h1 := table_prefix true model W a codes B (count+1) hc
  have hf := field_bound model W t a (codes.read ⟨count,by omega⟩) B hB (hCode _)
  unfold localWindow tailProfile tablePrefix
  omega

def peak {T m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) : (count : ℕ) → count≤T → ℕ
  | 0,hc => GeneralPaperRowBudgetStorage.frame (arrayWord W T) T 0+
      tablePrefix model W a codes B 0 hc+128*arrayWord W T
  | k+1,hk => GeneralPaperRowBudgetStorage.frame (arrayWord W T) T (k+1)+
      max (peak model W a codes B k (by omega)) (localWindow model W a codes B k hk)

def peakProfile (model : RationalCostModel) (W T m t : ℕ) (a : Alphabet) : ℕ :=
  (T+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W T) T+tailProfile model W T m t a

theorem peak_bound {T m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (hB : RationalHeight B t)
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) (count : ℕ) (hc : count≤T) :
    peak model W a codes B count hc≤
      (count+1)*GeneralPaperRowBudgetStorage.frameProfile (arrayWord W T) T+tailProfile model W T m t a := by
  induction count with
  | zero =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W T) T 0 hc
    have hp := table_prefix true model W a codes B 0 hc
    simp only [peak,Nat.zero_add,Nat.one_mul]
    unfold tailProfile tablePrefix
    omega
  | succ k ih =>
    have hf := GeneralPaperRowBudgetStorage.frame_bound (arrayWord W T) T (k+1) hc
    have hi := ih (by omega)
    have hl := local_bound model W t a codes B hB hCode k hc
    have hm := max_le hi (hl.trans (Nat.le_add_left _ _))
    rw [peak]
    nlinarith only [hf,hm]

def codeFootprint {T m : ℕ} (W : ℕ) (codes : FixedArrayTable T (FixedArrayTable m ℕ)) : ℕ :=
  GeneralPaperEncodedTrajectoryStorage.footprint W T codes.data

def codeProfile (W T m lambda : ℕ) : ℕ :=
  T*(m*GeneralPaperDecoderControls.operandWidth lambda+m*W+65*W)+64*W

theorem code_bound {T m : ℕ} (W : ℕ) (a : Alphabet) (codes : FixedArrayTable T (FixedArrayTable m ℕ))
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) : codeFootprint W codes≤codeProfile W T m a.lambda := by
  have h := reserved_bound W (m*(GeneralPaperDecoderControls.operandWidth a.lambda+W)+64*W) T
    (GeneralPaperEncodedTrajectoryStorage.rowFootprint W) codes.data (by rw [codes.size]) (by
      intro i
      let j : Fin T := ⟨i.val,i.isLt.trans_eq codes.size⟩
      have hr := GeneralPaperEncodedNatArray.bounded W (GeneralPaperDecoderControls.operandWidth a.lambda)
        (codes.read j) (fun l => GeneralPaperDecoderControls.code_word a _ (hCode j l))
      change GeneralPaperEncodedNatArray.footprint W (codes.read j)+32*W≤_
      omega)
  rw [GeneralPaperEncodedTrajectoryStorage.structural_footprint] at h
  unfold codeFootprint codeProfile
  nlinarith only [h]

def window {T m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) : ℕ :=
  codeFootprint W codes+rationalWordWidth B+peak model W a codes B T le_rfl+
    tableFootprint W (run true model W a codes B).1.1+256*W

def profile (model : RationalCostModel) (W T m t : ℕ) (a : Alphabet) : ℕ :=
  codeProfile W T m a.lambda+(1+2*t)+peakProfile model W T m t a+
    tableProfile W T m (binaryWordWidth a.C)+256*W

theorem bounded {T m : ℕ} (model : RationalCostModel) (W t : ℕ) (a : Alphabet)
    (codes : FixedArrayTable T (FixedArrayTable m ℕ)) (B : ℚ) (hB : RationalHeight B t)
    (hCode : ∀ i j,(codes.read i).read j≤8*a.C) : window model W a codes B≤profile model W T m t a := by
  have hc := code_bound W a codes hCode
  have hb := rationalWordWidth_of_height hB
  have hp := peak_bound model W t a codes B hB hCode T le_rfl
  have hr := returned true model W a codes B
  unfold window profile peakProfile
  omega

end Blotto.GeneralPaperSourceRowsStorage

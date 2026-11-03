import Blotto.GeneralPaperRangeUpdateBitPrice
import Blotto.GeneralPaperSparseNodeBits

/-! Live control frames of the native range traversal. Node payloads belong
to the separately counted old/new forest; frames borrow node references.
The completed left result retains its actual work/visit annotations while
the right recursion runs. All maxima are erased observations. -/
namespace Blotto.GeneralPaperRangeTraversalStorage
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperRangeGeometryPrice
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def resultBits {height : ℕ} (W : ℕ) (r : GeneralPaperIntervalUpdate.Result height) : ℕ :=
  (1+binaryWordWidth r.work)+(1+binaryWordWidth r.visits)+64*W

def frame (W amount height : ℕ) (lo hi start span : ℚ) : ℕ :=
  rationalWordWidth lo+rationalWordWidth hi+rationalWordWidth start+rationalWordWidth span+
    (if height=0 then 0 else rationalWordWidth (span/2)+rationalWordWidth (start+span/2))+
    (1+binaryWordWidth amount)+(1+binaryWordWidth height)+256*W

def peak (W : ℕ) (prepared : GeneralPaperPreparedPowers.Prepared) (lo hi : ℚ)
    (amount height : ℕ) (n : Node height) (start span : ℚ) : ℕ :=
    let found := GeneralPaperIntervalUpdate.run prepared lo hi amount height n start span
    let live := frame W amount height lo hi start span+resultBits W found
    if Disjoint start span lo hi then live else
      if Covered start span lo hi then live else
        match height with
        | 0 => live
        | height+1 =>
          let left := GeneralPaperIntervalUpdate.run prepared lo hi amount height (leftChild n) start (span/2)
          max live (frame W amount (height+1) lo hi start span+
            max (peak W prepared lo hi amount height (leftChild n) start (span/2))
              (resultBits W left+peak W prepared lo hi amount height (rightChild n) (start+span/2) (span/2)))
termination_by height

def coefficient (W m lambda k Qv amount : ℕ) : ℕ :=
  6*GeneralPaperDecoderControls.operandWidth lambda+
    5*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+
    (1+binaryWordWidth amount)+384*W

theorem result_bound (W m lambda k Qv : ℕ) (lo hi : ℚ) (amount height : ℕ)
    (n : Node height) (start span : ℚ) (hh : height≤lambda+1) (hs : 0<span) :
    resultBits W (GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k)
      lo hi amount height n start span)≤2*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+64*W := by
  have h := GeneralPaperRangeCounterPrice.native_bounds lambda k lo hi amount height n start span hh hs
  have hw := GeneralPaperRangeCounterPrice.operand_width m lambda k Qv
  have ha := binaryWordWidth_mono h.1
  have hb := binaryWordWidth_mono h.2
  unfold resultBits
  omega

theorem frame_bound (W m lambda k Qv amount height : ℕ) (lo hi start span : ℚ)
    (hh : height≤lambda+1) (hw : Window lambda height start span)
    (hl : Bounded lambda lo) (hr : Bounded lambda hi) :
    frame W amount height lo hi start span≤
      6*GeneralPaperDecoderControls.operandWidth lambda+
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+
        (1+binaryWordWidth amount)+256*W := by
  have hb := window_words lambda height start span hw
  have hLo := rational_word lambda lo hl
  have hHi := rational_word lambda hi hr
  have hHeight := GeneralPaperSparseNodeBits.height_word m lambda k Qv height hh
  cases height with
  | zero =>
    simp only [frame,ite_true]
    omega
  | succ height =>
    have hc := child_windows lambda height start span hw
    have ha := rational_word lambda (span/2) (window_bounds lambda height start (span/2) hc.1).2.1
    have hcW := rational_word lambda (start+span/2)
      (window_bounds lambda height (start+span/2) (span/2) hc.2).1
    simp only [frame,Nat.succ_ne_zero,ite_false]
    omega

theorem bounded (W m lambda k Qv amount height : ℕ) (lo hi : ℚ) (n : Node height) (start span : ℚ)
    (hh : height≤lambda+1) (hw : Window lambda height start span)
    (hl : Bounded lambda lo) (hr : Bounded lambda hi) :
    peak W (GeneralPaperPreparedPowers.prepare lambda k) lo hi amount height n start span≤
      (height+1)*coefficient W m lambda k Qv amount := by
  induction height generalizing start span with
  | zero =>
    have hf := frame_bound W m lambda k Qv amount 0 lo hi start span hh hw hl hr
    have hs := result_bound W m lambda k Qv lo hi amount 0 n start span hh
      (GeneralPaperRangeUpdateBitPrice.span_positive lambda 0 start span hw)
    rw [peak.eq_def]
    dsimp only
    split <;> (try split) <;> unfold coefficient <;> omega
  | succ height ih =>
    have hf := frame_bound W m lambda k Qv amount (height+1) lo hi start span hh hw hl hr
    have hs := result_bound W m lambda k Qv lo hi amount (height+1) n start span hh
      (GeneralPaperRangeUpdateBitPrice.span_positive lambda (height+1) start span hw)
    have hc := child_windows lambda height start span hw
    have hLeft := ih (leftChild n) start (span/2) (by omega) hc.1
    have hRight := ih (rightChild n) (start+span/2) (span/2) (by omega) hc.2
    have hRetain := result_bound W m lambda k Qv lo hi amount height (leftChild n) start (span/2)
      (by omega) (GeneralPaperRangeUpdateBitPrice.span_positive lambda height start (span/2) hc.1)
    have hLive : frame W amount (height+1) lo hi start span+
        resultBits W (GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k)
          lo hi amount (height+1) n start span)≤coefficient W m lambda k Qv amount := by
      unfold coefficient
      omega
    have hFrame : frame W amount (height+1) lo hi start span+
        resultBits W (GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k)
          lo hi amount height (leftChild n) start (span/2))≤coefficient W m lambda k Qv amount := by
      unfold coefficient
      omega
    rw [peak.eq_def]
    dsimp only
    split
    · nlinarith only [hLive,Nat.zero_le height]
    · split
      · nlinarith only [hLive,Nat.zero_le height]
      · refine max_le ?_ ?_
        · nlinarith only [hLive,Nat.zero_le height]
        · rw [←Nat.add_max_add_left]
          refine max_le ?_ ?_
          · have h0 : frame W amount (height+1) lo hi start span≤coefficient W m lambda k Qv amount := by omega
            nlinarith only [h0,hLeft]
          · nlinarith only [hFrame,hRight]

theorem root (W m lambda k Qv lo hi amount height : ℕ) (n : Node height)
    (hh : height≤lambda+1) (hl : lo≤2^(lambda+1)) (hr : hi≤2^(lambda+1)) :
    peak W (GeneralPaperPreparedPowers.prepare lambda k) (lo:ℚ) hi amount height n 0 ((2:ℚ)^height)≤
      (height+1)*coefficient W m lambda k Qv amount :=
  bounded W m lambda k Qv amount height (lo:ℚ) hi n 0 ((2:ℚ)^height) hh
    (root_window lambda height hh) ⟨lo,rfl,hl⟩ ⟨hi,rfl,hr⟩

end Blotto.GeneralPaperRangeTraversalStorage

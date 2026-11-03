import Blotto.GeneralPaperRangeUpdateArithmetic

/-! Reached dyadic windows retain integral endpoints. Every endpoint and
midpoint is within the existing root code span, so full rational geometry
words follow from lambda rather than a supplied encoding/magnitude oracle.
-/
namespace Blotto.GeneralPaperRangeGeometryPrice
open GeneralPaperRangeUpdateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def Bounded (lambda : ℕ) (q : ℚ) : Prop := ∃ n : ℕ,q=(n:ℚ) ∧ n≤2^(lambda+1)

def Window (lambda height : ℕ) (start span : ℚ) : Prop :=
  ∃ n : ℕ,start=(n:ℚ) ∧ span=(2:ℚ)^height ∧ n+2^height≤2^(lambda+1)

theorem natural_word (lambda n : ℕ) (h : n≤2^(lambda+1)) :
    1+binaryWordWidth n≤GeneralPaperDecoderControls.operandWidth lambda := by
  have hn := binaryWordWidth_mono h
  have hp := GeneralPaperNatPowerOperands.power_width 2 (lambda+1)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  unfold GeneralPaperDecoderControls.operandWidth
  omega

theorem rational_word (lambda : ℕ) (q : ℚ) (h : Bounded lambda q) :
    rationalWordWidth q≤GeneralPaperDecoderControls.operandWidth lambda := by
  obtain ⟨n,rfl,hn⟩ := h
  have hw := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height n)
  have hnW := binaryWordWidth_mono hn
  have hp := GeneralPaperNatPowerOperands.power_width 2 (lambda+1)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  unfold GeneralPaperDecoderControls.operandWidth
  omega

theorem window_bounds (lambda height : ℕ) (start span : ℚ) (h : Window lambda height start span) :
    Bounded lambda start ∧ Bounded lambda span ∧ Bounded lambda (start+span) := by
  obtain ⟨n,rfl,hs,hn⟩ := h
  have hPos := Nat.two_pow_pos height
  refine ⟨⟨n,rfl,by omega⟩,⟨2^height,?_,by omega⟩,⟨n+2^height,?_,hn⟩⟩
  · rw [hs]
    norm_cast
  · rw [hs]
    norm_cast

theorem root_window (lambda height : ℕ) (hHeight : height≤lambda+1) : Window lambda height 0 ((2:ℚ)^height) := by
  refine ⟨0,by norm_num,rfl,?_⟩
  simpa only [Nat.zero_add] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hHeight

theorem child_windows (lambda height : ℕ) (start span : ℚ) (h : Window lambda (height+1) start span) :
    Window lambda height start (span/2) ∧ Window lambda height (start+span/2) (span/2) := by
  obtain ⟨n,rfl,hs,hn⟩ := h
  have hHalf : span/2=(2:ℚ)^height := by rw [hs,pow_succ]; ring
  have hPow : 2^(height+1)=2^height+2^height := by rw [pow_succ]; omega
  rw [hPow] at hn
  have hPos := Nat.two_pow_pos height
  constructor
  · exact ⟨n,rfl,hHalf,by omega⟩
  · refine ⟨n+2^height,?_,hHalf,by omega⟩
    rw [hHalf]
    norm_cast

theorem window_words (lambda height : ℕ) (start span : ℚ) (h : Window lambda height start span) :
    rationalWordWidth start≤GeneralPaperDecoderControls.operandWidth lambda ∧
    rationalWordWidth span≤GeneralPaperDecoderControls.operandWidth lambda ∧
    rationalWordWidth (start+span)≤GeneralPaperDecoderControls.operandWidth lambda := by
  have hb := window_bounds lambda height start span h
  exact ⟨rational_word lambda start hb.1,rational_word lambda span hb.2.1,rational_word lambda (start+span) hb.2.2⟩

theorem guard_work (price : ℕ → ℕ) (hMono : Monotone price) (W lambda height : ℕ) (start span a b : ℚ)
    (hWindow : Window lambda height start span) (ha : Bounded lambda a) (hb : Bounded lambda b) :
    guardCost price W start span a b≤4*price (GeneralPaperDecoderControls.operandWidth lambda)+64*W := by
  have hw := window_words lambda height start span hWindow
  have haW := rational_word lambda a ha
  have hbW := rational_word lambda b hb
  have hAdd := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun x y => x+y) start span
    (GeneralPaperDecoderControls.operandWidth lambda) hw.1 hw.2.1 hw.2.2
  have hA := hMono (max_le haW hw.1)
  have hB := hMono (max_le hw.2.2 hbW)
  unfold guardCost RationalExpression.pairWidth
  omega

theorem split_work (price : ℕ → ℕ) (hMono : Monotone price) (W lambda height : ℕ) (start span : ℚ)
    (hWindow : Window lambda (height+1) start span) (hHeight : height+1≤lambda+1) :
    splitCost price W height start span≤6*price (GeneralPaperDecoderControls.operandWidth lambda)+64*W := by
  have hp := window_words lambda (height+1) start span hWindow
  have children := child_windows lambda height start span hWindow
  have hl := window_words lambda height start (span/2) children.1
  have hr := window_words lambda height (start+span/2) (span/2) children.2
  have hTwo : 2≤2^(lambda+1) := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤lambda+1 by omega)
    simpa only [pow_one] using h
  have h2 := rational_word lambda 2 ⟨2,by norm_num,hTwo⟩
  have hHalf := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun x y => x/y) span 2
    (GeneralPaperDecoderControls.operandWidth lambda) hp.2.1 h2 hl.2.1
  have hStart := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun x y => x+y) start (span/2)
    (GeneralPaperDecoderControls.operandWidth lambda) hp.1 hl.2.1 hr.1
  have hHeightCost := GeneralPaperDecoderControls.metadata_binary price hMono lambda (fun x y => x-y) (height+1) 1
    (by unfold GeneralPaperDecoderControls.metadataCap; omega)
    (by unfold GeneralPaperDecoderControls.metadataCap; omega)
    (by unfold GeneralPaperDecoderControls.metadataCap; omega)
  unfold splitCost
  omega

end Blotto.GeneralPaperRangeGeometryPrice

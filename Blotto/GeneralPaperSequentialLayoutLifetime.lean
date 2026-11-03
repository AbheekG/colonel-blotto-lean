import Blotto.GeneralPaperSelectedTemporaryOwnerRates

/-! Saved activations of the actual sequential layout. Every activation
includes source/next cursors, encoded-pointer work, arithmetic scratch,
recursive return cursors/prices and partial/full price accumulations.
Output region cells share tails and are counted once by the enclosing
owner window. Existing word-encoding lifetime bounds include primitive
scratch and all reached quotient/remainder activations. -/
namespace Blotto.GeneralPaperSequentialLayoutLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperSequentialLayout (run stepPrice)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def controlCap (S A M Q : ℕ) : ℕ := S + A + M + Q + 1

def controls (model : RationalCostModel) (S A start size : ℕ) (sizes : List ℕ) : List ℕ :=
  let encoded := GeneralPaperStoredWordEncoding.word model S A start
  let price := GeneralPaperEqualAddressConstruction.price model S start size (start + size)
  let child := run model S A (start + size) sizes
  [S,A,start,size,start + size,encoded.2,price,encoded.2 + price,child.2.1,child.2.2,
    (run model S A start (size :: sizes)).2.2]

theorem controls_bounded (model : RationalCostModel) (S A start size M Q : ℕ) (sizes : List ℕ)
    (hEnd : start + size + sizes.sum ≤ M) (hWork : (run model S A start (size :: sizes)).2.2 ≤ Q) :
    ∀ x ∈ controls model S A start size sizes,x ≤ controlCap S A M Q := by
  have hCursor := GeneralPaperSequentialLayout.cursor model S A (start + size) sizes
  have hWhole := hWork
  change (GeneralPaperStoredWordEncoding.word model S A start).2 +
    GeneralPaperEqualAddressConstruction.price model S start size (start + size) +
    (run model S A (start + size) sizes).2.2 + 64 * (S + A + 1) ≤ Q at hWork
  intro x hx
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
  unfold controlCap
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def localFoot (model : RationalCostModel) (S A start size : ℕ) (sizes : List ℕ) : ℕ :=
  fields S (controls model S A start size sizes) + A + 192 * S +
    GeneralPaperWordEncodingLifetime.window model S A start +
    GeneralPaperAddressConstructionLifetime.scalarFoot model S start size (start + size)

def localBound (model : RationalCostModel) (S A M Q : ℕ) : ℕ :=
  11 * (natBits (controlCap S A M Q) + S) + 224 * S + A +
    GeneralPaperWordEncodingLifetime.windowProfile model S A A + 32 * stepPrice model S A

theorem local_bound (model : RationalCostModel) (S A start size M Q : ℕ) (sizes : List ℕ)
    (hA : 0 < A) (hCap : start + size + sizes.sum < 2 ^ A)
    (hEnd : start + size + sizes.sum ≤ M) (hWork : (run model S A start (size :: sizes)).2.2 ≤ Q) :
    localFoot model S A start size sizes ≤ localBound model S A M Q := by
  have hControls := fields_bound S (natBits (controlCap S A M Q)) (controls model S A start size sizes) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono (controls_bounded model S A start size M Q sizes hEnd hWork x hx)) 1)
  change fields S (controls model S A start size sizes) ≤ 11 * (natBits (controlCap S A M Q) + S) + 32 * S at hControls
  have hStart := binaryWordWidth_le_of_lt_pow hA (show start < 2 ^ A by omega)
  have hSize := binaryWordWidth_le_of_lt_pow hA (show size < 2 ^ A by omega)
  have hNext := binaryWordWidth_le_of_lt_pow hA (show start + size < 2 ^ A by omega)
  have hEncoded := GeneralPaperWordEncodingLifetime.word_bound model S A start A hStart
  have hScalar := GeneralPaperAddressConstructionLifetime.scalar_bound model S start size (start + size)
  have hPrice := GeneralPaperEqualAddressConstruction.price_work model S start size (start + size) (A + 1)
    (by change 1 + binaryWordWidth start ≤ _; omega)
    (by change 1 + binaryWordWidth size ≤ _; omega)
    (by change 1 + binaryWordWidth (start + size) ≤ _; omega)
  have hStep : GeneralPaperEqualAddressConstruction.price model S start size (start + size) ≤ stepPrice model S A := by
    unfold stepPrice
    omega
  have hScratch := hScalar.trans (Nat.mul_le_mul_left 32 hStep)
  unfold localFoot localBound
  omega

def baseFoot (model : RationalCostModel) (S A start : ℕ) : ℕ :=
  fields S [S,A,start,(run model S A start []).2.2] + 64 * S

theorem base_bound (model : RationalCostModel) (S A start M Q : ℕ)
    (hEnd : start ≤ M) (hWork : (run model S A start []).2.2 ≤ Q) :
    baseFoot model S A start ≤ localBound model S A M Q := by
  have hFields := fields_bound S (natBits (controlCap S A M Q)) [S,A,start,(run model S A start []).2.2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold controlCap
    rcases hx with rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 4 * (natBits (controlCap S A M Q) + S) + 32 * S at hFields
  unfold baseFoot localBound
  omega

def frames (model : RationalCostModel) (S A : ℕ) : ℕ → List ℕ → ℕ
  | start,[] => baseFoot model S A start
  | start,size :: sizes => localFoot model S A start size sizes + frames model S A (start + size) sizes

theorem frames_bound (model : RationalCostModel) (S A start M Q : ℕ) (sizes : List ℕ)
    (hA : 0 < A) (hCap : start + sizes.sum < 2 ^ A) (hEnd : start + sizes.sum ≤ M)
    (hWork : (run model S A start sizes).2.2 ≤ Q) :
    frames model S A start sizes ≤ (sizes.length + 1) * localBound model S A M Q := by
  induction sizes generalizing start with
  | nil =>
    simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using
      base_bound model S A start M Q (by simpa only [List.sum_nil,Nat.add_zero] using hEnd) hWork
  | cons size sizes ih =>
    have hTotal : start + size + sizes.sum < 2 ^ A := by simpa only [List.sum_cons,Nat.add_assoc] using hCap
    have hTotalEnd : start + size + sizes.sum ≤ M := by simpa only [List.sum_cons,Nat.add_assoc] using hEnd
    have hLocal := local_bound model S A start size M Q sizes hA hTotal hTotalEnd hWork
    have hChildWork : (run model S A (start + size) sizes).2.2 ≤ Q := by
      change (GeneralPaperStoredWordEncoding.word model S A start).2 +
        GeneralPaperEqualAddressConstruction.price model S start size (start + size) +
        (run model S A (start + size) sizes).2.2 + 64 * (S + A + 1) ≤ Q at hWork
      omega
    have hChild := ih (start + size) hTotal hTotalEnd hChildWork
    simp only [frames,List.length_cons]
    nlinarith only [hLocal,hChild]

theorem reached_work (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) (depth : ℕ) :
    (run model S A (start + (sizes.take depth).sum) (sizes.drop depth)).2.2 ≤
      (run model S A start sizes).2.2 := by
  induction sizes generalizing start depth with
  | nil => simp only [List.take_nil,List.drop_nil,List.sum_nil,Nat.add_zero,le_refl]
  | cons size sizes ih =>
    cases depth with
    | zero => simp only [List.take_zero,List.drop_zero,List.sum_nil,Nat.add_zero,le_refl]
    | succ depth =>
      have h := ih (start + size) depth
      have hStep : (run model S A (start + size) sizes).2.2 ≤ (run model S A start (size :: sizes)).2.2 := by
        change _ ≤ (GeneralPaperStoredWordEncoding.word model S A start).2 +
          GeneralPaperEqualAddressConstruction.price model S start size (start + size) +
          (run model S A (start + size) sizes).2.2 + 64 * (S + A + 1)
        omega
      simpa only [List.take_succ_cons,List.drop_succ_cons,List.sum_cons,Nat.add_assoc] using h.trans hStep

theorem reached_frames (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) (depth : ℕ) :
    frames model S A (start + (sizes.take depth).sum) (sizes.drop depth) ≤ frames model S A start sizes := by
  induction sizes generalizing start depth with
  | nil => simp only [List.take_nil,List.drop_nil,List.sum_nil,Nat.add_zero,le_refl]
  | cons size sizes ih =>
    cases depth with
    | zero => simp only [List.take_zero,List.drop_zero,List.sum_nil,Nat.add_zero,le_refl]
    | succ depth =>
      have h := ih (start + size) depth
      have hStep : frames model S A (start + size) sizes ≤ frames model S A start (size :: sizes) := by
        change _ ≤ localFoot model S A start size sizes + frames model S A (start + size) sizes
        omega
      simpa only [List.take_succ_cons,List.drop_succ_cons,List.sum_cons,Nat.add_assoc] using h.trans hStep

theorem reached_output (model : RationalCostModel) (S A start : ℕ) (sizes : List ℕ) (depth : ℕ) :
    (run model S A (start + (sizes.take depth).sum) (sizes.drop depth)).1 =
      (run model S A start sizes).1.drop depth := by
  induction sizes generalizing start depth with
  | nil => simp only [List.take_nil,List.drop_nil,List.sum_nil,Nat.add_zero,run]
  | cons size sizes ih =>
    cases depth with
    | zero => simp only [List.take_zero,List.drop_zero,List.sum_nil,Nat.add_zero]
    | succ depth =>
      simpa only [List.take_succ_cons,List.drop_succ_cons,List.sum_cons,Nat.add_assoc,run] using
        ih (start + size) depth

theorem reached_controls_bounded (model : RationalCostModel) (S A start M Q : ℕ) (sizes : List ℕ)
    (depth size : ℕ) (tail : List ℕ) (hDrop : sizes.drop depth = size :: tail)
    (hEnd : start + sizes.sum ≤ M) (hWork : (run model S A start sizes).2.2 ≤ Q) :
    ∀ x ∈ controls model S A (start + (sizes.take depth).sum) size tail,x ≤ controlCap S A M Q := by
  have hSplit : (sizes.take depth).sum + (sizes.drop depth).sum = sizes.sum := by
    rw [← List.sum_append,List.take_append_drop]
  have hReached := (reached_work model S A start sizes depth).trans hWork
  rw [hDrop] at hReached hSplit
  exact controls_bounded model S A _ size M Q tail (by simp only [List.sum_cons] at hSplit; omega) hReached

end Blotto.GeneralPaperSequentialLayoutLifetime

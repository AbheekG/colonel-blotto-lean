import Blotto.BinaryPRGNormalizedRequest

/-! Successful native frame reads derive physical word widths, row count and
row-width sums from incoming length. These certificates apply before promise
checking and do not assume a legal game. They close the decoded-word aggregate
input bound without a caller-supplied dimension/width/source oracle. -/

namespace Blotto.BinaryDecodedInputLength
open BinaryRationalNormalization BinaryPRGFrame

theorem read_payload_consumed (bits payload suffix : List Bool)
    (h : PositiveBinaryWord.readPayload bits = some (payload,suffix)) : payload.length + suffix.length ≤ bits.length := by
  rw [PositiveBinaryWord.readPayload_refines] at h
  unfold PositiveBinaryWord.readPayloadNumeric at h
  cases hs : BinaryNatFrame.scanWidth 0 bits with
  | none => rw [hs,Option.bind_none] at h; cases h
  | some pair =>
      rcases pair with ⟨count,rest⟩
      rw [hs,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hl := BinaryNatFrame.scanWidth_length 0 bits count rest hs
        simp only [List.length_take,List.length_drop]
        omega
      · cases h

theorem read_word_consumed (bits : List Bool) (parsed : {word : SignedWord // BinaryRationalEncoding.CanonicalWord word} × List Bool)
    (h : (BinaryCanonicalFrameWork.read bits).1 = some parsed) : width parsed.1.val + parsed.2.length ≤ bits.length := by
  cases bits with
  | nil => cases h
  | cons sign rest =>
      unfold BinaryCanonicalFrameWork.read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i numerator hn
        have hN := read_payload_consumed rest numerator.1 numerator.2 hn
        split at h
        · cases h
        · rename_i denominator hd
          have hD := read_payload_consumed numerator.2 denominator.1 denominator.2 hd
          split at h
          · cases Option.some.inj h
            have hw := BinaryPRGPreparationWork.canonicalize_stored_width (⟨sign,numerator.1,denominator.1⟩ : SignedWord)
            change width (BinaryRationalOpcode.canonicalize _) + denominator.2.length ≤ _
            have hRaw : width (⟨sign,numerator.1,denominator.1⟩ : SignedWord) + denominator.2.length ≤ (sign :: rest).length := by
              unfold width
              simp only [List.length_cons]
              omega
            omega
          · cases h

theorem read_word_width (bits : List Bool) (parsed : {word : SignedWord // BinaryRationalEncoding.CanonicalWord word} × List Bool)
    (h : (BinaryCanonicalFrameWork.read bits).1 = some parsed) : width parsed.1.val ≤ bits.length := by
  cases bits with
  | nil => cases h
  | cons sign rest =>
      unfold BinaryCanonicalFrameWork.read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i numerator hn
        have hN := BinaryPRGHeaderFrame.readPayload_length_bound rest numerator.1 numerator.2 hn
        have hSuffix := BinaryCanonicalFrameWork.payload_suffix_lt rest numerator.1 numerator.2 hn
        split at h
        · cases h
        · rename_i denominator hd
          have hD := BinaryPRGHeaderFrame.readPayload_length_bound numerator.2 denominator.1 denominator.2 hd
          split at h
          · cases Option.some.inj h
            have hw := BinaryPRGPreparationWork.canonicalize_stored_width (⟨sign,numerator.1,denominator.1⟩ : SignedWord)
            change width (BinaryRationalOpcode.canonicalize _) ≤ _
            exact hw.trans (max_le (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega))
          · cases h

theorem read_row_count (n : ℕ) (bits : List Bool) (parsed : Words n × List Bool)
    (h : (BinaryCanonicalRowReadWork.read n bits).1 = some parsed) : n ≤ bits.length := by
  induction n generalizing bits with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      unfold BinaryCanonicalRowReadWork.read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i first hf
        obtain ⟨later,hl,hOut⟩ := Option.map_eq_some_iff.mp h
        have hc := ih first.2 later hl
        have hd := BinaryCanonicalFrameWork.read_suffix_lt bits first hf
        omega

theorem read_row_widths (n : ℕ) (bits : List Bool) (parsed : Words n × List Bool)
    (h : (BinaryCanonicalRowReadWork.read n bits).1 = some parsed) : ∀ word ∈ parsed.1.row, width word ≤ bits.length := by
  induction n generalizing bits with
  | zero =>
      have he : parsed.1.row = [] := List.eq_nil_of_length_eq_zero parsed.1.length
      simp [he]
  | succ n ih =>
      unfold BinaryCanonicalRowReadWork.read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i first hf
        obtain ⟨later,hl,hOut⟩ := Option.map_eq_some_iff.mp h
        subst parsed
        intro word hw
        rcases List.mem_cons.mp hw with he | ht
        · subst word; exact read_word_width bits first hf
        · exact (ih first.2 later hl word ht).trans (BinaryCanonicalFrameWork.read_suffix_lt bits first hf).le

theorem parsed_sizes (bits : List Bool) (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed) :
    parsed.1.1 ≤ bits.length ∧ width parsed.1.2.game.input.a ≤ bits.length ∧ width parsed.1.2.game.input.b ≤ bits.length ∧
      ∀ j, width (parsed.1.2.game.input.values.read j) ≤ bits.length := by
  unfold BinaryPRGNormalizedFrameWork.read at h
  split at h
  · cases h
  · rename_i dim hd
    have hDim := BinaryPRGNormalizedFrameWork.header_suffix_length bits dim hd
    dsimp only at h
    split at h
    · cases h
    · rename_i first hf
      have hFirst := (BinaryCanonicalFrameWork.read_suffix_lt dim.2 first hf).le.trans hDim
      have hA := (read_word_width dim.2 first hf).trans hDim
      split at h
      · cases h
      · rename_i second hs
        have hSecond := (BinaryCanonicalFrameWork.read_suffix_lt first.2 second hs).le.trans hFirst
        have hB := (read_word_width first.2 second hs).trans hFirst
        obtain ⟨words,hw,hOut⟩ := Option.map_eq_some_iff.mp h
        subst parsed
        refine ⟨(read_row_count dim.1.1 second.2 words hw).trans hSecond,hA,hB,?_⟩
        intro j
        have hc := read_row_widths dim.1.1 second.2 words hw
        have hMem : words.1.table.read j ∈ words.1.row := by
          unfold BinaryPRGFrame.Words.table FixedArrayTable.read
          simp only [List.getElem_toArray]
          exact List.getElem_mem _
        exact (hc _ hMem).trans hSecond

theorem read_row_consumed (n : ℕ) (bits : List Bool) (parsed : Words n × List Bool)
    (h : (BinaryCanonicalRowReadWork.read n bits).1 = some parsed) :
    (parsed.1.row.map width).sum + parsed.2.length ≤ bits.length := by
  induction n generalizing bits with
  | zero =>
      cases Option.some.inj h
      simp
  | succ n ih =>
      unfold BinaryCanonicalRowReadWork.read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i first hf
        obtain ⟨later,hl,hOut⟩ := Option.map_eq_some_iff.mp h
        have hc := ih first.2 later hl
        have hd := read_word_consumed bits first hf
        subst parsed
        simp only [List.map_cons,List.sum_cons]
        omega

theorem table_width_sum {n : ℕ} (words : Words n) :
    (∑ j, width (words.table.read j)) = (words.row.map width).sum := by
  rcases words with ⟨row,hl,hc⟩
  subst n
  simp only [Words.table,FixedArrayTable.read,List.getElem_toArray]
  change (∑ j : Fin row.length, width row[j.val]) = (row.map width).sum
  rw [← List.sum_ofFn]
  change (List.ofFn (width ∘ fun j : Fin row.length => row[j.val])).sum = (row.map width).sum
  rw [← List.map_ofFn,List.ofFn_getElem]

theorem parsed_widths_consumed (bits : List Bool) (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed) :
    BinaryPRGPreparationWork.storedInputWidth parsed.1.2.game.input + parsed.2.length ≤ bits.length + 2 := by
  unfold BinaryPRGNormalizedFrameWork.read at h
  split at h
  · cases h
  · rename_i dim hd
    have hDim := BinaryPRGNormalizedFrameWork.header_suffix_length bits dim hd
    dsimp only at h
    split at h
    · cases h
    · rename_i first hf
      have hFirst := read_word_consumed dim.2 first hf
      split at h
      · cases h
      · rename_i second hs
        have hSecond := read_word_consumed first.2 second hs
        obtain ⟨words,hw,hOut⟩ := Option.map_eq_some_iff.mp h
        have hWords := read_row_consumed dim.1.1 second.2 words hw
        subst parsed
        change width first.1.val + width second.1.val + (∑ j, width (words.1.table.read j)) + 2 + words.2.length ≤ bits.length + 2
        rw [table_width_sum]
        omega

def widthBound (length : ℕ) : ℕ := length + 2

theorem parsed_storedInputWidth (bits : List Bool) (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed) :
    BinaryPRGPreparationWork.storedInputWidth parsed.1.2.game.input ≤ widthBound bits.length := by
  have hc := parsed_widths_consumed bits parsed h
  unfold widthBound
  omega

def preparationEnvelope (n S : ℕ) : ℕ :=
  (2 * n + 1) * BinaryPRGPromiseWork.operationPrice (12 * (S + n + 3) + 10) +
    (2 * n + 5) * BinaryPRGPromiseWork.comparisonPrice (12 * (S + n + 3) + 10) +
      (1 + 2 * n) * (12000 * (3 * S + 2) ^ 3)

theorem preparationEnvelope_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    preparationEnvelope n S ≤ preparationEnvelope m T := by
  unfold preparationEnvelope BinaryPRGPromiseWork.operationPrice BinaryPRGPromiseWork.comparisonPrice
  gcongr

theorem preparation_bound_eq {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    BinaryPRGMeasuredPreparation.bound input = preparationEnvelope n (BinaryPRGPreparationWork.storedInputWidth input) := rfl

def preparationFrameBound (length : ℕ) : ℕ := preparationEnvelope length (widthBound length)

theorem parsed_preparation_bound (bits : List Bool) (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed) :
    BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input ≤ preparationFrameBound bits.length := by
  rw [preparation_bound_eq]
  exact preparationEnvelope_mono (parsed_sizes bits parsed h).1 (parsed_storedInputWidth bits parsed h)

def requestInputBound (length : ℕ) : ℕ := BinaryPRGNormalizedFrameWork.bound length + preparationFrameBound length

theorem read_request_input_bound (bits : List Bool) :
    (BinaryPRGNormalizedRequest.read bits).2.recorded ≤ requestInputBound bits.length := by
  have hr := BinaryPRGNormalizedRequest.read_recorded_bound bits
  cases he : (BinaryPRGNormalizedFrameWork.read bits).1 with
  | none =>
      simp only [he,Nat.add_zero] at hr
      exact hr.trans (Nat.le_add_right _ _)
  | some parsed =>
      simp only [he] at hr
      exact hr.trans (Nat.add_le_add_left (parsed_preparation_bound bits parsed he) _)

theorem run_request_input_bound (rich : Bool) (frame seed : List Bool) :
    (BinaryPRGNormalizedRequest.run rich frame seed).2.recorded ≤ requestInputBound frame.length :=
  read_request_input_bound frame

end Blotto.BinaryDecodedInputLength

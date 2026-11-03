import Blotto.BinaryStoredDimensionHeaderLifetime
import Blotto.BinaryStoredDimensionRowLifetime
import Blotto.BinaryLifetimeListArray
import Blotto.BinaryPRGStoredDimensionFrame

/-! Complete original-game parsing joins actual retained Boolean header,
both budget words, stored-countdown row parsing and successful array packing.
Only the returned row supplies the numeric dimension. Every original parsed
field/header/suffix/rejection is exact; promise/numerical/accuracy preparation
and subsequent sampling are not yet part of this input trace. -/
namespace Blotto.BinaryPRGGameFrameLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def packWithTable {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool)
    (values : FixedArrayTable rest.1.row.length SignedWord) (hValues : ∀ j,CanonicalWord (values.read j))
    (hRows : rest.1.row = List.ofFn values.read) :
    (Σ m,BinaryPRGHeaderFrame.Parsed m) × List Bool :=
  let m := rest.1.row.length
  let retained : BinaryPRGHeaderFrame.Header m :=
    ⟨header.bytes,(by change header.bytes = BinaryNatFrame.encode rest.1.row.length
                      rw [rest.1.length]; exact header.correct),header.visits,header.sourceWidth,header.visits_bound⟩
  (⟨m,⟨⟨⟨first.val,second.val,values⟩,first.property,second.property,hValues⟩,retained,
    rest.1.row,rfl,hRows⟩⟩,rest.2)

theorem packWithTable_state {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool)
    (values : FixedArrayTable rest.1.row.length SignedWord) (hValues : ∀ j,CanonicalWord (values.read j))
    (hRows : rest.1.row = List.ofFn values.read)
    (h : values = ⟨rest.1.row.toArray,by simp⟩) :
    packWithTable header first second rest values hValues hRows = BinaryPRGStoredDimensionFrame.pack header first second rest := by
  cases h
  rfl

theorem parsed_table_canonical {n : ℕ} (rest : Words n × List Bool) :
    ∀ j,CanonicalWord ((BinaryLifetimeListArray.tableWithTrace rest.1.row).1.read j) := by
  rw [BinaryLifetimeListArray.tableWithTrace_state]
  intro j
  change CanonicalWord (rest.1.row.toArray[j.val]'_)
  rw [List.getElem_toArray]
  exact rest.1.canonical _ (List.getElem_mem _)

def packWithTrace {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    ((Σ m,BinaryPRGHeaderFrame.Parsed m) × List Bool) × Trace :=
  let values := BinaryLifetimeListArray.tableWithTrace rest.1.row
  (packWithTable header first second rest values.1 (parsed_table_canonical rest)
    (by
      rw [BinaryLifetimeListArray.tableWithTrace_state]
      apply List.ext_getElem
      · simp
      · intro i hLeft hRight
        simp only [List.getElem_ofFn,FixedArrayTable.read,List.getElem_toArray]),
    wrap 32 (rest.1.row.length+2) [values.2])

theorem packWithTrace_state {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    (packWithTrace header first second rest).1 = BinaryPRGStoredDimensionFrame.pack header first second rest :=
  packWithTable_state header first second rest _ (parsed_table_canonical rest)
    (by
      rw [BinaryLifetimeListArray.tableWithTrace_state]
      apply List.ext_getElem
      · simp
      · intro i hLeft hRight
        simp only [List.getElem_ofFn,FixedArrayTable.read,List.getElem_toArray])
    (BinaryLifetimeListArray.tableWithTrace_state rest.1.row)

theorem packWithTrace_usage {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    usage (packWithTrace header first second rest).2 ≤ 2*(rest.1.row.length+2)^2+64 := by
  have hArray := BinaryLifetimeListArray.tableWithTrace_usage rest.1.row
  have hw := wrap_usage 32 (rest.1.row.length+2) [(BinaryLifetimeListArray.tableWithTrace rest.1.row).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (packWithTrace header first second rest).2 ≤ _ at hw
  nlinarith

def readWithTrace (bits : List Bool) : Option ((Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool) × Trace :=
  let dimension := BinaryStoredDimensionHeaderLifetime.readWithTrace bits
  match dimension.1 with
  | none => (none,wrap 16 2 [dimension.2])
  | some raw =>
      let first := BinaryCanonicalFrameLifetime.readWithTrace raw.2
      match first.1 with
      | none => (none,wrap 24 2 [dimension.2,first.2])
      | some firstWord =>
          let second := BinaryCanonicalFrameLifetime.readWithTrace firstWord.2
          match second.1 with
          | none => (none,wrap 32 2 [dimension.2,first.2,second.2])
          | some secondWord =>
              let words := BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload secondWord.2
              match words.1 with
              | none => (none,wrap 40 2 [dimension.2,first.2,second.2,words.2])
              | some rest =>
                  let packed := packWithTrace raw.1.typed firstWord.1 secondWord.1 rest
                  (some packed.1,wrap 80 (raw.1.payload.length+8) [dimension.2,first.2,second.2,words.2,packed.2])

theorem readWithTrace_state (bits : List Bool) :
    (readWithTrace bits).1 = (BinaryPRGStoredDimensionFrame.read bits).1 := by
  unfold readWithTrace BinaryPRGStoredDimensionFrame.read
  dsimp only
  rw [BinaryStoredDimensionHeaderLifetime.readWithTrace_state]
  cases hd : (BinaryStoredDimensionHeader.read bits).1 with
  | none => rfl
  | some raw =>
      dsimp only
      rw [BinaryCanonicalFrameLifetime.readWithTrace_state]
      cases hf : (BinaryCanonicalFrameWork.read raw.2).1 with
      | none => rfl
      | some first =>
          dsimp only
          rw [BinaryCanonicalFrameLifetime.readWithTrace_state]
          cases hs : (BinaryCanonicalFrameWork.read first.2).1 with
          | none => rfl
          | some second =>
              dsimp only
              rw [BinaryStoredDimensionRowLifetime.readWithTrace_state]
              cases (BinaryStoredDimensionRow.read raw.1.payload second.2).1 with
              | none => rfl
              | some rest => simp only [Option.map_some,packWithTrace_state]

theorem readWithTrace_original (bits : List Bool) : (readWithTrace bits).1 = BinaryPRGHeaderFrame.read bits :=
  (readWithTrace_state bits).trans (BinaryPRGStoredDimensionFrame.read_state bits)

def envelope (length : ℕ) : ℕ :=
  320*(length+1)+2*BinaryCanonicalFrameLifetime.envelope length+
    BinaryStoredDimensionRowLifetime.envelope length length+2*(length+2)^2+4*length+512

theorem readWithTrace_usage (bits : List Bool) : usage (readWithTrace bits).2 ≤ envelope bits.length := by
  have hDimension := BinaryStoredDimensionHeaderLifetime.readWithTrace_usage bits
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2]) ≤ _
    unfold envelope
    omega
  · rename_i raw hd
    have hOld := (BinaryStoredDimensionHeaderLifetime.readWithTrace_state bits).symm.trans hd
    have hPayload := BinaryStoredDimensionHeader.read_payload_length bits raw hOld
    have hRaw := BinaryStoredDimensionHeader.read_suffix_length bits raw hOld
    have hFirst := (BinaryCanonicalFrameLifetime.readWithTrace_usage raw.2).trans (BinaryCanonicalFrameLifetime.envelope_mono hRaw)
    split
    · have hw := wrap_usage 24 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
        (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
        (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2]) ≤ _
      unfold envelope
      omega
    · rename_i first hf
      have hFirstLen := (BinaryCanonicalFrameLifetime.read_suffix_lt raw.2 first hf).le.trans hRaw
      have hSecond := (BinaryCanonicalFrameLifetime.readWithTrace_usage first.2).trans (BinaryCanonicalFrameLifetime.envelope_mono hFirstLen)
      split
      · have hw := wrap_usage 32 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
          (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 32 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
          (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2]) ≤ _
        unfold envelope
        omega
      · rename_i second hs
        have hSecondLen := (BinaryCanonicalFrameLifetime.read_suffix_lt first.2 second hs).le.trans hFirstLen
        have hRow := (BinaryStoredDimensionRowLifetime.readWithTrace_usage raw.1.payload second.2).trans
          (BinaryStoredDimensionRowLifetime.envelope_mono hPayload hSecondLen)
        split
        · have hw := wrap_usage 40 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
            (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2,
            (BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload second.2).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          change usage (wrap 40 2 [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
            (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2,
            (BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload second.2).2]) ≤ _
          unfold envelope
          omega
        · rename_i rest hr
          have hCount := BinaryStoredDimensionRowLifetime.read_count_bound raw.1.payload second.2 rest hr
          have hLength : rest.1.row.length ≤ bits.length := by rw [rest.1.length]; exact hCount.trans hSecondLen
          have hPack := packWithTrace_usage raw.1.typed first.1 second.1 rest
          have hPackUpper := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 2) 2)
          have hw := wrap_usage 80 (raw.1.payload.length+8) [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
            (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2,
            (BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload second.2).2,
            (packWithTrace raw.1.typed first.1 second.1 rest).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          change usage (wrap 80 (raw.1.payload.length+8) [(BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2,
            (BinaryCanonicalFrameLifetime.readWithTrace raw.2).2,(BinaryCanonicalFrameLifetime.readWithTrace first.2).2,
            (BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload second.2).2,
            (packWithTrace raw.1.typed first.1 second.1 rest).2]) ≤ _
          unfold envelope
          omega

theorem envelope_polynomial (length : ℕ) : envelope length ≤ 10000*(length+2)^4 := by
  unfold envelope BinaryStoredDimensionRowLifetime.envelope BinaryCanonicalFrameLifetime.envelope
  nlinarith only [sq_nonneg (length:ℤ)]

theorem all_prefix (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+bits.length) (readWithTrace bits).2 steps ≤ borrowed+bits.length+envelope bits.length ∧
    framePeak ((readWithTrace bits).2.take steps) ≤ envelope bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage bits) _ steps

theorem all_prefix_polynomial (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+bits.length) (readWithTrace bits).2 steps ≤ borrowed+bits.length+10000*(bits.length+2)^4 ∧
    framePeak ((readWithTrace bits).2.take steps) ≤ 10000*(bits.length+2)^4 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ ((readWithTrace_usage bits).trans (envelope_polynomial bits.length)) _ steps

end Blotto.BinaryPRGGameFrameLifetime

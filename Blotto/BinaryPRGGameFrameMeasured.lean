import Blotto.BinaryStoredDimensionHeaderMeasured
import Blotto.BinaryStoredDimensionRowMeasured
import Blotto.BinaryLifetimeListArrayMeasured
import Blotto.BinaryPRGGameFrameLifetime

/-! Actual measured dimension, budgets, row and pinned array packing form
one game reader. All rejection branches and returned objects/traces refine
the old reader. Source work includes conservative array-copy slot charges;
native reference-bit transport, ownership and observer/allocator arithmetic
remain separate. Promise/numerical/accuracy preparation is still downstream. -/
namespace Blotto.BinaryPRGGameFrameMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def pack {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    (((Σ m,BinaryPRGHeaderFrame.Parsed m) × List Bool) × Trace) × ℕ :=
  let values := BinaryLifetimeListArrayMeasured.table rest.1.row
  have hValues : ∀ j,CanonicalWord (values.1.1.read j) := by
    dsimp only [values]
    rw [BinaryLifetimeListArrayMeasured.table_erases]
    exact BinaryPRGGameFrameLifetime.parsed_table_canonical rest
  have hRows : rest.1.row = List.ofFn values.1.1.read := by
    dsimp only [values]
    rw [BinaryLifetimeListArrayMeasured.table_erases,BinaryLifetimeListArray.tableWithTrace_state]
    apply List.ext_getElem
    · simp
    · intro i hLeft hRight
      simp only [List.getElem_ofFn,FixedArrayTable.read,List.getElem_toArray]
  ((BinaryPRGGameFrameLifetime.packWithTable header first second rest values.1.1 hValues hRows,
    wrap 32 (rest.1.row.length+2) [values.1.2]),values.2+4*rest.1.row.length+16)

theorem pack_erases {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    (pack header first second rest).1 = BinaryPRGGameFrameLifetime.packWithTrace header first second rest := by
  simp only [pack,BinaryPRGGameFrameLifetime.packWithTrace,BinaryLifetimeListArrayMeasured.table_erases]

theorem pack_work {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word}) (rest : Words n × List Bool) :
    (pack header first second rest).2 ≤ 64*(rest.1.row.length+1)^2 := by
  have ht := BinaryLifetimeListArrayMeasured.table_bound rest.1.row
  change (BinaryLifetimeListArrayMeasured.table rest.1.row).2+4*rest.1.row.length+16 ≤ _
  nlinarith

def read (bits : List Bool) : (Option ((Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool) × Trace) × ℕ :=
  let dimension := BinaryStoredDimensionHeaderMeasured.read bits
  match dimension.1.1 with
  | none => ((none,wrap 16 2 [dimension.1.2]),dimension.2+4)
  | some raw =>
      let first := BinaryCanonicalFrameMeasured.read raw.2
      match first.1.1 with
      | none => ((none,wrap 24 2 [dimension.1.2,first.1.2]),dimension.2+first.2+8)
      | some firstWord =>
          let second := BinaryCanonicalFrameMeasured.read firstWord.2
          match second.1.1 with
          | none => ((none,wrap 32 2 [dimension.1.2,first.1.2,second.1.2]),dimension.2+first.2+second.2+12)
          | some secondWord =>
              let words := BinaryStoredDimensionRowMeasured.read raw.1.payload secondWord.2
              match words.1.1 with
              | none => ((none,wrap 40 2 [dimension.1.2,first.1.2,second.1.2,words.1.2]),
                  dimension.2+first.2+second.2+words.2+16)
              | some rest =>
                  let packed := pack raw.1.typed firstWord.1 secondWord.1 rest
                  ((some packed.1.1,wrap 80 (raw.1.payload.length+8)
                    [dimension.1.2,first.1.2,second.1.2,words.1.2,packed.1.2]),
                    dimension.2+first.2+second.2+words.2+packed.2+20)

theorem read_erases (bits : List Bool) : (read bits).1 = BinaryPRGGameFrameLifetime.readWithTrace bits := by
  unfold read BinaryPRGGameFrameLifetime.readWithTrace
  dsimp only
  simp only [BinaryStoredDimensionHeaderMeasured.read_erases,BinaryCanonicalFrameMeasured.read_erases,
    BinaryStoredDimensionRowMeasured.read_erases,pack_erases]
  cases (BinaryStoredDimensionHeaderLifetime.readWithTrace bits).1 with
  | none => rfl
  | some raw =>
      dsimp only
      cases (BinaryCanonicalFrameLifetime.readWithTrace raw.2).1 with
      | none => rfl
      | some first =>
          dsimp only
          cases (BinaryCanonicalFrameLifetime.readWithTrace first.2).1 with
          | none => rfl
          | some second =>
              dsimp only
              cases (BinaryStoredDimensionRowLifetime.readWithTrace raw.1.payload second.2).1 <;> rfl

def price (length : ℕ) : ℕ :=
  128*(length+1)+2*BinaryCanonicalFrameMeasured.price length+
    BinaryStoredDimensionRowMeasured.price length length+64*(length+1)^2+64

theorem read_work (bits : List Bool) : (read bits).2 ≤ price bits.length := by
  have hDim := BinaryStoredDimensionHeaderMeasured.read_work bits
  unfold read
  dsimp only
  split
  · unfold price
    omega
  · rename_i raw hd
    have hPayload := BinaryStoredDimensionHeaderMeasured.read_payload_length bits raw hd
    have hRaw := BinaryStoredDimensionHeaderMeasured.read_suffix_length bits raw hd
    have hFirst := (BinaryCanonicalFrameMeasured.read_work raw.2).trans (BinaryCanonicalFrameMeasured.price_mono hRaw)
    split
    · unfold price
      omega
    · rename_i first hf
      have hFirstLen := (BinaryCanonicalFrameMeasured.read_suffix_lt raw.2 first hf).le.trans hRaw
      have hSecond := (BinaryCanonicalFrameMeasured.read_work first.2).trans (BinaryCanonicalFrameMeasured.price_mono hFirstLen)
      split
      · unfold price
        omega
      · rename_i second hs
        have hSecondLen := (BinaryCanonicalFrameMeasured.read_suffix_lt first.2 second hs).le.trans hFirstLen
        have hRow := (BinaryStoredDimensionRowMeasured.read_work raw.1.payload second.2).trans
          (BinaryStoredDimensionRowMeasured.price_mono hPayload hSecondLen)
        split
        · unfold price
          omega
        · rename_i rest hr
          have hCount := BinaryStoredDimensionRowMeasured.read_count_bound raw.1.payload second.2 rest hr
          have hLength : rest.1.row.length ≤ bits.length := by rw [rest.1.length]; exact hCount.trans hSecondLen
          have hPack := (pack_work raw.1.typed first.1 second.1 rest).trans
            (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hLength 1) 2))
          unfold price
          omega

theorem price_polynomial (length : ℕ) : price length ≤ 10000*(length+1)^3 := by
  unfold price BinaryStoredDimensionRowMeasured.price BinaryCanonicalFrameMeasured.price
  nlinarith

theorem read_usage (bits : List Bool) : usage (read bits).1.2 ≤ BinaryPRGGameFrameLifetime.envelope bits.length := by
  rw [read_erases]
  exact BinaryPRGGameFrameLifetime.readWithTrace_usage bits

theorem all_prefix (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+bits.length) (read bits).1.2 steps ≤
      borrowed+bits.length+BinaryPRGGameFrameLifetime.envelope bits.length ∧
    framePeak ((read bits).1.2.take steps) ≤ BinaryPRGGameFrameLifetime.envelope bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage bits) _ steps

end Blotto.BinaryPRGGameFrameMeasured

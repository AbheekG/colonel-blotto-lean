import Blotto.BinaryPRGGameFrameLifetime
import Blotto.BinaryPRGCheckedPreparationLifetime
import Blotto.BinaryPRGFlattenReservePolynomial

/-! Raw game bytes produce a retained canonical game/header, execute the
ordered promise checker and only then build accepted numerical arrays.
Actual parsed size/consumed-word bounds derive a quartic retained trace
envelope on every input, including malformed and failed-promise paths.
Accuracy parsing and the later complete seed/output join remain separate. -/
namespace Blotto.BinaryPRGCheckedGameLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def readWithTrace (bits : List Bool) : Option ((Σ n,BinaryPRGHeaderFrame.Checked n) × List Bool) × Trace :=
  let game := BinaryPRGGameFrameLifetime.readWithTrace bits
  match game.1 with
  | none => (none,wrap 16 2 [game.2])
  | some parsed =>
      let checked := BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows parsed.1.2.game.input
        parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback
      let result := checked.1.map (fun prepared => (⟨parsed.1.1,⟨prepared,parsed.1.2.header,
        parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2))
      (result,wrap 48 2 [game.2,checked.2])

theorem readWithTrace_state (bits : List Bool) : (readWithTrace bits).1 = (BinaryPRGHeaderFrame.readChecked bits).1 := by
  unfold readWithTrace BinaryPRGHeaderFrame.readChecked
  dsimp only
  rw [BinaryPRGGameFrameLifetime.readWithTrace_original]
  cases BinaryPRGHeaderFrame.read bits with
  | none => rfl
  | some parsed =>
      dsimp only
      rw [BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows_state,
        BinaryPRGMeasuredPreparation.prepareChecked_state]

theorem parsed_sizes (bits : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    parsed.1.1 ≤ bits.length ∧ BinaryPRGPreparationWork.storedInputWidth parsed.1.2.game.input ≤ bits.length+2 := by
  have hOld : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed :=
    (BinaryPRGNormalizedFrameWork.read_state bits).trans ((BinaryPRGGameFrameLifetime.readWithTrace_original bits).symm.trans h)
  exact ⟨(BinaryDecodedInputLength.parsed_sizes bits parsed hOld).1,
    BinaryDecodedInputLength.parsed_storedInputWidth bits parsed hOld⟩

def envelope (length : ℕ) : ℕ :=
  BinaryPRGGameFrameLifetime.envelope length+BinaryPRGCheckedPreparationLifetime.envelope length (length+2)+128

theorem readWithTrace_usage (bits : List Bool) : usage (readWithTrace bits).2 ≤ envelope bits.length := by
  have hGame := BinaryPRGGameFrameLifetime.readWithTrace_usage bits
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2]) ≤ _
    unfold envelope
    omega
  · rename_i parsed hParsed
    have hSizes := parsed_sizes bits parsed hParsed
    have hCheck := (BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows_usage parsed.1.2.game.input
      parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).trans
      (BinaryPRGCheckedPreparationLifetime.envelope_mono hSizes.1 hSizes.2)
    have hw := wrap_usage 48 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2,
      (BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows parsed.1.2.game.input
        parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 48 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2,
        (BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows parsed.1.2.game.input
          parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2]) ≤ _
    unfold envelope
    omega

theorem envelope_base_plus_flatten (length : ℕ) :
    envelope length ≤ 100000000000000*(length+4)^4 +
      BinaryPRGNumericalPreparationLifetime.flattenListReserve length (length+2) +
      BinaryPRGNumericalPreparationLifetime.flattenArrayReserve length (length+2) := by
  unfold envelope
  unfold_checked_preparation_envelope
  unfold BinaryPRGGameFrameLifetime.envelope BinaryStoredDimensionRowLifetime.envelope BinaryCanonicalFrameLifetime.envelope
  nlinarith only [sq_nonneg (length:ℤ)]

theorem envelope_polynomial (length : ℕ) : envelope length ≤ 400000000000000*(length+4)^8 := by
  have hBase := envelope_base_plus_flatten length
  have hReserve := BinaryPRGFlattenReservePolynomial.flatten_reserve_polynomial length
  have hPower : (length+4)^4 ≤ (length+4)^8 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc
    envelope length ≤ 100000000000000*(length+4)^4 +
        (BinaryPRGNumericalPreparationLifetime.flattenListReserve length (length+2) +
         BinaryPRGNumericalPreparationLifetime.flattenArrayReserve length (length+2)) := by
      simpa only [Nat.add_assoc] using hBase
    _ ≤ 100000000000000*(length+4)^8 + 300000000000000*(length+4)^8 :=
      Nat.add_le_add (Nat.mul_le_mul_left 100000000000000 hPower) hReserve
    _ = 400000000000000*(length+4)^8 := by ring

theorem all_prefix (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+bits.length) (readWithTrace bits).2 steps ≤ borrowed+bits.length+envelope bits.length ∧
    framePeak ((readWithTrace bits).2.take steps) ≤ envelope bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage bits) _ steps

theorem all_prefix_polynomial (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+bits.length) (readWithTrace bits).2 steps ≤ borrowed+bits.length+400000000000000*(bits.length+4)^8 ∧
    framePeak ((readWithTrace bits).2.take steps) ≤ 400000000000000*(bits.length+4)^8 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ ((readWithTrace_usage bits).trans (envelope_polynomial bits.length)) _ steps

end Blotto.BinaryPRGCheckedGameLifetime

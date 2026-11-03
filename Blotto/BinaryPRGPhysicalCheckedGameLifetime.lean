import Blotto.BinaryPRGCheckedPhysicalPreparationLifetime
import Blotto.BinaryPRGCheckedGameLifetime

/-! The raw game-frame parser carries accepted physical numerical stores
alongside its exact native compatibility preparation. Malformed frames and
failed promises return no stores. The selected fresh-bit terminal route
retains these stores; native compatibility arrays remain in the request. -/
namespace Blotto.BinaryPRGPhysicalCheckedGameLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Checked (n : ℕ) where
  prepared : {p : BinaryPRGCheckedPhysicalPreparationLifetime.PreparedPhysical n //
    p.numerical.Valid}
  header : BinaryPRGHeaderFrame.Header n
  rows : List BinaryRationalNormalization.SignedWord
  rows_length : rows.length = n

def forget {n : ℕ} (checked : Checked n) : BinaryPRGHeaderFrame.Checked n :=
  ⟨BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked.prepared,
    checked.header,checked.rows,checked.rows_length⟩

def forgetParsed (parsed : (Σ n, Checked n) × List Bool) :
    (Σ n, BinaryPRGHeaderFrame.Checked n) × List Bool :=
  (⟨parsed.1.1,forget parsed.1.2⟩,parsed.2)

def readWithTrace (bits : List Bool) :
    Option ((Σ n, Checked n) × List Bool) × Trace :=
  let game := BinaryPRGGameFrameLifetime.readWithTrace bits
  match game.1 with
  | none => (none,wrap 16 2 [game.2])
  | some parsed =>
      let checked := BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        parsed.1.2.game.input parsed.1.2.game.canonical
        parsed.1.2.rows parsed.1.2.rows_readback
      let result := checked.1.map (fun prepared =>
        (⟨parsed.1.1,⟨prepared,parsed.1.2.header,parsed.1.2.rows,
          parsed.1.2.rows_length⟩⟩,parsed.2))
      (result,wrap 48 2 [game.2,checked.2])

theorem readWithTrace_refines (bits : List Bool) :
    (readWithTrace bits).1.map forgetParsed =
      (BinaryPRGCheckedGameLifetime.readWithTrace bits).1 := by
  unfold readWithTrace BinaryPRGCheckedGameLifetime.readWithTrace
  dsimp only
  cases hGame : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 with
  | none => rfl
  | some parsed =>
      dsimp only
      have hChecked := BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysical_refines
        parsed.1.2.game.input parsed.1.2.game.canonical
        parsed.1.2.rows parsed.1.2.rows_readback
      cases hPhysical : (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        parsed.1.2.game.input parsed.1.2.game.canonical
        parsed.1.2.rows parsed.1.2.rows_readback).1 with
      | none =>
          simp only [hPhysical,Option.map_none] at hChecked ⊢
          exact hChecked.symm ▸ rfl
      | some prepared =>
          simp only [hPhysical,Option.map_some] at hChecked ⊢
          rw [← hChecked]
          rfl

theorem readWithTrace_original (bits : List Bool) :
    (readWithTrace bits).1.map forgetParsed =
      (BinaryPRGHeaderFrame.readChecked bits).1 :=
  (readWithTrace_refines bits).trans (BinaryPRGCheckedGameLifetime.readWithTrace_state bits)

theorem returned_stores_readback (bits : List Bool)
    (parsed : (Σ n, Checked n) × List Bool)
    (hParsed : (readWithTrace bits).1 = some parsed)
    (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.prepared.1.lengthStore index).1 =
        some (parsed.1.2.prepared.1.numerical.lengths.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.prepared.1.poorStore index).1 =
        some (parsed.1.2.prepared.1.numerical.poorResources.read j) := by
  unfold readWithTrace at hParsed
  cases hGame : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 with
  | none => simp only [hGame] at hParsed; cases hParsed
  | some game =>
      simp only [hGame] at hParsed
      cases hPrepared : (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        game.1.2.game.input game.1.2.game.canonical game.1.2.rows
        game.1.2.rows_readback).1 with
      | none => simp only [hPrepared,Option.map_none] at hParsed; cases hParsed
      | some prepared =>
          simp only [hPrepared,Option.map_some,Option.some.injEq] at hParsed
          subst parsed
          exact BinaryPRGCheckedPhysicalPreparationLifetime.checked_result_readback
            game.1.2.game.input game.1.2.game.canonical game.1.2.rows
            game.1.2.rows_readback prepared hPrepared index j hIndex

def envelope (length : ℕ) : ℕ :=
  BinaryPRGGameFrameLifetime.envelope length+
  BinaryPRGPromiseLifetime.envelope length (length+2)+
  BinaryPRGNumericalPreparationLifetime.envelope length (length+2)+
  2*(PRGPhysicalArrayInterface.preparationBound length+2*length+40)+320

private theorem wrap_two (a b : Trace) : usage (wrap 48 2 [a,b]) ≤ usage a+usage b+64 := by
  have h := wrap_usage 48 2 [a,b]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
  omega

private theorem wrap_one (a : Trace) : usage (wrap 16 2 [a]) ≤ usage a+32 := by
  have h := wrap_usage 16 2 [a]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
  omega

theorem readWithTrace_usage (bits : List Bool) :
    usage (readWithTrace bits).2 ≤ envelope bits.length := by
  have hGame := BinaryPRGGameFrameLifetime.readWithTrace_usage bits
  unfold readWithTrace
  dsimp only
  split
  · have hWrap := wrap_one (BinaryPRGGameFrameLifetime.readWithTrace bits).2
    change usage (wrap 16 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2]) ≤ _
    unfold envelope
    omega
  · rename_i parsed hParsed
    have hChecked := BinaryPRGCheckedPhysicalPreparationLifetime.parsed_checked_physical_usage
      bits parsed hParsed
    have hWrap := wrap_two (BinaryPRGGameFrameLifetime.readWithTrace bits).2
      (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        parsed.1.2.game.input parsed.1.2.game.canonical
        parsed.1.2.rows parsed.1.2.rows_readback).2
    change usage (wrap 48 2 [(BinaryPRGGameFrameLifetime.readWithTrace bits).2,
      (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        parsed.1.2.game.input parsed.1.2.game.canonical
        parsed.1.2.rows parsed.1.2.rows_readback).2]) ≤ _
    unfold envelope
    omega

theorem readWithTrace_prefix (bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (readWithTrace bits).2 steps ≤
        borrowed+envelope bits.length ∧
      framePeak ((readWithTrace bits).2.take steps) ≤ envelope bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage bits) borrowed steps

end Blotto.BinaryPRGPhysicalCheckedGameLifetime

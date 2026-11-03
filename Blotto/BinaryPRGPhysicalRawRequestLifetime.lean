import Blotto.BinaryPRGPhysicalCheckedGameLifetime
import Blotto.BinaryPRGRawRequestLifetime
import Blotto.BinaryPRGResourceWork

/-! The complete raw request reader retains physical numerical stores through
accuracy parsing and Boolean-ruler assembly. Its logical request is the old
one exactly. The selected fresh-bit terminal route now carries these stores
through output; remaining native table-access charges are separate. -/
namespace Blotto.BinaryPRGPhysicalRawRequestLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Request (n : ℕ) where
  logical : BinaryPRGAccuracyRulerRequest.Request n
  physical : BinaryPRGCheckedPhysicalPreparationLifetime.PreparedPhysical n
  numerical_eq : logical.request.prepared = physical.numerical

def forgetParsed (parsed : (Σ n, Request n) × List Bool) :
    (Σ n, BinaryPRGAccuracyRulerRequest.Request n) × List Bool :=
  (⟨parsed.1.1,parsed.1.2.logical⟩,parsed.2)

def readWithTrace (frame : List Bool) :
    Option ((Σ n, Request n) × List Bool) × Trace :=
  let game := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame
  match game.1 with
  | none => (none,wrap 16 2 [game.2])
  | some parsed =>
      let accuracy := BinaryAccuracyLifetime.readWithTrace parsed.2
      match accuracy.1 with
      | none => (none,wrap 48 2 [game.2,accuracy.2])
      | some selected =>
          let checked := parsed.1.2.prepared
          let assembled := BinaryPRGRequestRulers.assembleWithRows
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          let physical : Request parsed.1.1 :=
            ⟨assembled.1,checked.1,rfl⟩
          (some (⟨parsed.1.1,physical⟩,selected.2),
            wrap 64 2 [game.2,accuracy.2,assembled.2])

theorem readWithTrace_refines (frame : List Bool) :
    (readWithTrace frame).1.map forgetParsed =
      (BinaryPRGRawRequestLifetime.readWithTrace frame).1 := by
  unfold readWithTrace BinaryPRGRawRequestLifetime.readWithTrace
  dsimp only
  cases hGame : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 with
  | none =>
      have hOld := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_refines frame
      simp only [hGame,Option.map_none] at hOld ⊢
      exact hOld.symm ▸ rfl
  | some parsed =>
      have hOld := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_refines frame
      simp only [hGame,Option.map_some] at hOld
      rw [← hOld]
      dsimp [BinaryPRGPhysicalCheckedGameLifetime.forgetParsed,
        BinaryPRGPhysicalCheckedGameLifetime.forget,forgetParsed]
      cases hAccuracy : (BinaryAccuracyLifetime.readWithTrace parsed.2).1 with
      | none => simp only [Option.map_none]
      | some selected => simp only [Option.map_some,forgetParsed]

theorem readWithTrace_original (frame : List Bool) :
    (readWithTrace frame).1.map forgetParsed =
      (BinaryPRGAccuracyRulerRequest.read frame).1 :=
  (readWithTrace_refines frame).trans (BinaryPRGRawRequestLifetime.readWithTrace_state frame)

theorem returned_stores_readback (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.physical.lengthStore index).1 =
        some (parsed.1.2.logical.request.prepared.lengths.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.physical.poorStore index).1 =
        some (parsed.1.2.logical.request.prepared.poorResources.read j) := by
  unfold readWithTrace at hParsed
  cases hGame : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 with
  | none => simp only [hGame] at hParsed; cases hParsed
  | some game =>
      simp only [hGame] at hParsed
      cases hAccuracy : (BinaryAccuracyLifetime.readWithTrace game.2).1 with
      | none => simp only [hAccuracy] at hParsed; cases hParsed
      | some selected =>
          simp only [hAccuracy,Option.some.injEq] at hParsed
          subst parsed
          have hMatch : (BinaryPRGRequestRulers.assembleWithRows
              (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical game.1.2.prepared)
              selected.1 game.1.2.header game.1.2.rows game.1.2.rows_length).1.request.prepared =
                game.1.2.prepared.1.numerical := rfl
          rw [hMatch]
          exact BinaryPRGPhysicalCheckedGameLifetime.returned_stores_readback
            frame game hGame index j hIndex

theorem returned_resource_reads (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace
      parsed.1.2.physical.lengthStore index).1 =
        some ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace
        (if rich then parsed.1.2.physical.lengthStore
          else parsed.1.2.physical.poorStore) index).1 =
        some ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource.read j) := by
  have hRead := returned_stores_readback frame parsed hParsed index j hIndex
  cases rich with
  | false =>
      simpa only [BinaryPRGResourceWork.resourceInput,Bool.false_eq_true,ite_false,
        BinaryPRGPreparation.Prepared.poor] using hRead
  | true =>
      exact ⟨by simpa only [BinaryPRGResourceWork.resourceInput,ite_true,
          BinaryPRGPreparation.Prepared.rich] using hRead.1,
        by simpa only [BinaryPRGResourceWork.resourceInput,ite_true,
          BinaryPRGPreparation.Prepared.rich] using hRead.1⟩

theorem physical_game_suffix_length (frame : List Bool)
    (parsed : (Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool)
    (h : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 = some parsed) :
    parsed.2.length ≤ frame.length := by
  have hOld := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_refines frame
  rw [h] at hOld
  exact BinaryPRGRawRequestLifetime.checked_suffix_length frame
    (BinaryPRGPhysicalCheckedGameLifetime.forgetParsed parsed)
    (by simpa only [Option.map_some] using hOld.symm)

theorem physical_game_dimension_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool)
    (h : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.1 ≤ frame.length := by
  have hOld := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_refines frame
  rw [h] at hOld
  exact BinaryPRGRawRequestLifetime.checked_dimension_bound frame
    (BinaryPRGPhysicalCheckedGameLifetime.forgetParsed parsed)
    (by simpa only [Option.map_some] using hOld.symm)

def envelope (length : ℕ) : ℕ :=
  BinaryPRGPhysicalCheckedGameLifetime.envelope length+
    BinaryAccuracyLifetime.envelope length+100000*(length+1001)+256

theorem readWithTrace_usage (frame : List Bool) :
    usage (readWithTrace frame).2 ≤ envelope frame.length := by
  have hGame := BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2]) ≤ _
    unfold envelope
    omega
  · rename_i parsed hSome
    have hLength := physical_game_suffix_length frame parsed hSome
    have hn := physical_game_dimension_bound frame parsed hSome
    have hAccuracy := (BinaryAccuracyLifetime.readWithTrace_usage parsed.2).trans
      (BinaryAccuracyLifetime.envelope_mono hLength)
    split
    · have hw := wrap_usage 48 2
        [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2,
          (BinaryAccuracyLifetime.readWithTrace parsed.2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 48 2 [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2,
        (BinaryAccuracyLifetime.readWithTrace parsed.2).2]) ≤ _
      unfold envelope
      omega
    · rename_i selected hSelected
      have hWidth := BinaryAccuracyRulerReadWork.read_widths parsed.2 selected
        ((BinaryAccuracyLifetime.readWithTrace_state parsed.2).symm.trans hSelected)
      have hAssembly := BinaryPRGRequestRulers.assembleWithRows_usage
        (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical parsed.1.2.prepared)
        selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
      have hw := wrap_usage 64 2
        [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2,
          (BinaryAccuracyLifetime.readWithTrace parsed.2).2,
          (BinaryPRGRequestRulers.assembleWithRows
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical parsed.1.2.prepared)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 64 2 [(BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).2,
        (BinaryAccuracyLifetime.readWithTrace parsed.2).2,
        (BinaryPRGRequestRulers.assembleWithRows
          (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical parsed.1.2.prepared)
          selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length).2]) ≤ _
      unfold envelope
      omega

theorem readWithTrace_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (readWithTrace frame).2 steps ≤
        borrowed+envelope frame.length ∧
      framePeak ((readWithTrace frame).2.take steps) ≤ envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) borrowed steps

end Blotto.BinaryPRGPhysicalRawRequestLifetime

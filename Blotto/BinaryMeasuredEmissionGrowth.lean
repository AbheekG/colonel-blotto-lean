import Blotto.BinaryGroupEmissionMeasured
import Blotto.BinaryPRGGlobalFallbackMeasured

/-! The measured emitter changes array reservations, not arithmetic words.
Its retained-cell/frame growth over the selected traced source is bounded
additively without any row-width or execution-price oracle. These are source
trace comparisons; native bit/address/observer/allocator prices are separate. -/

namespace Blotto.BinaryMeasuredEmissionGrowth
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryPRGHeapPrimitiveLifetime (cells)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Growth (before after : Trace) (extra : ℕ) : Prop :=
  cells after ≤ cells before+extra ∧ framePeak after ≤ framePeak before+extra

theorem frames_under_le (depth : ℕ) (trace : Trace) : framePeak trace ≤ framePeak (under depth trace) := by
  induction trace with
  | nil => simp [under,framePeak]
  | cons event rest ih => cases event <;>
      simp only [under,List.map_cons,shiftEvent,framePeak] at ih ⊢ <;> omega

theorem usage_growth (before after : Trace) (extra : ℕ) (h : Growth before after extra) :
    usage after ≤ usage before+2*extra := by
  unfold Growth usage at *
  omega

theorem growth_mono (before after : Trace) (a b : ℕ) (h : Growth before after a) (hab : a ≤ b) :
    Growth before after b := ⟨h.1.trans (by omega),h.2.trans (by omega)⟩

theorem wrap_one (slots frames : ℕ) (before after : Trace) (extra : ℕ) (h : Growth before after extra) :
    Growth (wrap slots frames [before]) (wrap slots frames [after]) (extra+2) := by
  have hu := framePeak_under 2 after
  have hl := frames_under_le 2 before
  unfold Growth at *
  simp only [wrap,combine,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold cells at h
  exact ⟨by omega,by omega⟩

theorem wrap_pair (slots frames : ℕ) (same before after : Trace) (extra : ℕ) (h : Growth before after extra) :
    Growth (wrap slots frames [same,before]) (wrap slots frames [same,after]) (extra+2) := by
  have hu := framePeak_under 2 after
  have hl := frames_under_le 2 before
  unfold Growth at *
  simp only [wrap,combine,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold cells at h
  exact ⟨by omega,by omega⟩

def arrayDelta (n : ℕ) : ℕ := BinaryLifetimeArrayMeasured.storageReserve n+2*n+8

theorem wrap_two (slots frames : ℕ) (a b x y : Trace) (A B : ℕ)
    (ha : Growth a x A) (hb : Growth b y B) :
    Growth (wrap slots frames [a,b]) (wrap slots frames [x,y]) (A+B+2) := by
  have hxa := framePeak_under 2 x
  have hyb := framePeak_under 2 y
  have hla := frames_under_le 2 a
  have hlb := frames_under_le 2 b
  simp only [Growth,wrap,combine,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak] at ha hb ⊢
  exact ⟨by omega,by omega⟩

theorem array_growth {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    Growth (BinaryLifetimeArray.build n (fun j => (produce j).1)).2
      (BinaryLifetimeArrayMeasured.build n produce).1.2 (arrayDelta n) := by
  let children := BinaryLifetimeArray.children n (fun j => (produce j).1.2)
  have hu := framePeak_under (n+2) children
  have hl := frames_under_le 2 children
  rw [BinaryLifetimeArray.build_reference,BinaryLifetimeArrayMeasured.build_trace]
  unfold BinaryLifetimeArray.buildReference Growth arrayDelta
  change cells ([.frames (2*n+8),.arrayAllocation (BinaryLifetimeArrayMeasured.storageReserve n)]++under (n+2) children) ≤ _ ∧ _
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  dsimp only [children] at hu hl ⊢
  exact ⟨by omega,by omega⟩

theorem emit_growth {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    Growth (BinaryGroupEmissionLifetime.emitWithTrace routes row).2
      (BinaryGroupEmissionMeasured.emit routes row).1.2 (arrayDelta n) := by
  have h := array_growth n (BinaryGroupEmissionMeasured.cell routes row)
  simpa only [BinaryGroupEmissionMeasured.emit_record,BinaryGroupEmissionLifetime.emitWithTrace,
    BinaryGroupEmissionMeasured.cell_erases] using h

def mixedDelta (n m : ℕ) : ℕ := BinaryGroupEmissionMeasured.referenceEnvelope m+
  BinaryGroupEmissionMeasured.referenceEnvelope n+arrayDelta n+128

theorem mixed_growth {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    Growth (BinaryGroupEmissionLifetime.emitMixedWithTrace routes pivot row).2
      (BinaryGroupEmissionMeasured.emitMixed routes pivot row).1.2 (mixedDelta n m) := by
  simp only [BinaryGroupEmissionMeasured.emitMixed_record]
  simp only [BinaryPlannedQuadratic.apply_previous]
  let uniform := BinaryGroupEmissionMeasured.subrow row
  let emitted := BinaryGroupEmissionMeasured.emit routes uniform.1.1
  let before := BinaryGroupEmissionLifetime.emitWithTrace routes uniform.1.1
  let extra := BinaryQuadraticMeasured.apply .add (emitted.1.1.read pivot) (row.read (Fin.last m))
  let copied := BinaryGroupEmissionMeasured.replace emitted.1.1 pivot extra.1.1
  have hOld : (BinaryGroupEmissionLifetime.emitMixedWithTrace routes pivot row).2 =
      wrap (2*(m+1)^2+4*(n+1)^2+64) (n+m+8) [before.2,extra.1.2] := by
    simp only [before,extra,emitted,uniform,BinaryGroupEmissionLifetime.emitMixedWithTrace,
      BinaryGroupEmissionMeasured.subrow_data,BinaryGroupEmissionMeasured.emit_data,
      BinaryQuadraticMeasured.apply_erases]
  have hEmit := emit_growth routes uniform.1.1
  change Growth before.2 emitted.1.2 (arrayDelta n) at hEmit
  have hSub := BinaryGroupEmissionMeasured.subrow_usage row
  have hCopy := BinaryGroupEmissionMeasured.replace_usage emitted.1.1 pivot extra.1.1
  change usage uniform.1.2 ≤ _ at hSub
  change usage copied.1.2 ≤ _ at hCopy
  have fSub := framePeak_under 2 uniform.1.2
  have fEmit := framePeak_under 2 emitted.1.2
  have fExtra := framePeak_under 2 extra.1.2
  have fCopy := framePeak_under 2 copied.1.2
  have lEmit := frames_under_le 2 before.2
  have lExtra := frames_under_le 2 extra.1.2
  rw [hOld]
  change Growth (wrap (2*(m+1)^2+4*(n+1)^2+64) (n+m+8) [before.2,extra.1.2])
    (wrap 64 2 [uniform.1.2,emitted.1.2,extra.1.2,copied.1.2]) (mixedDelta n m)
  simp only [Growth,mixedDelta,usage,wrap,combine,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak] at hSub hCopy hEmit ⊢
  exact ⟨by omega,by omega⟩

theorem option_growth {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (rows : Option (FixedArrayTable m SignedWord)) :
    Growth (BinaryGroupEmissionLifetime.emitOptionWithTrace routes rows).2
      (BinaryGroupEmissionMeasured.emitOption routes rows).1.2 (arrayDelta n+2) := by
  cases rows with
  | none => exact ⟨by simp [BinaryGroupEmissionLifetime.emitOptionWithTrace,BinaryGroupEmissionMeasured.emitOption_record],
      by simp [BinaryGroupEmissionLifetime.emitOptionWithTrace,BinaryGroupEmissionMeasured.emitOption_record]⟩
  | some row => exact wrap_one 16 2 _ _ _ (emit_growth routes row)

theorem mixed_option_growth {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (rows : Option (FixedArrayTable (m+1) SignedWord)) :
    Growth (BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot rows).2
      (BinaryGroupEmissionMeasured.emitMixedOption routes pivot rows).1.2 (mixedDelta n m+2) := by
  cases rows with
  | none => exact ⟨by simp [BinaryGroupEmissionLifetime.emitMixedOptionWithTrace,BinaryGroupEmissionMeasured.emitMixedOption_record],
      by simp [BinaryGroupEmissionLifetime.emitMixedOptionWithTrace,BinaryGroupEmissionMeasured.emitMixedOption_record]⟩
  | some row => exact wrap_one 16 2 _ _ _ (mixed_growth routes pivot row)

theorem mixedDelta_mono (n m M : ℕ) (h : m ≤ M) : mixedDelta n m ≤ mixedDelta n M := by
  unfold mixedDelta BinaryGroupEmissionMeasured.referenceEnvelope BinaryLifetimeArrayMeasured.storageReserve
  gcongr

theorem fallback_growth {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    Growth (BinaryPRGGlobalFallbackLifetime.prepareWithTrace input).2
      (BinaryPRGGlobalFallbackMeasured.prepare input).1.2 (arrayDelta n) := by
  exact array_growth n _

theorem arrayDelta_polynomial (n : ℕ) : arrayDelta n ≤ 128*(n+1)^2 := by
  unfold arrayDelta BinaryLifetimeArrayMeasured.storageReserve
  nlinarith

theorem mixedDelta_polynomial (n m : ℕ) : mixedDelta n m ≤ 1024*(n+m+1)^2 := by
  unfold mixedDelta arrayDelta BinaryGroupEmissionMeasured.referenceEnvelope BinaryLifetimeArrayMeasured.storageReserve
  nlinarith

end Blotto.BinaryMeasuredEmissionGrowth

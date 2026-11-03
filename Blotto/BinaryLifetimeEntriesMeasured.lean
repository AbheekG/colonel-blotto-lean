import Blotto.BinaryLifetimeMapMeasured
import Blotto.BinaryLifetimeFlattenMeasured
import Blotto.BinaryLifetimeArrayMeasured

/-! Both actual entry projections, pinned array pack and list-only trace
flatten return the old entry table/trace with work. Aggregate numerical
regions retain the matched projection cells. Array charges conservatively
allow a complete old-prefix reference copy; native bit/ownership joins remain. -/
namespace Blotto.BinaryLifetimeEntriesMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def fromEntries {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hEntries : entries.length = n) :
    (FixedArrayTable n α × Trace) × ℕ :=
  let values := BinaryLifetimeMapMeasured.map (fun item : α × Trace => (item.1,0)) entries
  let traces := BinaryLifetimeMapMeasured.map (fun item : α × Trace => (item.2,0)) entries
  let packed := BinaryLifetimeArrayMeasured.pack values.1 (Array.mkEmpty n)
  let flat := BinaryLifetimeFlattenMeasured.flatten traces.1
  have hSize : packed.1.size = n := by
    rw [BinaryLifetimeArrayMeasured.pack_empty_state]
    simp [values,BinaryLifetimeMapMeasured.map_length,hEntries]
  ((⟨packed.1,hSize⟩,[.frames (n+4),.arrayAllocation (2*(n+1)^2+8)]++under 2 flat.1),
    values.2+traces.2+packed.2+flat.2+8)

theorem fromEntries_erases {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hEntries : entries.length = n) :
    (fromEntries n entries hEntries).1 = BinaryLifetimeArray.fromEntries n entries hEntries := by
  apply Prod.ext
  · apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp only [fromEntries,BinaryLifetimeArray.fromEntries,BinaryLifetimeArray.packEntries_state,
      BinaryLifetimeArrayMeasured.pack_empty_state,BinaryLifetimeMapMeasured.map_data]
  · simp only [fromEntries,BinaryLifetimeArray.fromEntries,BinaryLifetimeMapMeasured.map_data,
      BinaryLifetimeFlattenMeasured.flatten_data]

theorem fromEntries_work {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hEntries : entries.length = n) :
    (fromEntries n entries hEntries).2 ≤
      64*(n+1)^2+8*BinaryLifetimeFlattenList.payloadCount (BinaryLifetimeArray.mapDirect Prod.snd entries) := by
  let values := BinaryLifetimeMapMeasured.map (fun item : α × Trace => (item.1,0)) entries
  let traces := BinaryLifetimeMapMeasured.map (fun item : α × Trace => (item.2,0)) entries
  have hv := BinaryLifetimeMapMeasured.map_bound (fun item : α × Trace => (item.1,0)) entries 0 (by simp)
  have ht := BinaryLifetimeMapMeasured.map_bound (fun item : α × Trace => (item.2,0)) entries 0 (by simp)
  have hV : values.1.length = n := by rw [BinaryLifetimeMapMeasured.map_length,hEntries]
  have hT : traces.1.length = n := by rw [BinaryLifetimeMapMeasured.map_length,hEntries]
  have hp := BinaryLifetimeArrayMeasured.pack_bound values.1 (Array.mkEmpty n) n (by simp [hV])
  have hf := BinaryLifetimeFlattenMeasured.flatten_work traces.1
  have hTraces : traces.1 = BinaryLifetimeArray.mapDirect Prod.snd entries := BinaryLifetimeMapMeasured.map_data _ _
  rw [hT] at hf
  have hf' : (BinaryLifetimeFlattenMeasured.flatten traces.1).2 =
      8*BinaryLifetimeFlattenList.payloadCount (BinaryLifetimeArray.mapDirect Prod.snd entries)+6*n+2 := by
    simpa only [hTraces] using hf
  change values.2 ≤ _ at hv
  change traces.2 ≤ _ at ht
  rw [hEntries] at hv ht
  rw [hV] at hp
  change values.2+traces.2+(BinaryLifetimeArrayMeasured.pack values.1 (Array.mkEmpty n)).2+
    (BinaryLifetimeFlattenMeasured.flatten traces.1).2+8 ≤ _
  nlinarith

end Blotto.BinaryLifetimeEntriesMeasured

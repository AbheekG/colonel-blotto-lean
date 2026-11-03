import Blotto.GeneralPaperUnifiedDirectoryInstallation

/-! Extensional refinement of the two earlier typed read interfaces by the
single installed address map. Equality includes empty addresses, so readers
and their local payload-sensitive work transfer without additional oracles. -/
namespace Blotto.GeneralPaperUnifiedFieldMemoryViews
open GeneralPaperUnifiedFieldValue GeneralPaperReferenceSlotConstruction
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def heap {α : Type*} (S A : ℕ) (width : α → ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A α)) :
    GeneralPaperPayloadMemory.Memory α :=
  (GeneralPaperPayloadMemory.install S A width (GeneralPaperPayloadMemory.empty α) entries).1

theorem heap_read {α : Type*} (S A : ℕ) (width : α → ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A α))
    (hKeys : (entries.map (fun entry => entry.1.value)).Nodup) (entry : GeneralPaperPayloadMemory.Entry A α)
    (hEntry : entry ∈ entries) : heap S A width entries entry.1.value = some entry.2 :=
  GeneralPaperPayloadMemory.installed S A width (GeneralPaperPayloadMemory.empty α) entries hKeys entry hEntry

theorem heap_none {α : Type*} (S A : ℕ) (width : α → ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A α))
    (key : ℕ) (hKey : key ∉ entries.map (fun entry => entry.1.value)) : heap S A width entries key = none := by
  exact GeneralPaperMixedReferenceMemory.preserves_key S A width (GeneralPaperPayloadMemory.empty α) entries key
    (fun entry he hEq => hKey (List.mem_map.mpr ⟨entry,he,hEq⟩))

def referenceHeap (S A : ℕ) (words : List (Entry A)) : GeneralPaperPayloadMemory.Memory Word :=
  heap S A GeneralPaperMixedReferenceMemory.encode (GeneralPaperMixedReferenceMemory.lift S A words).1

theorem reference_heap_read (S A : ℕ) (words : List (Entry A))
    (hKeys : (words.map (fun entry => entry.location.value)).Nodup) (entry : Entry A) (hEntry : entry ∈ words) :
    referenceHeap S A words entry.location.value = some (⟨A,entry.target⟩ : Word) := by
  exact heap_read S A GeneralPaperMixedReferenceMemory.encode (GeneralPaperMixedReferenceMemory.lift S A words).1
    (by rw [GeneralPaperMixedReferenceMemory.lift_keys]; exact hKeys)
    (GeneralPaperMixedReferenceMemory.liftEntry entry)
    (by rw [GeneralPaperMixedReferenceMemory.lift_data]; exact List.mem_map.mpr ⟨entry,hEntry,rfl⟩)

theorem reference_heap_none (S A : ℕ) (words : List (Entry A)) (key : ℕ)
    (hKey : key ∉ words.map (fun entry => entry.location.value)) : referenceHeap S A words key = none := by
  exact heap_none S A GeneralPaperMixedReferenceMemory.encode (GeneralPaperMixedReferenceMemory.lift S A words).1 key
    (by rw [GeneralPaperMixedReferenceMemory.lift_keys]; exact hKey)

theorem empty_key (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (key : ℕ) (hWords : key ∉ words.map (fun entry => entry.location.value))
    (hScalars : key ∉ scalars.map (fun entry => entry.1.value)) :
    (GeneralPaperUnifiedFieldMemory.prepare S A words scalars (GeneralPaperPayloadMemory.empty Value)).1 key = none := by
  exact GeneralPaperUnifiedFieldMemory.preserves_key S A words scalars (GeneralPaperPayloadMemory.empty Value) key
    (fun entry he hEq => hWords (List.mem_map.mpr ⟨entry,he,hEq⟩))
    (fun entry he hEq => hScalars (List.mem_map.mpr ⟨entry,he,hEq⟩))

theorem reference_view (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (hWords : (words.map (fun entry => entry.location.value)).Nodup)
    (hScalars : (scalars.map (fun entry => entry.1.value)).Nodup)
    (hCross : List.Disjoint (words.map (fun entry => entry.location.value)) (scalars.map (fun entry => entry.1.value))) :
    referenceMemory (GeneralPaperUnifiedFieldMemory.prepare S A words scalars (GeneralPaperPayloadMemory.empty Value)).1 =
      referenceHeap S A words := by
  classical
  funext key
  by_cases hw : key ∈ words.map (fun entry => entry.location.value)
  · obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hw
    rw [reference_heap_read S A words hWords entry he]
    exact reference_at _ _ _ (GeneralPaperUnifiedFieldMemory.reference_read S A words scalars
      (GeneralPaperPayloadMemory.empty Value) hWords hCross entry he)
  · rw [reference_heap_none S A words key hw]
    by_cases hs : key ∈ scalars.map (fun entry => entry.1.value)
    · obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hs
      exact scalar_excludes_reference _ _ _ (scalar_at _ _ _ (GeneralPaperUnifiedFieldMemory.scalar_read
        S A words scalars (GeneralPaperPayloadMemory.empty Value) hScalars entry he))
    · simp only [referenceMemory,empty_key S A words scalars key hw hs,Option.bind_none]

theorem scalar_view (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (hWords : (words.map (fun entry => entry.location.value)).Nodup)
    (hScalars : (scalars.map (fun entry => entry.1.value)).Nodup)
    (hCross : List.Disjoint (words.map (fun entry => entry.location.value)) (scalars.map (fun entry => entry.1.value))) :
    scalarMemory (GeneralPaperUnifiedFieldMemory.prepare S A words scalars (GeneralPaperPayloadMemory.empty Value)).1 =
      heap S A GeneralPaperRetainedScalarValue.encode scalars := by
  classical
  funext key
  by_cases hs : key ∈ scalars.map (fun entry => entry.1.value)
  · obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hs
    rw [heap_read S A GeneralPaperRetainedScalarValue.encode scalars hScalars entry he]
    exact scalar_at _ _ _ (GeneralPaperUnifiedFieldMemory.scalar_read S A words scalars
      (GeneralPaperPayloadMemory.empty Value) hScalars entry he)
  · rw [heap_none S A GeneralPaperRetainedScalarValue.encode scalars key hs]
    by_cases hw : key ∈ words.map (fun entry => entry.location.value)
    · obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hw
      exact reference_excludes_scalar _ _ _ (reference_at _ _ _ (GeneralPaperUnifiedFieldMemory.reference_read
        S A words scalars (GeneralPaperPayloadMemory.empty Value) hWords hCross entry he))
    · simp only [scalarMemory,empty_key S A words scalars key hw hs,Option.bind_none]

end Blotto.GeneralPaperUnifiedFieldMemoryViews

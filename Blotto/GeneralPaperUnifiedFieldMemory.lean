import Blotto.GeneralPaperUnifiedFieldValue

/-! One actual address map installs reference entries followed by scalar
entries. Cross-key disjointness preserves every reference through scalar
installation. Both typed views therefore come from the same stored cells.
Lifting and installation carry explicit complete-payload copy prices. -/
namespace Blotto.GeneralPaperUnifiedFieldMemory
open GeneralPaperUnifiedFieldValue GeneralPaperReferenceSlotConstruction
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def wordEntry {A : ℕ} (entry : Entry A) : GeneralPaperPayloadMemory.Entry A Value :=
  (entry.location,.reference ⟨A,entry.target⟩)

def scalarEntry {A : ℕ} (entry : GeneralPaperPayloadMemory.Entry A Scalar) : GeneralPaperPayloadMemory.Entry A Value :=
  (entry.1,.scalar entry.2)

def liftWords (S A : ℕ) : List (Entry A) → List (GeneralPaperPayloadMemory.Entry A Value) × ℕ
  | [] => ([],64 * (S + A + 1))
  | entry :: entries =>
    let later := liftWords S A entries
    (wordEntry entry :: later.1,later.2 + 2 * A + 64 * (S + A + 1))

def liftScalars (S A : ℕ) : List (GeneralPaperPayloadMemory.Entry A Scalar) → List (GeneralPaperPayloadMemory.Entry A Value) × ℕ
  | [] => ([],64 * (S + A + 1))
  | entry :: entries =>
    let later := liftScalars S A entries
    (scalarEntry entry :: later.1,later.2 + GeneralPaperRetainedScalarValue.encode entry.2 + A + 64 * (S + A + 1))

theorem lift_words_data (S A : ℕ) (entries : List (Entry A)) : (liftWords S A entries).1 = entries.map wordEntry := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp only [liftWords,ih,List.map_cons]

theorem lift_scalars_data (S A : ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A Scalar)) :
    (liftScalars S A entries).1 = entries.map scalarEntry := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp only [liftScalars,ih,List.map_cons]

theorem lift_words_keys (S A : ℕ) (entries : List (Entry A)) :
    ((liftWords S A entries).1.map (fun entry => entry.1.value)) = entries.map (fun entry => entry.location.value) := by
  simp only [lift_words_data,List.map_map,wordEntry,Function.comp_def]

theorem lift_scalars_keys (S A : ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A Scalar)) :
    ((liftScalars S A entries).1.map (fun entry => entry.1.value)) = entries.map (fun entry => entry.1.value) := by
  simp only [lift_scalars_data,List.map_map,scalarEntry,Function.comp_def]

theorem lift_words_work (S A : ℕ) (entries : List (Entry A)) :
    (liftWords S A entries).2 = entries.length * (2 * A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction entries with
  | nil => simp only [liftWords,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih => simp only [liftWords,ih,List.length_cons]; ring

theorem lift_scalars_work (S A : ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A Scalar)) :
    (liftScalars S A entries).2 = (entries.map (fun entry => GeneralPaperRetainedScalarValue.encode entry.2)).sum +
      entries.length * (A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction entries with
  | nil => simp only [liftScalars,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih => simp only [liftScalars,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

theorem word_payload (S A : ℕ) (entries : List (Entry A)) :
    ((liftWords S A entries).1.map (fun entry => encode entry.2)).sum = entries.length * A := by
  simp only [lift_words_data,List.map_map,wordEntry,encode,Function.comp_def,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

theorem scalar_payload (S A : ℕ) (entries : List (GeneralPaperPayloadMemory.Entry A Scalar)) :
    ((liftScalars S A entries).1.map (fun entry => encode entry.2)).sum =
      (entries.map (fun entry => GeneralPaperRetainedScalarValue.encode entry.2)).sum := by
  simp only [lift_scalars_data,List.map_map,scalarEntry,encode,Function.comp_def]

def prepare (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (memory : Memory) : Memory × ℕ :=
  let wordValues := liftWords S A words
  let first := GeneralPaperPayloadMemory.install S A encode memory wordValues.1
  let scalarValues := liftScalars S A scalars
  let second := GeneralPaperPayloadMemory.install S A encode first.1 scalarValues.1
  (second.1,wordValues.2 + first.2 + scalarValues.2 + second.2 + 128 * (S + A + 1))

theorem reference_read (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (memory : Memory) (hKeys : (words.map (fun entry => entry.location.value)).Nodup)
    (hCross : List.Disjoint (words.map (fun entry => entry.location.value)) (scalars.map (fun entry => entry.1.value)))
    (entry : Entry A) (hEntry : entry ∈ words) :
    (prepare S A words scalars memory).1 entry.location.value = some (.reference ⟨A,entry.target⟩) := by
  have hWordKeys : ((liftWords S A words).1.map (fun entry => entry.1.value)).Nodup := by rw [lift_words_keys]; exact hKeys
  have hFirst := GeneralPaperPayloadMemory.installed S A encode memory (liftWords S A words).1 hWordKeys (wordEntry entry)
    (by rw [lift_words_data]; exact List.mem_map.mpr ⟨entry,hEntry,rfl⟩)
  have hLater := GeneralPaperMixedReferenceMemory.preserves_key S A encode
    (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1 entry.location.value (by
      intro scalar hs hEq
      rw [lift_scalars_data] at hs
      obtain ⟨source,hSource,rfl⟩ := List.mem_map.mp hs
      apply List.disjoint_left.mp hCross (List.mem_map.mpr ⟨entry,hEntry,rfl⟩)
      exact List.mem_map.mpr ⟨source,hSource,hEq⟩)
  exact hLater.trans hFirst

theorem scalar_read (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (memory : Memory) (hKeys : (scalars.map (fun entry => entry.1.value)).Nodup)
    (entry : GeneralPaperPayloadMemory.Entry A Scalar) (hEntry : entry ∈ scalars) :
    (prepare S A words scalars memory).1 entry.1.value = some (.scalar entry.2) := by
  have hScalarKeys : ((liftScalars S A scalars).1.map (fun entry => entry.1.value)).Nodup := by rw [lift_scalars_keys]; exact hKeys
  exact GeneralPaperPayloadMemory.installed S A encode
    (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1 hScalarKeys (scalarEntry entry)
    (by rw [lift_scalars_data]; exact List.mem_map.mpr ⟨entry,hEntry,rfl⟩)

theorem preserves_key (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar))
    (memory : Memory) (key : ℕ) (hWords : ∀ entry ∈ words,entry.location.value ≠ key)
    (hScalars : ∀ entry ∈ scalars,entry.1.value ≠ key) :
    (prepare S A words scalars memory).1 key = memory key := by
  have hFirst := GeneralPaperMixedReferenceMemory.preserves_key S A encode memory (liftWords S A words).1 key (by
    intro entry he
    rw [lift_words_data] at he
    obtain ⟨source,hSource,rfl⟩ := List.mem_map.mp he
    exact hWords source hSource)
  have hLater := GeneralPaperMixedReferenceMemory.preserves_key S A encode
    (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1 (liftScalars S A scalars).1 key (by
      intro entry he
      rw [lift_scalars_data] at he
      obtain ⟨source,hSource,rfl⟩ := List.mem_map.mp he
      exact hScalars source hSource)
  exact hLater.trans hFirst

theorem prepare_work (S A : ℕ) (words : List (Entry A)) (scalars : List (GeneralPaperPayloadMemory.Entry A Scalar)) (memory : Memory) :
    (prepare S A words scalars memory).2 = words.length * (67 * A + 64 + 128 * (S + A + 1)) +
      2 * (scalars.map (fun entry => GeneralPaperRetainedScalarValue.encode entry.2)).sum +
      scalars.length * (65 * A + 64 + 128 * (S + A + 1)) + 384 * (S + A + 1) := by
  dsimp only [prepare]
  rw [lift_words_work,lift_scalars_work,GeneralPaperPayloadMemory.install_work,GeneralPaperPayloadMemory.install_work,
    word_payload,scalar_payload,lift_words_data,lift_scalars_data,List.length_map,List.length_map]
  ring

end Blotto.GeneralPaperUnifiedFieldMemory

import Blotto.GeneralPaperEqualReferencePoolInstallation

/-! One paper RAM holds words from two reference pools at their own widths.
The dependent width is an erased semantic annotation of the owner cell; the
encoded payload is the raw word itself. No inner target is widened. Lifting
entries and both installations execute once, with explicit linear prices. -/
namespace Blotto.GeneralPaperMixedReferenceMemory
open GeneralPaperReferenceSlotConstruction
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

abbrev Word := (A : ℕ) × FixedBinaryWord A
def encode (word : Word) : ℕ := word.1

def liftEntry {A : ℕ} (entry : Entry A) : GeneralPaperPayloadMemory.Entry A Word :=
  (entry.location,⟨A,entry.target⟩)

def lift (S A : ℕ) : List (Entry A) → List (GeneralPaperPayloadMemory.Entry A Word) × ℕ
  | [] => ([],64 * (S + A + 1))
  | entry :: entries =>
    let later := lift S A entries
    (liftEntry entry :: later.1,later.2 + 2 * A + 64 * (S + A + 1))

theorem lift_data (S A : ℕ) (entries : List (Entry A)) : (lift S A entries).1 = entries.map liftEntry := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp only [lift,ih,List.map_cons]

theorem lift_work (S A : ℕ) (entries : List (Entry A)) :
    (lift S A entries).2 = entries.length * (2 * A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction entries with
  | nil => simp only [lift,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih => simp only [lift,ih,List.length_cons]; ring

theorem lift_keys (S A : ℕ) (entries : List (Entry A)) :
    ((lift S A entries).1.map (fun entry => entry.1.value)) = entries.map (fun entry => entry.location.value) := by
  simp only [lift_data,List.map_map,liftEntry,Function.comp_def]

theorem lift_payload (S A : ℕ) (entries : List (Entry A)) :
    ((lift S A entries).1.map (fun entry => encode entry.2)).sum = entries.length * A := by
  simp only [lift_data,List.map_map,liftEntry,encode,Function.comp_def,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

theorem preserves_key {α : Type*} (S A : ℕ) (width : α → ℕ) (memory : GeneralPaperPayloadMemory.Memory α)
    (entries : List (GeneralPaperPayloadMemory.Entry A α)) (key : ℕ) (h : ∀ e ∈ entries,e.1.value ≠ key) :
    (GeneralPaperPayloadMemory.install S A width memory entries).1 key = memory key := by
  induction entries generalizing memory with
  | nil => rfl
  | cons entry entries ih =>
    have hh := h entry (List.mem_cons_self ..)
    have ht := ih (GeneralPaperPayloadMemory.write A width memory entry).1 (fun e he => h e (List.mem_cons_of_mem entry he))
    change (GeneralPaperPayloadMemory.install S A width (GeneralPaperPayloadMemory.write A width memory entry).1 entries).1 key = _
    rw [ht]
    exact Function.update_of_ne (Ne.symm hh) _ _

structure Prepared where
  memory : GeneralPaperPayloadMemory.Memory Word
  work : ℕ

def prepare (S A B : ℕ) (inside : List (Entry A)) (outside : List (Entry B))
    (memory : GeneralPaperPayloadMemory.Memory Word) : Prepared :=
  let liftedInside := lift S A inside
  let first := GeneralPaperPayloadMemory.install S A encode memory liftedInside.1
  let liftedOutside := lift S B outside
  let second := GeneralPaperPayloadMemory.install S B encode first.1 liftedOutside.1
  ⟨second.1,liftedInside.2 + first.2 + liftedOutside.2 + second.2 + 64 * (S + A + B + 1)⟩

theorem prepare_work (S A B : ℕ) (inside : List (Entry A)) (outside : List (Entry B))
    (memory : GeneralPaperPayloadMemory.Memory Word) :
    (prepare S A B inside outside memory).work =
      inside.length * (67 * A + 64 + 128 * (S + A + 1)) +
      outside.length * (67 * B + 64 + 128 * (S + B + 1)) +
      128 * (S + A + 1) + 128 * (S + B + 1) + 64 * (S + A + B + 1) := by
  dsimp only [prepare]
  rw [lift_work,lift_work,GeneralPaperPayloadMemory.install_work,GeneralPaperPayloadMemory.install_work,
    lift_payload,lift_payload,lift_data,lift_data,List.length_map,List.length_map]
  ring

theorem inside_read (S A B : ℕ) (inside : List (Entry A)) (outside : List (Entry B))
    (memory : GeneralPaperPayloadMemory.Memory Word)
    (hKeys : (inside.map (fun entry => entry.location.value)).Nodup)
    (hDisjoint : List.Disjoint (inside.map (fun entry => entry.location.value)) (outside.map (fun entry => entry.location.value)))
    (entry : Entry A) (hEntry : entry ∈ inside) :
    (prepare S A B inside outside memory).memory entry.location.value = some (⟨A,entry.target⟩ : Word) := by
  have hLiftKeys : ((lift S A inside).1.map (fun e => e.1.value)).Nodup := by rw [lift_keys]; exact hKeys
  have hFirst := GeneralPaperPayloadMemory.installed S A encode memory (lift S A inside).1 hLiftKeys (liftEntry entry)
    (by rw [lift_data]; exact List.mem_map.mpr ⟨entry,hEntry,rfl⟩)
  have hLater := preserves_key S B encode (GeneralPaperPayloadMemory.install S A encode memory (lift S A inside).1).1
    (lift S B outside).1 entry.location.value (by
      intro e he hEq
      rw [lift_data] at he
      obtain ⟨source,hs,rfl⟩ := List.mem_map.mp he
      apply List.disjoint_left.mp hDisjoint (List.mem_map.mpr ⟨entry,hEntry,rfl⟩)
      exact List.mem_map.mpr ⟨source,hs,hEq⟩)
  change (GeneralPaperPayloadMemory.install S B encode
    (GeneralPaperPayloadMemory.install S A encode memory (lift S A inside).1).1 (lift S B outside).1).1 entry.location.value = _
  exact hLater.trans hFirst

theorem outside_read (S A B : ℕ) (inside : List (Entry A)) (outside : List (Entry B))
    (memory : GeneralPaperPayloadMemory.Memory Word)
    (hKeys : (outside.map (fun entry => entry.location.value)).Nodup)
    (entry : Entry B) (hEntry : entry ∈ outside) :
    (prepare S A B inside outside memory).memory entry.location.value = some (⟨B,entry.target⟩ : Word) := by
  have hLiftKeys : ((lift S B outside).1.map (fun e => e.1.value)).Nodup := by rw [lift_keys]; exact hKeys
  exact GeneralPaperPayloadMemory.installed S B encode
    (GeneralPaperPayloadMemory.install S A encode memory (lift S A inside).1).1 (lift S B outside).1 hLiftKeys (liftEntry entry)
    (by rw [lift_data]; exact List.mem_map.mpr ⟨entry,hEntry,rfl⟩)

end Blotto.GeneralPaperMixedReferenceMemory

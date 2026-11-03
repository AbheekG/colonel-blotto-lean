import Blotto.BinaryPRGWordControllerWordStore

/-! Table traversal uses the retained Boolean cap, Boolean strict guard,
actual Boolean lookup and actual carry increment.  Its data path executes no
natural loop bound, Fin index construction or numeric address decoder.  Exact
source-list erasure and cell/payload work support lowering the still-unjoined
native table/Fin callers.  Pointer-word interpretation is a separate join. -/

namespace Blotto.BinaryPRGWordControllerWordWalk
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore

theorem cap_room (store : Store) : store.cap.value < 2^store.width := by
  have h := BinaryBigEndian.value_bounds store.cap.bits.reverse
  rw [BinaryBigEndian.value_reverse, List.length_reverse, store.cap.size] at h
  exact h

def zeroIndex (store : Store) : FixedBinaryWord store.width :=
  ⟨store.cap.bits.map (fun _ => false), (List.length_map _).trans store.cap.size⟩

theorem zeroIndex_value (store : Store) : (zeroIndex store).value = 0 := by
  rw [← FixedBinaryWord.isZero_value]
  unfold zeroIndex FixedBinaryWord.isZero
  simp

def advance (store : Store) (pc : FixedBinaryWord store.width)
    (_h : BinaryIndexWord.lt pc store.cap = true) : FixedBinaryWord store.width :=
  (BinaryIndexWord.increment pc).1

theorem advance_value (store : Store) (pc : FixedBinaryWord store.width)
    (h : BinaryIndexWord.lt pc store.cap = true) :
    (advance store pc h).value = pc.value + 1 := by
  have hRead := (BinaryIndexWord.lt_value pc store.cap).mp h
  exact (BinaryIndexWord.increment_value pc (by have hc := cap_room store; omega)).1

theorem advance_bound (store : Store) (pc : FixedBinaryWord store.width)
    (h : BinaryIndexWord.lt pc store.cap = true) :
    (advance store pc h).value ≤ store.cap.value := by
  rw [advance_value]
  have hRead := (BinaryIndexWord.lt_value pc store.cap).mp h
  omega

def walk (store : Store) (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) : List SignedWord :=
  if hRead : BinaryIndexWord.lt pc store.cap = true then
    lookup store.tree pc :: walk store (advance store pc hRead) (advance_bound store pc hRead)
  else []
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hn := advance_value store pc hRead
  have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

theorem walk_length (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (walk store pc hp).length = store.cap.value - pc.value := by
  conv_lhs => unfold walk
  split
  · rename_i hRead
    rw [List.length_cons, walk_length]
    have hn := advance_value store pc hRead
    have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hRead
    omega
  · rename_i hStop
    have he : pc.value = store.cap.value := by
      have hNot : ¬pc.value < store.cap.value := fun h => hStop ((BinaryIndexWord.lt_value pc store.cap).mpr h)
      omega
    simp only [List.length_nil, he, Nat.sub_self]
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hn := advance_value store pc hRead
  have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

theorem drop_getD_cons (fallback : SignedWord) (items : List SignedWord) (index : ℕ) (h : index < items.length) :
    items.drop index = items.getD index fallback :: items.drop (index + 1) := by
  induction items generalizing index with
  | nil => simp at h
  | cons word rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have hr : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using h
          simpa only [List.drop_succ_cons, List.getD_cons_succ, Nat.succ_add] using ih index hr

theorem walk_prepare (fallback : SignedWord) (items : List SignedWord)
    (pc : FixedBinaryWord (prepare fallback items).width)
    (hp : pc.value ≤ (prepare fallback items).cap.value) :
    walk (prepare fallback items) pc hp = items.drop pc.value := by
  conv_lhs => unfold walk
  split
  · rename_i hRead
    rw [walk_prepare, prepare_lookup, advance_value]
    have hReadValue := (BinaryIndexWord.lt_value pc (prepare fallback items).cap).mp hRead
    rw [prepare_cap] at hReadValue
    exact (drop_getD_cons fallback items pc.value hReadValue).symm
  · rename_i hStop
    have he : pc.value = items.length := by
      have hNot : ¬pc.value < (prepare fallback items).cap.value :=
        fun h => hStop ((BinaryIndexWord.lt_value pc (prepare fallback items).cap).mpr h)
      rw [prepare_cap] at hp hNot
      omega
    simp only [he, List.drop_length]
termination_by (prepare fallback items).cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc (prepare fallback items).cap = true := by assumption
  have hn := advance_value (prepare fallback items) pc hRead
  have hReadValue := (BinaryIndexWord.lt_value pc (prepare fallback items).cap).mp hRead
  omega

theorem scan_payload_bound {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    BinaryRationalExpression.payloadWords (scan tree address) ≤ maxPayload tree := by
  induction tree generalizing address with
  | leaf word => exact le_rfl
  | @branch depth left right ihl ihr =>
      cases address with
      | nil => exact (ihl []).trans (Nat.le_max_left _ _)
      | cons bit rest =>
          cases bit
          · exact (ihl rest).trans (Nat.le_max_left _ _)
          · exact (ihr rest).trans (Nat.le_max_right _ _)

def walkWithWork (store : Store) (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) : List SignedWord × ℕ :=
  let guard := BinaryIndexWord.ltWithWork pc store.cap
  if hRead : guard.1 = true then
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hRead
    let later := walkWithWork store (advance store pc hData) (advance_bound store pc hData)
    (lookup store.tree pc :: later.1, guard.2 + lookupCells store.tree pc +
      (BinaryIndexWord.incrementWithWork pc).2 + later.2 + 3)
  else ([], guard.2 + 1)
termination_by store.cap.value - pc.value
decreasing_by
  have hn := advance_value store pc hData
  have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

theorem walkWithWork_erasure (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (walkWithWork store pc hp).1 = walk store pc hp := by
  conv_lhs => unfold walkWithWork
  conv_rhs => unfold walk
  dsimp only
  split
  · rename_i hFirst
    split
    · rename_i hSecond
      have hRead : BinaryIndexWord.lt pc store.cap = true := by
        simpa only [BinaryIndexWord.ltWithWork_state] using hFirst
      simp only
      exact congrArg (lookup store.tree pc :: ·)
        (walkWithWork_erasure store (advance store pc hRead) (advance_bound store pc hRead))
    · rename_i hSecond
      simp only [BinaryIndexWord.ltWithWork_state] at hFirst hSecond
      exact False.elim (hSecond hFirst)
  · rename_i hFirst
    split
    · rename_i hSecond
      simp only [BinaryIndexWord.ltWithWork_state] at hFirst hSecond
      exact False.elim (hFirst hSecond)
    · rfl
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hn := advance_value store pc hRead
  have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

def bound (store : Store) (remaining : ℕ) : ℕ :=
  remaining * (30 * (store.width + 1) + maxPayload store.tree) + 12 * store.width + 13

theorem walkWithWork_bound (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (walkWithWork store pc hp).2 ≤ bound store (store.cap.value - pc.value) := by
  have hGuard := BinaryIndexWord.ltWithWork_bound pc store.cap
  conv_lhs => unfold walkWithWork
  dsimp only
  split
  · rename_i hRead
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hRead
    have hLater := walkWithWork_bound store (advance store pc hData) (advance_bound store pc hData)
    have hIncrement := BinaryIndexWord.incrementWithWork_bound pc
    have hLookup := scan_payload_bound store.tree pc.bits.reverse
    have hAdvance := advance_value store pc hData
    have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hData
    rw [lookupCells_exact]
    change BinaryRationalExpression.payloadWords (lookup store.tree pc) ≤ maxPayload store.tree at hLookup
    unfold bound at hLater ⊢
    have hRemaining : store.cap.value - pc.value = (store.cap.value - (advance store pc hData).value) + 1 := by omega
    rw [hRemaining]
    dsimp only
    nlinarith
  · unfold bound
    omega
termination_by store.cap.value - pc.value
decreasing_by
  have hn := advance_value store pc hData
  have hReadValue := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

def toListWithWork (store : Store) : List SignedWord × ℕ :=
  let visited := walkWithWork store (zeroIndex store) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  (visited.1, 4 * store.width + 1 + visited.2)

theorem toListWithWork_prepare (fallback : SignedWord) (items : List SignedWord) :
    (toListWithWork (prepare fallback items)).1 = items := by
  unfold toListWithWork
  dsimp only
  rw [walkWithWork_erasure, walk_prepare, zeroIndex_value, List.drop_zero]

theorem toListWithWork_bound (store : Store) :
    (toListWithWork store).2 ≤ 4 * store.width + 1 + bound store store.cap.value := by
  have h := walkWithWork_bound store (zeroIndex store) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  simp only [zeroIndex_value, Nat.sub_zero] at h
  unfold toListWithWork
  dsimp only
  omega

end Blotto.BinaryPRGWordControllerWordWalk

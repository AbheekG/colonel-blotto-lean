import Blotto.BinaryPRGWordControllerBooleanResourceInitial

/-! Initial resource identifiers are enumerated from a Boolean cap word alone.
The measured guard and carry increment run on finite bit lists. A logical Store
occurs only in erased comparison theorems, so callers need not construct its
shadow tree merely to obtain the initial active identifiers. -/

namespace Blotto.BinaryPRGHeapAddressEnumeration
open BinaryRationalEncoding BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerWordStore (Store)

variable {width : ℕ}

def zero (cap : FixedBinaryWord width) : FixedBinaryWord width :=
  ⟨cap.bits.map (fun _ => false),(List.length_map _).trans cap.size⟩

theorem zero_value (cap : FixedBinaryWord width) : (zero cap).value = 0 := by
  rw [← FixedBinaryWord.isZero_value]
  unfold zero FixedBinaryWord.isZero
  simp

theorem cap_room (cap : FixedBinaryWord width) : cap.value < 2^width := by
  have h := BinaryBigEndian.value_bounds cap.bits.reverse
  rw [BinaryBigEndian.value_reverse,List.length_reverse,cap.size] at h
  exact h

def enumerateWithWork (cap : FixedBinaryWord width) (pc : FixedBinaryWord width)
    (_hp : pc.value ≤ cap.value) : List (Address width cap) × ℕ :=
  let guard := BinaryIndexWord.ltWithWork pc cap
  if hRead : guard.1 = true then
    have hLt : pc.value < cap.value :=
      (BinaryIndexWord.lt_value pc cap).mp ((BinaryIndexWord.ltWithWork_state pc cap).symm.trans hRead)
    let advanced := BinaryIndexWord.incrementWithWork pc
    have hAdvance : advanced.1.1.value = pc.value + 1 :=
      (BinaryIndexWord.increment_value pc (by have hc := cap_room cap; omega)).1
    let later := enumerateWithWork cap advanced.1.1 (by omega)
    (⟨pc,hLt⟩ :: later.1,guard.2 + advanced.2 + 2 * (cap.bits.length + 1) + later.2 + 4)
  else ([],guard.2 + 1)
termination_by cap.value - pc.value
decreasing_by
  have hNext : (BinaryIndexWord.incrementWithWork pc).1.1.value = pc.value + 1 :=
    (BinaryIndexWord.increment_value pc (by have hc := cap_room cap; omega)).1
  omega

def allWithWork (cap : FixedBinaryWord width) : List (Address width cap) × ℕ :=
  enumerateWithWork cap (zero cap) (by rw [zero_value]; omega)

theorem enumerateWithWork_lower (cap pc : FixedBinaryWord width)
    (hp : pc.value ≤ cap.value) :
    cap.value - pc.value ≤ (enumerateWithWork cap pc hp).2 := by
  conv_rhs => unfold enumerateWithWork
  dsimp only
  split
  · rename_i hRead
    have hLt : pc.value < cap.value :=
      (BinaryIndexWord.lt_value pc cap).mp
        ((BinaryIndexWord.ltWithWork_state pc cap).symm.trans hRead)
    have hNext : (BinaryIndexWord.incrementWithWork pc).1.1.value = pc.value+1 :=
      (BinaryIndexWord.increment_value pc (by have hc := cap_room cap; omega)).1
    have hLater := enumerateWithWork_lower cap
      (BinaryIndexWord.incrementWithWork pc).1.1 (by omega)
    omega
  · rename_i hGuard
    have hNot : ¬ pc.value < cap.value := by
      intro hLt
      apply hGuard
      exact (BinaryIndexWord.ltWithWork_state pc cap).trans
        ((BinaryIndexWord.lt_value pc cap).mpr hLt)
    omega
termination_by cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc cap = true := by assumption
  have _hLt := (BinaryIndexWord.lt_value pc cap).mp hRead
  have hNext := BinaryIndexWord.increment_value pc (by have hc := cap_room cap; omega)
  omega

theorem allWithWork_lower (cap : FixedBinaryWord width) :
    cap.value ≤ (allWithWork cap).2 := by
  have h := enumerateWithWork_lower cap (zero cap)
    (by rw [zero_value]; omega)
  simpa only [zero_value,Nat.sub_zero,allWithWork] using h

theorem enumerateWithWork_reference (store : Store) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (enumerateWithWork store.cap pc hp).1 =
      BinaryPRGWordControllerBooleanResourceInitial.addresses store pc hp := by
  conv_lhs => unfold enumerateWithWork
  conv_rhs => unfold BinaryPRGWordControllerBooleanResourceInitial.addresses
  split
  · rename_i hGuard
    have hRead : BinaryIndexWord.lt pc store.cap = true :=
      (BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hGuard
    simp only [BinaryIndexWord.ltWithWork_state,hRead]
    have hNext := enumerateWithWork_reference store
      (BinaryPRGWordControllerWordWalk.advance store pc hRead)
      (BinaryPRGWordControllerWordWalk.advance_bound store pc hRead)
    simpa [BinaryIndexWord.ltWithWork_state,BinaryIndexWord.incrementWithWork,hRead,
      BinaryPRGWordControllerWordWalk.advance] using
      congrArg (fun rest => (⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hRead⟩ : Address store.width store.cap) :: rest) hNext
  · rename_i hGuard
    have hRead : BinaryIndexWord.lt pc store.cap = false := by
      cases hc : BinaryIndexWord.lt pc store.cap
      · rfl
      · exact False.elim (hGuard ((BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hc))
    simp [BinaryIndexWord.ltWithWork_state,hRead]
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hLt := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  have hNext := BinaryPRGWordControllerWordWalk.advance_value store pc hRead
  omega

theorem allWithWork_reference (store : Store) :
    (allWithWork store.cap).1 = BinaryPRGWordControllerBooleanResourceInitial.allAddresses store := by
  unfold allWithWork BinaryPRGWordControllerBooleanResourceInitial.allAddresses
  exact enumerateWithWork_reference store _ _

theorem enumerateWithWork_bound (cap : FixedBinaryWord width) (pc : FixedBinaryWord width)
    (hp : pc.value ≤ cap.value) :
    (enumerateWithWork cap pc hp).2 ≤
      (cap.value - pc.value) * (20 * (width + 1) + 4) + 12 * (width + 1) + 1 := by
  conv_lhs => unfold enumerateWithWork
  dsimp only
  split
  · rename_i hGuard
    have hLt : pc.value < cap.value :=
      (BinaryIndexWord.lt_value pc cap).mp ((BinaryIndexWord.ltWithWork_state pc cap).symm.trans hGuard)
    have hNext : (BinaryIndexWord.incrementWithWork pc).1.1.value = pc.value + 1 :=
      (BinaryIndexWord.increment_value pc (by have hc := cap_room cap; omega)).1
    have hRemain : cap.value - pc.value =
        (cap.value - (BinaryIndexWord.incrementWithWork pc).1.1.value) + 1 := by omega
    have hLater := enumerateWithWork_bound cap (BinaryIndexWord.incrementWithWork pc).1.1 (by omega)
    have hGuardWork := BinaryIndexWord.ltWithWork_bound pc cap
    have hAdvanceWork := BinaryIndexWord.incrementWithWork_bound pc
    change (BinaryIndexWord.ltWithWork pc cap).2 + (BinaryIndexWord.incrementWithWork pc).2 +
      2 * (cap.bits.length + 1) + (enumerateWithWork cap (BinaryIndexWord.incrementWithWork pc).1.1 _).2 + 4 ≤ _
    rw [cap.size]
    rw [hRemain]
    simp only [Nat.add_mul,one_mul]
    omega
  · change (BinaryIndexWord.ltWithWork pc cap).2 + 1 ≤ _
    have hGuardWork := BinaryIndexWord.ltWithWork_bound pc cap
    omega
termination_by cap.value - pc.value
decreasing_by
  omega

theorem allWithWork_bound (cap : FixedBinaryWord width) :
    (allWithWork cap).2 ≤ cap.value * (20 * (width + 1) + 4) + 12 * (width + 1) + 1 := by
  unfold allWithWork
  have h := enumerateWithWork_bound cap (zero cap) (by rw [zero_value]; omega)
  simpa only [zero_value,Nat.sub_zero] using h

end Blotto.BinaryPRGHeapAddressEnumeration

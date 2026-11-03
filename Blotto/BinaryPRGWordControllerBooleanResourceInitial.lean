import Blotto.BinaryPRGWordControllerBooleanResourceUpdateWork

/-! Resource identifiers are constructed by an actual Boolean guard/carry
loop over the stored cap. Natural values and native Fin identifiers occur only
in semantic proofs. Initialization scans the resource tree at those addresses,
including the empty and singleton cap cases. Outer input/output conversion and
pointer-word interpretation remain separate caller joins. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceInitial
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourceUpdateWork

def addresses (store : Store) (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) :
    List (Address store.width store.cap) :=
  if hRead : BinaryIndexWord.lt pc store.cap = true then
    ⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hRead⟩ ::
      addresses store (advance store pc hRead) (advance_bound store pc hRead)
  else []
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have _hn := advance_value store pc hRead
  have _hv := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

theorem addresses_values (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (addresses store pc hp).map (fun address => address.word.value) =
      List.range' pc.value (store.cap.value - pc.value) := by
  conv_lhs => unfold addresses
  split
  · rename_i hRead
    have hv := (BinaryIndexWord.lt_value pc store.cap).mp hRead
    have hn := advance_value store pc hRead
    have hRemain : store.cap.value - pc.value = (store.cap.value - (advance store pc hRead).value) + 1 := by omega
    rw [List.map_cons,addresses_values,hRemain,List.range'_succ,hn]
  · rename_i hStop
    have he : pc.value = store.cap.value := by
      have hv : ¬pc.value < store.cap.value := fun h => hStop ((BinaryIndexWord.lt_value pc store.cap).mpr h)
      omega
    simp only [he,Nat.sub_self,List.map_nil,List.range'_zero]
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have _hn := advance_value store pc hRead
  have _hv := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

theorem addresses_length (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (addresses store pc hp).length = store.cap.value - pc.value := by
  have h := congrArg List.length (addresses_values store pc hp)
  simpa only [List.length_map,List.length_range'] using h

def allAddresses (store : Store) : List (Address store.width store.cap) :=
  addresses store (zeroIndex store) (by rw [zeroIndex_value]; exact Nat.zero_le _)

theorem allAddresses_values (store : Store) :
    (allAddresses store).map (fun address => address.word.value) = List.range store.cap.value := by
  unfold allAddresses
  rw [addresses_values,zeroIndex_value,Nat.sub_zero]
  exact List.range_eq_range'.symm

def initial (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (_hCap : resource.cap = hWidth.symm ▸ capacity.cap) : State capacity.width capacity.cap :=
  let tree : Tree capacity.width := hWidth ▸ resource.tree
  ⟨tree,(allAddresses capacity).filter (fractional capacity.tree tree)⟩

theorem allAddresses_indices (store : Store) (n : ℕ) (hCount : n = store.cap.value) :
    (allAddresses store).map (fun address => address.index n hCount) = List.finRange n := by
  apply List.ext_getElem
  · have h := congrArg List.length (allAddresses_values store)
    simpa only [List.length_map,List.length_range,List.length_finRange,hCount] using h
  · intro i hLeft hRight
    apply Fin.ext
    have hIndex : i < store.cap.value := by
      have hl := congrArg List.length (allAddresses_values store)
      simp only [List.length_map,List.length_range] at hl
      simp only [List.length_map] at hLeft
      omega
    have hAddresses : i < (allAddresses store).length := by simpa only [List.length_map] using hLeft
    have h := congrArg (fun values => values[i]?) (allAddresses_values store)
    rw [List.getElem?_map,List.getElem?_range hIndex,List.getElem?_eq_getElem hAddresses] at h
    have hValue := Option.some.inj h
    simpa [List.getElem_map,Address.index,List.getElem_finRange] using hValue

theorem initial_reference (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) (n : ℕ) (hCount : n = capacity.cap.value) :
    (initial capacity resource hWidth hCap).reference n hCount =
      BinaryResourceState.initial (table capacity.cap capacity.tree n hCount)
        (table capacity.cap (hWidth ▸ resource.tree) n hCount) := by
  unfold initial State.reference BinaryResourceState.initial
  dsimp only
  rw [filter_reference,allAddresses_indices]

def addressesWithWork (store : Store) (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) :
    List (Address store.width store.cap) × ℕ :=
  let guard := BinaryIndexWord.ltWithWork pc store.cap
  if hRead : guard.1 = true then
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hRead
    let later := addressesWithWork store (advance store pc hData) (advance_bound store pc hData)
    (⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hData⟩ :: later.1,
      guard.2 + (BinaryIndexWord.incrementWithWork pc).2 + 2 * (store.width + 1) + later.2 + 4)
  else ([],guard.2 + 1)
termination_by store.cap.value - pc.value
decreasing_by
  have hn := advance_value store pc hData
  have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

theorem addressesWithWork_erasure (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (addressesWithWork store pc hp).1 = addresses store pc hp := by
  conv_lhs => unfold addressesWithWork
  conv_rhs => unfold addresses
  dsimp only
  split
  · rename_i hFirst
    split
    · rename_i hSecond
      have hRead : BinaryIndexWord.lt pc store.cap = true := by
        simpa only [BinaryIndexWord.ltWithWork_state] using hFirst
      simp only
      exact congrArg ((⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hRead⟩ : Address store.width store.cap) :: ·)
        (addressesWithWork_erasure store (advance store pc hRead) (advance_bound store pc hRead))
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
  have _hn := advance_value store pc hRead
  have _hv := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

def addressBound (indexWidth count : ℕ) : ℕ := (count + 1) * (30 * indexWidth + 30)

theorem addressesWithWork_bound (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (addressesWithWork store pc hp).2 ≤ addressBound store.width (store.cap.value - pc.value) := by
  have hGuard := BinaryIndexWord.ltWithWork_bound pc store.cap
  have hIncrement := BinaryIndexWord.incrementWithWork_bound pc
  conv_lhs => unfold addressesWithWork
  dsimp only
  split
  · rename_i hRead
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryIndexWord.ltWithWork_state pc store.cap).symm.trans hRead
    have ih := addressesWithWork_bound store (advance store pc hData) (advance_bound store pc hData)
    have hn := advance_value store pc hData
    have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
    have hRemain : store.cap.value - pc.value = store.cap.value - (advance store pc hData).value + 1 := by omega
    unfold addressBound at ih ⊢
    rw [hRemain]
    nlinarith
  · unfold addressBound
    nlinarith
termination_by store.cap.value - pc.value
decreasing_by
  have hn := advance_value store pc hData
  have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

def initialWithWork (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (_hCap : resource.cap = hWidth.symm ▸ capacity.cap) : State capacity.width capacity.cap × ℕ :=
  let tree : Tree capacity.width := hWidth ▸ resource.tree
  let enumerated := addressesWithWork capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  let scanned := scanWithWork capacity.tree tree enumerated.1
  (⟨tree,scanned.1⟩,2 * capacity.width + 1 + enumerated.2 + scanned.2 + 4)

theorem initialWithWork_erasure (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) :
    (initialWithWork capacity resource hWidth hCap).1 = initial capacity resource hWidth hCap := by
  unfold initialWithWork initial allAddresses
  dsimp only
  rw [addressesWithWork_erasure,scanWithWork_erasure]

def initialBound (indexWidth W count : ℕ) : ℕ :=
  addressBound indexWidth count + count * (fractionalBound indexWidth W + 2 * (indexWidth + 1) + 3) +
    2 * indexWidth + 6

theorem initialWithWork_bound (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ address : Address capacity.width capacity.cap,width (lookup capacity.tree address.word) ≤ W)
    (hResource : ∀ address : Address capacity.width capacity.cap,width (lookup (hWidth ▸ resource.tree) address.word) ≤ W) :
    (initialWithWork capacity resource hWidth hCap).2 ≤ initialBound capacity.width W capacity.cap.value := by
  let enumerated := addressesWithWork capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have hEnumeration := addressesWithWork_bound capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  simp only [zeroIndex_value,Nat.sub_zero] at hEnumeration
  have hScan := scanWithWork_bound capacity.tree (hWidth ▸ resource.tree) enumerated.1 W hW
    (fun address _ => hCapacity address) (fun address _ => hResource address)
  have hLength : enumerated.1.length = capacity.cap.value := by
    dsimp only [enumerated]
    rw [addressesWithWork_erasure,addresses_length,zeroIndex_value,Nat.sub_zero]
  rw [hLength] at hScan
  unfold initialWithWork initialBound
  dsimp only
  change 2 * capacity.width + 1 + enumerated.2 +
    (scanWithWork capacity.tree (hWidth ▸ resource.tree) enumerated.1).2 + 4 ≤ _
  change enumerated.2 ≤ _ at hEnumeration
  omega

end Blotto.BinaryPRGWordControllerBooleanResourceInitial

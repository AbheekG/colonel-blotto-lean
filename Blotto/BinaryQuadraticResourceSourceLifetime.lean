import Blotto.BinaryQuadraticResourceStateLifetime

/-! One stored-array-to-tree preparation and final native continuation
materialization for the Boolean resource source. Tree leaves and output row
cells borrow signed-word tails; all array versions and list/reference regions
remain retained. Final capped numeric readback has an explicit source recursion
trace. Its scalar/reference slots are not a physical Nat/pointer bit encoding.
Work/count observers and the ghost trace's own construction are excluded. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticResourceSourceLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerBooleanResourceUpdate BinaryPRGWordControllerBooleanResourceLoop
open BinaryPRGWordControllerBooleanResourceSource BinaryQuadraticResourceStateLifetime
variable {n : ℕ}

def inputTrace (capacity resource : FixedArrayTable n SignedWord) : Trace :=
  let items := capacity.data.toList
  let ruler := BinaryCarryCounter.count items []
  [.frames (n+4),.listAllocation (2*n),.arrayAllocation (16*n+24)] ++
    under 2 (BinaryWordStoreLifetime.countWithTrace items []).2 ++
    under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler items).2 ++
    under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler resource.data.toList).2

theorem inputTrace_bounds (capacity resource : FixedArrayTable n SignedWord) :
    cells (inputTrace capacity resource) ≤ 100*n+60 ∧ framePeak (inputTrace capacity resource) ≤ 3*n+12 := by
  let items := capacity.data.toList
  let ruler := BinaryCarryCounter.count items []
  have hn : items.length = n := by simp only [items,Array.length_toList,capacity.size]
  have hc := BinaryWordStoreLifetime.countWithTrace_bounds items []
  have hCarry := BinaryCarryCounter.countCarryCells_bound items []
  have ha := BinaryQuadraticResourcePairLifetime.buildWithTrace_bounds BinaryRationalOpcode.zero ruler items
  have hb := BinaryQuadraticResourcePairLifetime.buildWithTrace_bounds BinaryRationalOpcode.zero ruler resource.data.toList
  have va := buildVisits_exact BinaryRationalOpcode.zero ruler items
  have vb := buildVisits_exact BinaryRationalOpcode.zero ruler resource.data.toList
  have hRoom := prepare_capacity_bound BinaryRationalOpcode.zero items
  have hWidth := prepare_width_bound BinaryRationalOpcode.zero items
  have hLog := Nat.log2_le_self n
  change 2^ruler.length ≤ 2*items.length+1 at hRoom
  change ruler.length ≤ binaryWordWidth items.length at hWidth
  rw [hn] at hRoom hWidth
  have hRuler : ruler.length ≤ n+1 := by unfold binaryWordWidth at hWidth; omega
  rw [pow_succ] at va vb
  have cf := framePeak_under 2 (BinaryWordStoreLifetime.countWithTrace items []).2
  have af := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler items).2
  have bf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler resource.data.toList).2
  simp only [List.length_nil,BinaryCarryCounter.ones,hn] at hc hCarry
  dsimp only [items,ruler] at hc hCarry ha hb va vb hRoom hWidth hRuler cf af bf
  unfold inputTrace
  change cells ([.frames (n+4),.listAllocation (2*n),.arrayAllocation (16*n+24)] ++
    under 2 (BinaryWordStoreLifetime.countWithTrace items []).2 ++
    under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler items).2 ++
    under 2 (BinaryQuadraticResourcePairLifetime.buildWithTrace BinaryRationalOpcode.zero ruler resource.data.toList).2) ≤ _ ∧ _
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by nlinarith only [hc.1,hCarry,ha.1,hb.1,va,vb,hRoom],by omega⟩

def sourceInitialWithTrace (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    Certified (capacityStore capacity) n (source_count capacity) × Trace :=
  let cached := capacityStore capacity
  let resourceTree := BinaryPRGWordControllerBooleanResourceSourceWork.resourceFromCached cached resource.data.toList
  let started := BinaryQuadraticResourceStateLifetime.initialWithTrace cached resourceTree rfl rfl
  (⟨started.1,by
      have he : started.1 = (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR).state :=
        BinaryQuadraticResourceStateLifetime.initialWithTrace_erases cached resourceTree rfl rfl
      exact he.symm ▸ (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR).certified⟩,
    [.frames 2,.arrayAllocation 16] ++ under 2 (inputTrace capacity resource) ++ under 2 started.2)

@[simp] theorem sourceInitialWithTrace_erases (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (sourceInitialWithTrace capacity resource hC hR).1 = BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR := by
  apply BinaryPRGWordControllerBooleanResourceLoopWork.certified_ext
  change (BinaryQuadraticResourceStateLifetime.initialWithTrace (capacityStore capacity) (resourceStore capacity resource) rfl rfl).1 = _
  exact BinaryQuadraticResourceStateLifetime.initialWithTrace_erases _ _ _ _

def startBound (n w W : ℕ) : ℕ := 100*n+76 + BinaryQuadraticResourceStateLifetime.initialBound w W n
def startFrames (n w W : ℕ) : ℕ := 3*n+16 + BinaryQuadraticResourceStateLifetime.initialFrames w W n
theorem sourceInitialWithTrace_bounds (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (W : ℕ) (hW : 1 ≤ W)
    (hc : ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,width (lookup (capacityStore capacity).tree address.word) ≤ W)
    (hr : ∀ address : Address (capacityStore capacity).width (capacityStore capacity).cap,width (lookup (resourceStore capacity resource).tree address.word) ≤ W) :
    cells (sourceInitialWithTrace capacity resource hC hR).2 ≤ startBound n (capacityStore capacity).width W ∧
      framePeak (sourceInitialWithTrace capacity resource hC hR).2 ≤ startFrames n (capacityStore capacity).width W := by
  have hi := inputTrace_bounds capacity resource
  have hs := BinaryQuadraticResourceStateLifetime.initialWithTrace_bounds (capacityStore capacity) (resourceStore capacity resource) rfl rfl W hW hc hr
  rw [← source_count capacity] at hs
  have fi := framePeak_under 2 (inputTrace capacity resource)
  have fs := framePeak_under 2 (BinaryQuadraticResourceStateLifetime.initialWithTrace (capacityStore capacity) (resourceStore capacity resource) rfl rfl).2
  simp only [cells] at hi hs
  unfold sourceInitialWithTrace startBound startFrames
  simp only [BinaryPRGWordControllerBooleanResourceSourceWork.resourceFromCached_source,cells,listCells_append,arraySlots_append,
    listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

def rowsWithTrace {w : ℕ} {cap : FixedBinaryWord w} (tree : Tree w) : List (Address w cap) → List SignedWord × Trace
  | [] => ([],[.frames 1,.arrayAllocation 4])
  | address :: rest =>
      let word := BinaryQuadraticResourcePairLifetime.lookupWithTrace tree address.word
      let later := rowsWithTrace tree rest
      (word.1 :: later.1,[.frames 2,.listAllocation 1,.arrayAllocation 8] ++ under 2 word.2 ++ under 1 later.2)

@[simp] theorem rowsWithTrace_erases {w : ℕ} {cap : FixedBinaryWord w} (tree : Tree w) (addresses : List (Address w cap)) :
    (rowsWithTrace tree addresses).1 = addresses.map (fun address => lookup tree address.word) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [rowsWithTrace,BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,List.map_cons,ih]

theorem rowsWithTrace_bounds {w : ℕ} {cap : FixedBinaryWord w} (tree : Tree w) (addresses : List (Address w cap)) :
    cells (rowsWithTrace tree addresses).2 ≤ addresses.length*(5*w+21)+4 ∧
      framePeak (rowsWithTrace tree addresses).2 ≤ addresses.length+w+6 := by
  induction addresses with
  | nil => simp [rowsWithTrace,cells,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have hw := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds tree address.word
      have wf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace tree address.word).2
      have lf := framePeak_under 1 (rowsWithTrace tree rest).2
      simp only [cells] at ih
      simp only [rowsWithTrace,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,List.length_cons]
      exact ⟨by nlinarith only [hw.1,ih.1],by omega⟩

def littleValueWithTrace : List Bool → ℕ × Trace
  | [] => (0,[.frames 1,.arrayAllocation 4])
  | bit :: rest =>
      let later := littleValueWithTrace rest
      ((if bit then 1 else 0)+2*later.1,[.frames 1,.arrayAllocation 8] ++ under 1 later.2)

@[simp] theorem littleValueWithTrace_erases (bits : List Bool) :
    (littleValueWithTrace bits).1 = BinaryBigEndian.littleValue bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [littleValueWithTrace,BinaryBigEndian.littleValue,ih]; omega

theorem littleValueWithTrace_bounds (bits : List Bool) :
    cells (littleValueWithTrace bits).2 = 8*bits.length+4 ∧ framePeak (littleValueWithTrace bits).2 ≤ bits.length+1 := by
  induction bits with
  | nil => simp [littleValueWithTrace,cells,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      have lf := framePeak_under 1 (littleValueWithTrace rest).2
      simp only [cells] at ih
      simp only [littleValueWithTrace,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,List.length_cons]
      exact ⟨by omega,by omega⟩

def indicesWithTrace {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value) :
    List (Address capacity.width capacity.cap) → List (Fin n) × Trace
  | [] => ([],[.frames 1,.arrayAllocation 4])
  | address :: rest =>
      let decoded := littleValueWithTrace address.word.bits
      have hDecode : decoded.1 = (decodeIndex address n hCount).val := littleValueWithTrace_erases _
      let later := indicesWithTrace n hCount rest
      (⟨decoded.1,by rw [hDecode]; exact (decodeIndex address n hCount).isLt⟩ :: later.1,
        [.frames 2,.arrayAllocation 8,.listAllocation 1] ++ under 2 decoded.2 ++ under 1 later.2)

@[simp] theorem indicesWithTrace_erases {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value)
    (addresses : List (Address capacity.width capacity.cap)) :
    (indicesWithTrace n hCount addresses).1 = addresses.map (fun address => decodeIndex address n hCount) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [indicesWithTrace,littleValueWithTrace_erases,List.map_cons,ih]; rfl

theorem indicesWithTrace_bounds {capacity : Store} (n : ℕ) (hCount : n = capacity.cap.value)
    (addresses : List (Address capacity.width capacity.cap)) :
    cells (indicesWithTrace n hCount addresses).2 ≤ addresses.length*(8*capacity.width+13)+4 ∧
      framePeak (indicesWithTrace n hCount addresses).2 ≤ addresses.length+capacity.width+4 := by
  induction addresses with
  | nil => simp [indicesWithTrace,cells,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have hd := littleValueWithTrace_bounds address.word.bits
      rw [address.word.size] at hd
      have df := framePeak_under 2 (littleValueWithTrace address.word.bits).2
      have lf := framePeak_under 1 (indicesWithTrace n hCount rest).2
      simp only [cells] at hd ih
      simp only [indicesWithTrace,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,List.length_cons]
      exact ⟨by nlinarith only [hd.1,ih.1],by omega⟩

variable {capacity : Store} {hCount : n = capacity.cap.value}
def materializeWithTrace (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity) (state : Certified capacity n hCount) :
    BinaryResourcePair.Certified nativeCapacity × Trace :=
  let enumerated := addressesWithTrace capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  let rows := rowsWithTrace state.state.resource enumerated.1
  let active := indicesWithTrace n hCount state.state.active
  let nativeState : BinaryResourceState.State n :=
    ⟨⟨rows.1.toArray,by rw [List.size_toArray,rowsWithTrace_erases,addressesWithTrace_erases,List.length_map,
      BinaryPRGWordControllerBooleanResourceInitial.addresses_length,zeroIndex_value,Nat.sub_zero]; exact hCount.symm⟩,active.1⟩
  have hState : nativeState = materializedState state := by
    apply BinaryPRGWordControllerBooleanResourceSourceWork.state_ext
    · apply BinaryPRGWordControllerBooleanResourceSourceWork.table_data_ext
      change rows.1.toArray = (rowWords capacity state.state).toArray
      simp only [rows,rowsWithTrace_erases,enumerated,addressesWithTrace_erases]
      rfl
    · exact indicesWithTrace_erases _ _ _
  (⟨nativeState,(by rw [hState]; exact (materializeTo nativeCapacity hTable state).canonical),
    (by rw [hState]; exact (materializeTo nativeCapacity hTable state).nodup),
    (by rw [hState]; exact (materializeTo nativeCapacity hTable state).membership)⟩,
    [.frames (rows.1.length+capacity.width+4),.listAllocation capacity.width,
      .arrayAllocation (2*(rows.1.length+1)^2+24)] ++ under 2 enumerated.2 ++ under 2 rows.2 ++ under 2 active.2)

@[simp] theorem materializeWithTrace_erases (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity) (state : Certified capacity n hCount) :
    (materializeWithTrace nativeCapacity hTable state).1 = materializeTo nativeCapacity hTable state := by
  apply native_ext
  apply BinaryPRGWordControllerBooleanResourceSourceWork.state_ext
  · apply BinaryPRGWordControllerBooleanResourceSourceWork.table_data_ext
    change (rowsWithTrace state.state.resource (addressesWithTrace capacity (zeroIndex capacity) _).1).1.toArray = _
    rw [rowsWithTrace_erases,addressesWithTrace_erases]
    rfl
  · exact indicesWithTrace_erases _ _ _

def outputBound (n w : ℕ) : ℕ := (n+1)*addressStep w + n*(13*w+34) + 2*(n+1)^2 + w + 32
def outputFrames (n w : ℕ) : ℕ := n+2*w+16
theorem materializeWithTrace_bounds (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : table capacity.cap capacity.tree n hCount = nativeCapacity) (state : Certified capacity n hCount) :
    cells (materializeWithTrace nativeCapacity hTable state).2 ≤ outputBound n capacity.width ∧
      framePeak (materializeWithTrace nativeCapacity hTable state).2 ≤ outputFrames n capacity.width := by
  let enumerated := addressesWithTrace capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have he := addressesWithTrace_bounds capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have hLength : enumerated.1.length = n := by
    dsimp only [enumerated]
    rw [addressesWithTrace_erases,BinaryPRGWordControllerBooleanResourceInitial.addresses_length,zeroIndex_value,Nat.sub_zero,hCount]
  have hr := rowsWithTrace_bounds state.state.resource enumerated.1
  rw [hLength] at hr
  have hi := indicesWithTrace_bounds n hCount state.state.active
  have hn := BinaryGeneralResourceRun.active_length_le state.reference
  rw [state.reference_state] at hn
  simp only [State.reference,List.length_map] at hn
  have hRows : (rowsWithTrace state.state.resource enumerated.1).1.length = n := by rw [rowsWithTrace_erases,List.length_map,hLength]
  have ef := framePeak_under 2 enumerated.2
  have rf := framePeak_under 2 (rowsWithTrace state.state.resource enumerated.1).2
  have inf := framePeak_under 2 (indicesWithTrace n hCount state.state.active).2
  simp only [cells,zeroIndex_value,Nat.sub_zero,← hCount] at he hr hi
  unfold materializeWithTrace outputBound outputFrames
  dsimp only
  change _ ≤ _ ∧ _
  dsimp only [enumerated] at hRows hr he ef rf
  rw [hRows]
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by nlinarith only [he.1,hr.1,hi.1,hn],by omega⟩

end Blotto.BinaryQuadraticResourceSourceLifetime

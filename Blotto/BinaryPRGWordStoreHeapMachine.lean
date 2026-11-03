import Blotto.BinaryPRGWordStoreHeap

/-! Measured interpretation of the physical Boolean tape heap. Every addressed
read scans via the actual stored countdown and parses stored cell/pointer bits.
Prices count reached Boolean tape/buffer visits, with conservative copied-bit
reservations. Preparation, selected writes and source caller joins use these
same operations; no access-price or representation oracle is supplied. -/
namespace Blotto.BinaryPRGWordStoreHeapMachine
open BinaryRationalNormalization BinaryPRGWordStoreHeap
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

structure Charge where
  work : ℕ
  allocatedBits : ℕ

instance : Inhabited Charge := ⟨⟨0,0⟩⟩

def Charge.add (first second : Charge) : Charge :=
  ⟨first.work + second.work,first.allocatedBits + second.allocatedBits⟩

def fieldWithWork : List Bool → List Bool × Charge
  | [] => ([false],⟨2,1⟩)
  | bit :: rest =>
      let later := fieldWithWork rest
      (true :: bit :: later.1,⟨later.2.work + 4,later.2.allocatedBits + 2⟩)

theorem fieldWithWork_erasure (bits : List Bool) : (fieldWithWork bits).1 = field bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [fieldWithWork,field,ih]

theorem fieldWithWork_price (bits : List Bool) :
    (fieldWithWork bits).2.work = 4 * bits.length + 2 ∧ (fieldWithWork bits).2.allocatedBits = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [fieldWithWork]
  | cons bit rest ih => simp only [fieldWithWork,List.length_cons]; exact ⟨by omega,by omega⟩

def readFieldWithWork : List Bool → Option (List Bool × List Bool) × Charge
  | false :: rest => (some ([],rest),⟨2,0⟩)
  | true :: bit :: rest =>
      let later := readFieldWithWork rest
      (later.1.map (fun parsed => (bit :: parsed.1,parsed.2)),⟨later.2.work + 4,later.2.allocatedBits + 1⟩)
  | _ => (none,⟨2,0⟩)

theorem readFieldWithWork_erasure (bits : List Bool) : (readFieldWithWork bits).1 = readField bits := by
  induction bits using readFieldWithWork.induct with
  | case1 rest => rfl
  | case2 bit rest ih => simp only [readFieldWithWork,readField,ih]
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => rfl
      | cons bit rest =>
        cases bit
        · exact False.elim (hFalse rest rfl)
        · cases rest with
          | nil => rfl
          | cons next rest => exact False.elim (hTrue next rest rfl)

theorem readFieldWithWork_bounds (bits : List Bool) :
    (readFieldWithWork bits).2.work ≤ 4 * bits.length + 2 ∧
      (readFieldWithWork bits).2.allocatedBits ≤ bits.length := by
  induction bits using readFieldWithWork.induct with
  | case1 rest => simp only [readFieldWithWork,List.length_cons]; exact ⟨by omega,by omega⟩
  | case2 bit rest ih => simp only [readFieldWithWork,List.length_cons]; exact ⟨by omega,by omega⟩
  | case3 bits => cases bits <;> simp [readFieldWithWork]

theorem readField_suffix (bits : List Bool) (parsed : List Bool × List Bool) (h : readField bits = some parsed) :
    parsed.2.length ≤ bits.length := by
  induction bits using readField.induct generalizing parsed with
  | case1 rest => cases h; simp
  | case2 bit rest ih =>
      cases he : readField rest with
      | none => simp only [readField,he,Option.map_none] at h; cases h
      | some later =>
          simp only [readField,he,Option.map_some] at h
          cases h
          have hl := ih later he
          simp only [List.length_cons]
          omega
  | case3 bits => cases bits <;> simp [readField] at h

def decodeWithWork : List Bool → Option Cell × Charge
  | false :: negative :: rest =>
      let first := readFieldWithWork rest
      match first.1 with
      | none => (none,⟨first.2.work + 4,first.2.allocatedBits + 4⟩)
      | some parsed =>
          let second := readFieldWithWork parsed.2
          (second.1.map (fun later => .leaf ⟨negative,parsed.1,later.1⟩),
            ⟨first.2.work + second.2.work + 6,first.2.allocatedBits + second.2.allocatedBits + 4⟩)
  | true :: rest =>
      let first := readFieldWithWork rest
      match first.1 with
      | none => (none,⟨first.2.work + 3,first.2.allocatedBits + 4⟩)
      | some parsed =>
          let second := readFieldWithWork parsed.2
          (second.1.map (fun later => .branch parsed.1 later.1),
            ⟨first.2.work + second.2.work + 5,first.2.allocatedBits + second.2.allocatedBits + 4⟩)
  | _ => (none,⟨2,0⟩)

theorem decodeWithWork_erasure (bits : List Bool) : (decodeWithWork bits).1 = decode bits := by
  cases bits with
  | nil => rfl
  | cons first rest =>
      cases first
      · cases rest with
        | nil => rfl
        | cons negative rest =>
          simp only [decodeWithWork,decode,readFieldWithWork_erasure]
          cases he : readField rest <;> simp [Option.map_eq_bind]
      · simp only [decodeWithWork,decode,readFieldWithWork_erasure]
        cases he : readField rest <;> simp [Option.map_eq_bind]

theorem decodeWithWork_bounds (bits : List Bool) :
    (decodeWithWork bits).2.work ≤ 8 * bits.length + 10 ∧
      (decodeWithWork bits).2.allocatedBits ≤ 2 * bits.length + 4 := by
  cases bits with
  | nil => simp [decodeWithWork]
  | cons first rest =>
      cases first
      · cases rest with
        | nil => simp [decodeWithWork]
        | cons negative rest =>
          have hf := readFieldWithWork_bounds rest
          dsimp only [decodeWithWork]
          split
          · simp only [List.length_cons]; exact ⟨by omega,by omega⟩
          · rename_i parsed he
            have hData : readField rest = some parsed := (readFieldWithWork_erasure rest).symm.trans he
            have hl := readField_suffix rest parsed hData
            have hs := readFieldWithWork_bounds parsed.2
            simp only [List.length_cons]
            exact ⟨by omega,by omega⟩
      · have hf := readFieldWithWork_bounds rest
        dsimp only [decodeWithWork]
        split
        · simp only [List.length_cons]; exact ⟨by omega,by omega⟩
        · rename_i parsed he
          have hData : readField rest = some parsed := (readFieldWithWork_erasure rest).symm.trans he
          have hl := readField_suffix rest parsed hData
          have hs := readFieldWithWork_bounds parsed.2
          simp only [List.length_cons]
          exact ⟨by omega,by omega⟩

def skipWithWork (tape : List Bool) (pointer : Pointer) : List Bool × Charge :=
  let tested := BinaryStoredCountdown.nonzeroWithWork pointer
  if tested.1 then
    match tape with
    | [] => ([],⟨tested.2 + 1,0⟩)
    | _ :: rest =>
        let decremented := BinaryStoredCountdown.predecessorWithWork pointer
        let later := skipWithWork rest decremented.1
        (later.1,⟨tested.2 + decremented.2 + later.2.work + 3,
          pointer.length + later.2.allocatedBits⟩)
  else (tape,⟨tested.2 + 1,0⟩)
termination_by tape.length

theorem skipWithWork_erasure (tape : List Bool) (pointer : Pointer) : (skipWithWork tape pointer).1 = skip tape pointer := by
  induction tape generalizing pointer with
  | nil =>
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp only [skipWithWork,skip,BinaryStoredCountdown.nonzeroWithWork,hn,Bool.false_eq_true,ite_true,ite_false]
  | cons bit rest ih =>
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true
      · simp only [skipWithWork,skip,BinaryStoredCountdown.nonzeroWithWork,hn,ite_true,
          BinaryStoredCountdown.predecessorWithWork_state]
        exact ih _
      · simp only [skipWithWork,skip,BinaryStoredCountdown.nonzeroWithWork,hn,Bool.false_eq_true,ite_false]

def skipBound (cells pointerWidth : ℕ) : ℕ := (cells + 1) * (5 * (pointerWidth + 1) + 4)

theorem skipWithWork_bounds (tape : List Bool) (pointer : Pointer) :
    (skipWithWork tape pointer).2.work ≤ skipBound tape.length pointer.length ∧
      (skipWithWork tape pointer).2.allocatedBits ≤ tape.length * pointer.length := by
  induction tape generalizing pointer with
  | nil =>
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp [skipWithWork,skipBound,BinaryStoredCountdown.nonzeroWithWork,hn] <;> omega
  | cons bit rest ih =>
      have hd := BinaryStoredCountdown.predecessorWithWork_bound pointer
      have hl : (BinaryStoredCountdown.predecessorWithWork pointer).1.length = pointer.length := BinaryStoredCountdown.predecessor_length pointer
      have hi := ih (BinaryStoredCountdown.predecessorWithWork pointer).1
      rw [hl] at hi
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true
      · simp only [skipWithWork,BinaryStoredCountdown.nonzeroWithWork,hn,ite_true,List.length_cons]
        unfold skipBound at hi ⊢
        exact ⟨by nlinarith,by nlinarith⟩
      · simp only [skipWithWork,BinaryStoredCountdown.nonzeroWithWork,hn,Bool.false_eq_true,ite_false,List.length_cons]
        unfold skipBound
        exact ⟨by nlinarith,by nlinarith⟩

def readWithWork (tape : List Bool) (pointer : Pointer) : Option Cell × Charge :=
  let reached := skipWithWork tape pointer
  let parsed := decodeWithWork reached.1
  (parsed.1,reached.2.add parsed.2)

theorem readWithWork_erasure (tape : List Bool) (pointer : Pointer) : (readWithWork tape pointer).1 = read tape pointer := by
  simp only [readWithWork,BinaryPRGWordStoreHeap.read,decodeWithWork_erasure,skipWithWork_erasure]

def readBound (cells pointerWidth : ℕ) : ℕ := skipBound cells pointerWidth + 8 * cells + 10

theorem readWithWork_bounds (tape : List Bool) (pointer : Pointer) :
    (readWithWork tape pointer).2.work ≤ readBound tape.length pointer.length ∧
      (readWithWork tape pointer).2.allocatedBits ≤ tape.length * pointer.length + 2 * tape.length + 4 := by
  have hs := skipWithWork_bounds tape pointer
  have hd := decodeWithWork_bounds (skipWithWork tape pointer).1
  have hl : (skipWithWork tape pointer).1.length ≤ tape.length := by
    rw [skipWithWork_erasure,skip_drop]
    simp only [List.length_drop]
    omega
  unfold readWithWork Charge.add readBound
  dsimp only
  exact ⟨by omega,by nlinarith⟩

def appendWithWork : List Bool → List Bool → List Bool × Charge
  | [],suffix => (suffix,⟨1,0⟩)
  | bit :: rest,suffix =>
      let later := appendWithWork rest suffix
      (bit :: later.1,⟨later.2.work + 4,later.2.allocatedBits + 1⟩)

theorem appendWithWork_erasure (first second : List Bool) : (appendWithWork first second).1 = first ++ second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp only [appendWithWork,List.cons_append,ih]

theorem appendWithWork_price (first second : List Bool) :
    (appendWithWork first second).2.work = 4 * first.length + 1 ∧
      (appendWithWork first second).2.allocatedBits = first.length := by
  induction first with
  | nil => simp [appendWithWork]
  | cons bit rest ih => simp only [appendWithWork,List.length_cons]; exact ⟨by omega,by omega⟩

def encodeWithWork : Cell → List Bool × Charge
  | .leaf word =>
      let first := fieldWithWork word.numerator
      let second := fieldWithWork word.denominator
      let joined := appendWithWork first.1 second.1
      (false :: word.negative :: joined.1,
        ⟨first.2.work + second.2.work + joined.2.work + 4,
          first.2.allocatedBits + second.2.allocatedBits + joined.2.allocatedBits + 2⟩)
  | .branch left right =>
      let first := fieldWithWork left
      let second := fieldWithWork right
      let joined := appendWithWork first.1 second.1
      (true :: joined.1,
        ⟨first.2.work + second.2.work + joined.2.work + 3,
          first.2.allocatedBits + second.2.allocatedBits + joined.2.allocatedBits + 1⟩)

theorem encodeWithWork_erasure (cell : Cell) : (encodeWithWork cell).1 = encode cell := by
  cases cell <;> simp only [encodeWithWork,encode,appendWithWork_erasure,fieldWithWork_erasure]

theorem encodeWithWork_bounds (cell : Cell) :
    (encodeWithWork cell).2.work ≤ 12 * (encode cell).length + 12 ∧
      (encodeWithWork cell).2.allocatedBits ≤ 3 * (encode cell).length := by
  cases cell with
  | leaf word =>
      have hf := fieldWithWork_price word.numerator
      have hs := fieldWithWork_price word.denominator
      have ha := appendWithWork_price (fieldWithWork word.numerator).1 (fieldWithWork word.denominator).1
      have hl : (fieldWithWork word.numerator).1.length = 2 * word.numerator.length + 1 := by rw [fieldWithWork_erasure,field_length]
      unfold encodeWithWork
      dsimp only
      rw [encode_leaf_length]
      exact ⟨by omega,by omega⟩
  | branch left right =>
      have hf := fieldWithWork_price left
      have hs := fieldWithWork_price right
      have ha := appendWithWork_price (fieldWithWork left).1 (fieldWithWork right).1
      have hl : (fieldWithWork left).1.length = 2 * left.length + 1 := by rw [fieldWithWork_erasure,field_length]
      unfold encodeWithWork
      dsimp only
      rw [encode_branch_length]
      exact ⟨by omega,by omega⟩

theorem carryCells_bound (counter : List Bool) : BinaryCarryCounter.carryCells counter ≤ counter.length + 1 := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [BinaryCarryCounter.carryCells,List.length_cons] <;> omega

def countWithWork {α : Type*} : List α → Pointer → Pointer × Charge
  | [],counter => (counter,⟨1,0⟩)
  | _ :: rest,counter =>
      let advanced := BinaryCarryCounter.increment counter
      let later := countWithWork rest advanced
      (later.1,⟨4 * BinaryCarryCounter.carryCells counter + 4 * (counter.length + 1) + later.2.work + 4,
        advanced.length + later.2.allocatedBits⟩)

theorem countWithWork_erasure {α : Type*} (bits : List α) (counter : List Bool) : (countWithWork bits counter).1 = BinaryCarryCounter.count bits counter := by
  induction bits generalizing counter with
  | nil => rfl
  | cons bit rest ih => simp only [countWithWork,BinaryCarryCounter.count,ih]

def countBound (cells pointerWidth : ℕ) : ℕ := 12 * (cells + 1) * (pointerWidth + cells + 1)

theorem countWithWork_bounds {α : Type*} (bits : List α) (counter : List Bool) :
    (countWithWork bits counter).2.work ≤ countBound bits.length counter.length ∧
      (countWithWork bits counter).2.allocatedBits ≤ bits.length * (counter.length + bits.length + 1) := by
  induction bits generalizing counter with
  | nil => simp [countWithWork,countBound]; omega
  | cons bit rest ih =>
      have hi := ih (BinaryCarryCounter.increment counter)
      have hc := BinaryWordStoreLifetime.carry_length counter
      have hCarry := carryCells_bound counter
      unfold countWithWork countBound
      dsimp only
      simp only [List.length_cons]
      unfold countBound at hi
      exact ⟨by nlinarith,by nlinarith⟩

def allocateWithWork (heap : Heap) (cell : Cell) : (Pointer × Heap) × Charge :=
  let encoded := encodeWithWork cell
  let written := appendWithWork heap.tape encoded.1
  let advanced := countWithWork encoded.1 heap.next
  ((heap.next,⟨written.1,advanced.1⟩),
    ⟨encoded.2.work + written.2.work + advanced.2.work + 4 * (heap.next.length + 1) + 6,
      encoded.2.allocatedBits + written.2.allocatedBits + advanced.2.allocatedBits + heap.next.length + 4⟩)

theorem allocateWithWork_erasure (heap : Heap) (cell : Cell) : (allocateWithWork heap cell).1 = allocate heap cell := by
  simp only [allocateWithWork,allocate,encodeWithWork_erasure,appendWithWork_erasure,countWithWork_erasure]

def allocationBound (cells : ℕ) : ℕ := 100 * (cells + 1)^2

theorem allocateWithWork_bounds (heap : Heap) (cell : Cell) (hHeap : Valid heap) (B : ℕ)
    (hTape : heap.tape.length + (encode cell).length ≤ B) :
    (allocateWithWork heap cell).2.work ≤ allocationBound B ∧
      (allocateWithWork heap cell).2.allocatedBits ≤ allocationBound B := by
  have he := encodeWithWork_bounds cell
  have ha := appendWithWork_price heap.tape (encodeWithWork cell).1
  have hc := countWithWork_bounds (encodeWithWork cell).1 heap.next
  rw [encodeWithWork_erasure] at hc
  have hp := next_width heap hHeap
  have hLog := Nat.log2_le_self heap.tape.length
  have hp' : heap.next.length ≤ B + 1 := by unfold binaryWordWidth at hp; omega
  unfold allocateWithWork allocationBound
  dsimp only
  rw [encodeWithWork_erasure]
  rw [encodeWithWork_erasure] at ha
  unfold countBound at hc
  exact ⟨by nlinarith,by nlinarith⟩

def lookupWithWork : List Bool → Pointer → List Bool → List Bool → Option SignedWord × Charge
  | tape,pointer,[],_ =>
      let found := readWithWork tape pointer
      (match found.1 with | some (.leaf word) => some word | _ => none,found.2.add ⟨2,4⟩)
  | tape,pointer,_ :: ruler,address =>
      let found := readWithWork tape pointer
      match found.1 with
      | some (.branch left right) =>
          let later := if address.headD false then lookupWithWork tape right ruler address.tail else lookupWithWork tape left ruler address.tail
          (later.1,found.2.add (later.2.add ⟨4,4⟩))
      | _ => (none,found.2.add ⟨2,4⟩)

theorem lookupWithWork_erasure (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (lookupWithWork tape pointer ruler address).1 = BinaryPRGWordStoreHeap.lookup tape pointer ruler address := by
  induction ruler generalizing pointer address with
  | nil => simp only [lookupWithWork,BinaryPRGWordStoreHeap.lookup,readWithWork_erasure]; rfl
  | cons bit ruler ih =>
      simp only [lookupWithWork,BinaryPRGWordStoreHeap.lookup,readWithWork_erasure]
      cases hc : BinaryPRGWordStoreHeap.read tape pointer with
      | none => rfl
      | some cell =>
        cases cell with
        | leaf word => rfl
        | branch left right =>
          by_cases h : address.headD false = true <;> simp only [h,Bool.false_eq_true,ite_true,ite_false,ih]


def lookupBound (cells depth : ℕ) : ℕ := (depth + 1) * (readBound cells (binaryWordWidth cells) + 4)
def lookupAllocation (cells depth : ℕ) : ℕ := (depth + 1) * (cells * binaryWordWidth cells + 2 * cells + 8)

theorem readContains_bounds {tape : List Bool} {pointer : Pointer} {cell : Cell} (h : Contains tape pointer cell) :
    (readWithWork tape pointer).1 = some cell ∧
      (readWithWork tape pointer).2.work ≤ readBound tape.length (binaryWordWidth tape.length) ∧
      (readWithWork tape pointer).2.allocatedBits ≤ tape.length * binaryWordWidth tape.length + 2 * tape.length + 4 := by
  have hb := readWithWork_bounds tape pointer
  have hp := contains_pointer_width h
  refine ⟨(readWithWork_erasure tape pointer).trans (contains_read h),?_,?_⟩
  · apply hb.1.trans
    unfold readBound skipBound
    gcongr
  · exact hb.2.trans (by gcongr)

theorem lookupWithWork_bounds {depth : ℕ} {tape : List Bool} {pointer : Pointer} {tree : BinaryPRGWordControllerWordStore.Tree depth}
    (h : Realizes tape pointer tree) (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) :
    (lookupWithWork tape pointer ruler address).2.work ≤ lookupBound tape.length depth ∧
      (lookupWithWork tape pointer ruler address).2.allocatedBits ≤ lookupAllocation tape.length depth := by
  induction h generalizing ruler address with
  | leaf word cell =>
      have he : ruler = [] := List.length_eq_zero_iff.mp hr
      subst ruler
      obtain ⟨hData,hWork,hAllocation⟩ := readContains_bounds cell
      simp only [lookupWithWork,hData,Charge.add,lookupBound,lookupAllocation,Nat.zero_add,Nat.one_mul]
      exact ⟨by omega,by omega⟩
  | branch cell hl hrTree ihl ihr =>
      cases ruler with
      | nil => simp at hr
      | cons ignored ruler =>
        cases address with
        | nil => simp at ha
        | cons bit address =>
          obtain ⟨hData,hWork,hAllocation⟩ := readContains_bounds cell
          have hr' := Nat.succ.inj hr
          have ha' := Nat.succ.inj ha
          cases bit
          · have hi := ihl ruler address hr' ha'
            simp only [lookupWithWork,hData,List.headD_cons,List.tail_cons,Bool.false_eq_true,ite_false,Charge.add]
            unfold lookupBound lookupAllocation at hi ⊢
            exact ⟨by nlinarith,by nlinarith⟩
          · have hi := ihr ruler address hr' ha'
            simp only [lookupWithWork,hData,List.headD_cons,List.tail_cons,ite_true,Charge.add]
            unfold lookupBound lookupAllocation at hi ⊢
            exact ⟨by nlinarith,by nlinarith⟩

def buildWithWork (fallback : SignedWord) : List Bool → List SignedWord → Heap → Built × Charge
  | [],[],heap =>
      let produced := allocateWithWork heap (.leaf fallback)
      (⟨produced.1.1,produced.1.2,[]⟩,produced.2.add ⟨4,4⟩)
  | [],word :: rest,heap =>
      let produced := allocateWithWork heap (.leaf word)
      (⟨produced.1.1,produced.1.2,rest⟩,produced.2.add ⟨4,4⟩)
  | _ :: ruler,items,heap =>
      let first := buildWithWork fallback ruler items heap
      let second := buildWithWork fallback ruler first.1.remaining first.1.heap
      let produced := allocateWithWork second.1.heap (.branch first.1.root second.1.root)
      (⟨produced.1.1,produced.1.2,second.1.remaining⟩,first.2.add (second.2.add (produced.2.add ⟨8,8⟩)))

theorem buildWithWork_erasure (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap) :
    (buildWithWork fallback ruler items heap).1 = BinaryPRGWordStoreHeap.build fallback ruler items heap := by
  induction ruler generalizing items heap with
  | nil => cases items <;> simp only [buildWithWork,BinaryPRGWordStoreHeap.build,allocateWithWork_erasure]
  | cons bit ruler ih =>
      simp only [buildWithWork,BinaryPRGWordStoreHeap.build,ih,allocateWithWork_erasure]

def nodes (depth : ℕ) : ℕ := 2^(depth + 1) - 1

theorem extends_length {new old : Heap} (h : Extends new old) : old.tape.length ≤ new.tape.length := by
  obtain ⟨suffix,he⟩ := h
  simp only [he,List.length_append]
  omega

theorem buildWithWork_bounds (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap)
    (hHeap : Valid heap) (B : ℕ) (hB : (BinaryPRGWordStoreHeap.build fallback ruler items heap).heap.tape.length ≤ B) :
    (buildWithWork fallback ruler items heap).2.work ≤ nodes ruler.length * (allocationBound B + 8) ∧
      (buildWithWork fallback ruler items heap).2.allocatedBits ≤ nodes ruler.length * (allocationBound B + 8) := by
  induction ruler generalizing items heap with
  | nil =>
      cases items with
      | nil =>
        have hAlloc := allocateWithWork_bounds heap (.leaf fallback) hHeap B (by simpa only [BinaryPRGWordStoreHeap.build,allocate,List.length_append] using hB)
        simp only [buildWithWork,Charge.add,nodes,List.length_nil,Nat.reduceAdd,Nat.reducePow,Nat.reduceSub,Nat.one_mul]
        exact ⟨by omega,by omega⟩
      | cons word rest =>
        have hAlloc := allocateWithWork_bounds heap (.leaf word) hHeap B (by simpa only [BinaryPRGWordStoreHeap.build,allocate,List.length_append] using hB)
        simp only [buildWithWork,Charge.add,nodes,List.length_nil,Nat.reduceAdd,Nat.reducePow,Nat.reduceSub,Nat.one_mul]
        exact ⟨by omega,by omega⟩
  | cons bit ruler ih =>
      let first := BinaryPRGWordStoreHeap.build fallback ruler items heap
      let second := BinaryPRGWordStoreHeap.build fallback ruler first.remaining first.heap
      obtain ⟨hFirst,hFirstExt,hFirstTree,hFirstRest⟩ := build_contract fallback ruler items heap hHeap
      change Valid first.heap at hFirst
      obtain ⟨hSecond,hSecondExt,hSecondTree,hSecondRest⟩ := build_contract fallback ruler first.remaining first.heap hFirst
      change Valid second.heap at hSecond
      change Extends second.heap first.heap at hSecondExt
      have hLastExt := allocate_extends second.heap (.branch first.root second.root)
      have hFirstB : first.heap.tape.length ≤ B :=
        (extends_length (extends_trans hLastExt hSecondExt)).trans hB
      have hSecondB : second.heap.tape.length ≤ B := (extends_length hLastExt).trans hB
      have hl := ih items heap hHeap hFirstB
      have hr := ih first.remaining first.heap hFirst hSecondB
      have hAlloc := allocateWithWork_bounds second.heap (.branch first.root second.root) hSecond B (by
        change (second.heap.tape ++ encode (.branch first.root second.root)).length ≤ B at hB
        simpa only [List.length_append] using hB)
      simp only [buildWithWork,buildWithWork_erasure,Charge.add]
      change _ + (_ + ((allocateWithWork second.heap (.branch first.root second.root)).2.work + 8)) ≤ _ ∧
        _ + (_ + ((allocateWithWork second.heap (.branch first.root second.root)).2.allocatedBits + 8)) ≤ _
      have hN : nodes (ruler.length + 1) = 2 * nodes ruler.length + 1 := by
        have hp : 1 ≤ 2^(ruler.length + 1) := Nat.one_le_two_pow
        unfold nodes
        rw [show ruler.length + 1 + 1 = (ruler.length + 1) + 1 by omega,pow_succ]
        omega
      simp only [List.length_cons,hN]
      exact ⟨by nlinarith,by nlinarith⟩

def prepareWithWork (fallback : SignedWord) (items : List SignedWord) : Store × Charge :=
  let counted := countWithWork items []
  let stored := buildWithWork fallback counted.1 items empty
  (⟨counted.1,stored.1.heap,stored.1.root⟩,counted.2.add (stored.2.add ⟨4,4⟩))

theorem prepareWithWork_erasure (fallback : SignedWord) (items : List SignedWord) :
    (prepareWithWork fallback items).1 = BinaryPRGWordStoreHeap.prepare fallback items := by
  simp only [prepareWithWork,BinaryPRGWordStoreHeap.prepare,countWithWork_erasure,buildWithWork_erasure]

def preparationBound (fallback : SignedWord) (items : List SignedWord) : ℕ :=
  countBound items.length 0 + 4 + (4 * items.length + 1) * (allocationBound (sourceHeapBound fallback items) + 8)

theorem prepareWithWork_bounds (fallback : SignedWord) (items : List SignedWord) :
    (prepareWithWork fallback items).2.work ≤ preparationBound fallback items ∧
      (prepareWithWork fallback items).2.allocatedBits ≤ preparationBound fallback items := by
  have hHeap := prepared_source_heap fallback items
  have hBuilt := buildWithWork_bounds fallback (BinaryCarryCounter.count items []) items empty empty_valid
    (sourceHeapBound fallback items) hHeap
  have hCap := BinaryPRGWordControllerWordStore.prepare_capacity_bound fallback items
  have hNodes : nodes (BinaryCarryCounter.count items []).length ≤ 4 * items.length + 1 := by
    unfold nodes
    rw [pow_succ]
    change 2^(BinaryCarryCounter.count items []).length ≤ 2 * items.length + 1 at hCap
    omega
  have hc := countWithWork_bounds items []
  have hW := hBuilt.1.trans (Nat.mul_le_mul_right _ hNodes)
  have hA := hBuilt.2.trans (Nat.mul_le_mul_right _ hNodes)
  unfold prepareWithWork preparationBound Charge.add
  simp only [countWithWork_erasure,List.length_nil] at hc ⊢
  constructor
  · omega
  · unfold countBound
    unfold countBound at hc
    nlinarith

def lookupStoreWithWork (store : Store) (address : FixedBinaryWord store.width) : Option SignedWord × Charge :=
  let found := lookupWithWork store.heap.tape store.root store.capBits address.bits.reverse
  (found.1,found.2.add ⟨4 * address.bits.length + 2,2 * address.bits.length⟩)

theorem lookupStoreWithWork_erasure (store : Store) (address : FixedBinaryWord store.width) :
    (lookupStoreWithWork store address).1 = lookupStore store address := by
  simp only [lookupStoreWithWork,lookupStore,lookupWithWork_erasure]
  rfl

def sourceLookupBound (fallback : SignedWord) (items : List SignedWord) : ℕ :=
  lookupBound (sourceHeapBound fallback items) (binaryWordWidth items.length) + 4 * binaryWordWidth items.length + 2

theorem lookupBound_mono {first second depth otherDepth : ℕ} (h : first ≤ second) (hd : depth ≤ otherDepth) :
    lookupBound first depth ≤ lookupBound second otherDepth := by
  have hp := binaryWordWidth_mono h
  unfold lookupBound readBound skipBound
  gcongr

theorem stored_lookup_work (store : Store) (tree : BinaryPRGWordControllerWordStore.Tree store.width)
    (h : Realizes store.heap.tape store.root tree) (address : FixedBinaryWord store.width) :
    (lookupStoreWithWork store address).2.work ≤ lookupBound store.heap.tape.length store.width + 4 * store.width + 2 := by
  have hb := lookupWithWork_bounds h store.capBits address.bits.reverse rfl (by rw [List.length_reverse,address.size])
  unfold lookupStoreWithWork Charge.add
  dsimp only
  rw [address.size]
  omega

theorem prepared_lookup_work (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (BinaryPRGWordStoreHeap.prepare fallback items).width) :
    (lookupStoreWithWork (BinaryPRGWordStoreHeap.prepare fallback items) address).2.work ≤ sourceLookupBound fallback items := by
  have hb := stored_lookup_work (BinaryPRGWordStoreHeap.prepare fallback items) _ (prepare_realizes fallback items) address
  have ht := prepared_source_heap fallback items
  have hd : (BinaryPRGWordStoreHeap.prepare fallback items).width ≤ binaryWordWidth items.length :=
    BinaryPRGWordControllerWordStore.prepare_width_bound fallback items
  have hm := lookupBound_mono ht hd
  unfold sourceLookupBound
  exact hb.trans (Nat.add_le_add_right (Nat.add_le_add hm (Nat.mul_le_mul_left 4 hd)) 2)

def patchWithWork : Heap → Pointer → List Bool → List Bool → SignedWord → Option (Pointer × Heap) × Charge
  | heap,pointer,[],_,word =>
      let found := readWithWork heap.tape pointer
      match found.1 with
      | some (.leaf _) =>
          let produced := allocateWithWork heap (.leaf word)
          (some produced.1,found.2.add (produced.2.add ⟨4,4⟩))
      | _ => (none,found.2.add ⟨2,4⟩)
  | heap,pointer,_ :: ruler,address,word =>
      let found := readWithWork heap.tape pointer
      match found.1 with
      | some (.branch left right) =>
          let changed := if address.headD false then patchWithWork heap right ruler address.tail word
            else patchWithWork heap left ruler address.tail word
          match changed.1 with
          | none => (none,found.2.add (changed.2.add ⟨2,4⟩))
          | some later =>
              let cell := if address.headD false then Cell.branch left later.1 else Cell.branch later.1 right
              let produced := allocateWithWork later.2 cell
              (some produced.1,found.2.add (changed.2.add (produced.2.add ⟨4,4⟩)))
      | _ => (none,found.2.add ⟨2,4⟩)

theorem patchWithWork_erasure (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (patchWithWork heap pointer ruler address word).1 = patch heap pointer ruler address word := by
  induction ruler generalizing heap pointer address with
  | nil =>
      simp only [patchWithWork,patch,readWithWork_erasure]
      cases hc : BinaryPRGWordStoreHeap.read heap.tape pointer with
      | none => rfl
      | some cell => cases cell <;> simp only [allocateWithWork_erasure]
  | cons bit ruler ih =>
      simp only [patchWithWork,patch,readWithWork_erasure]
      cases hc : BinaryPRGWordStoreHeap.read heap.tape pointer with
      | none => rfl
      | some cell =>
          cases cell with
          | leaf old => rfl
          | branch left right =>
              by_cases hb : address.headD false = true <;>
                simp only [hb,Bool.false_eq_true,ite_true,ite_false,ih]
              all_goals split
              all_goals rename_i heq
              all_goals simp [heq,allocateWithWork_erasure]


def patchBound (cells depth : ℕ) : ℕ :=
  (depth + 1) * (readBound cells (binaryWordWidth cells) + allocationBound cells + 8)

theorem patchWithWork_bounds {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth) (heap : Heap) (pointer : Pointer)
    (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) (word : SignedWord)
    (result : Pointer × Heap) (hSuccess : patch heap pointer ruler address word = some result)
    (B : ℕ) (hB : result.2.tape.length ≤ B) :
    (patchWithWork heap pointer ruler address word).2.work ≤ patchBound B depth ∧
      (patchWithWork heap pointer ruler address word).2.allocatedBits ≤ patchBound B depth := by
  induction tree generalizing heap pointer ruler address result with
  | leaf old =>
      have he : ruler = [] := List.length_eq_zero_iff.mp hr
      subst ruler
      cases hTree with
      | leaf old cell =>
          obtain ⟨hRead,hWork,hAlloc⟩ := readContains_bounds cell
          simp only [patch,contains_read cell] at hSuccess
          cases hSuccess
          have hAllocB := allocateWithWork_bounds heap (.leaf word) hHeap B (by simpa only [allocate,List.length_append] using hB)
          have hOld : heap.tape.length ≤ B := by simp only [allocate,List.length_append] at hB; omega
          have hPointer := binaryWordWidth_mono hOld
          simp only [patchWithWork,hRead,Charge.add,patchBound,Nat.zero_add,Nat.one_mul]
          simp only [readBound,skipBound,allocationBound] at hWork hAllocB ⊢
          exact ⟨by nlinarith,by nlinarith⟩
  | @branch depth left right ihl ihr =>
      cases ruler with
      | nil => simp at hr
      | cons ignored ruler =>
        cases address with
        | nil => simp at ha
        | cons bit address =>
          have hr' : ruler.length = depth := Nat.succ.inj hr
          have ha' : address.length = depth := Nat.succ.inj ha
          cases hTree with
          | @branch _ _ leftPointer rightPointer _ _ cell leftTree rightTree =>
            obtain ⟨hRead,hWork,hAlloc⟩ := readContains_bounds cell
            cases bit
            · obtain ⟨child,hChild,hValid,hExt,hRealizes⟩ := patch_contract left heap leftPointer hHeap leftTree ruler address hr' ha' word
              simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,Bool.false_eq_true,ite_false,hChild] at hSuccess
              cases hSuccess
              have hChildB : child.2.tape.length ≤ B := by simp only [allocate,List.length_append] at hB; omega
              have hOld := (extends_length hExt).trans hChildB
              have hp := binaryWordWidth_mono hOld
              have hi := ihl heap leftPointer hHeap leftTree ruler address hr' ha' child hChild hChildB
              have hAllocB := allocateWithWork_bounds child.2 (.branch child.1 rightPointer) hValid B (by simpa only [allocate,List.length_append] using hB)
              have hMeasured := (patchWithWork_erasure heap leftPointer ruler address word).trans hChild
              simp only [patchWithWork,hRead,List.headD_cons,List.tail_cons,Bool.false_eq_true,ite_false,hMeasured,Charge.add]
              simp only [patchBound,readBound,skipBound,allocationBound] at hi hWork hAllocB ⊢
              exact ⟨by nlinarith,by nlinarith⟩
            · obtain ⟨child,hChild,hValid,hExt,hRealizes⟩ := patch_contract right heap rightPointer hHeap rightTree ruler address hr' ha' word
              simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,ite_true,hChild] at hSuccess
              cases hSuccess
              have hChildB : child.2.tape.length ≤ B := by simp only [allocate,List.length_append] at hB; omega
              have hOld := (extends_length hExt).trans hChildB
              have hp := binaryWordWidth_mono hOld
              have hi := ihr heap rightPointer hHeap rightTree ruler address hr' ha' child hChild hChildB
              have hAllocB := allocateWithWork_bounds child.2 (.branch leftPointer child.1) hValid B (by simpa only [allocate,List.length_append] using hB)
              have hMeasured := (patchWithWork_erasure heap rightPointer ruler address word).trans hChild
              simp only [patchWithWork,hRead,List.headD_cons,List.tail_cons,ite_true,hMeasured,Charge.add]
              simp only [patchBound,readBound,skipBound,allocationBound] at hi hWork hAllocB ⊢
              exact ⟨by nlinarith,by nlinarith⟩

theorem patch_source_bounds {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth) (heap : Heap) (pointer : Pointer)
    (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) (word : SignedWord) :
    ∃ result, (patchWithWork heap pointer ruler address word).1 = some result ∧
      result.2.tape.length ≤ heapBound (patchRawBound heap ruler word) ∧
      (patchWithWork heap pointer ruler address word).2.work ≤ patchBound (heapBound (patchRawBound heap ruler word)) depth ∧
      (patchWithWork heap pointer ruler address word).2.allocatedBits ≤ patchBound (heapBound (patchRawBound heap ruler word)) depth := by
  obtain ⟨result,hResult,hValid,hExt,hRealizes⟩ := patch_contract tree heap pointer hHeap hTree ruler address hr ha word
  have hSize := patch_heap_bound tree heap pointer hHeap hTree ruler address hr ha word result hResult
  have hPrice := patchWithWork_bounds tree heap pointer hHeap hTree ruler address hr ha word result hResult _ hSize
  exact ⟨result,(patchWithWork_erasure heap pointer ruler address word).trans hResult,hSize,hPrice.1,hPrice.2⟩

end Blotto.BinaryPRGWordStoreHeapMachine

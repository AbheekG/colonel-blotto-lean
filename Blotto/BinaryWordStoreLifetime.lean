import Blotto.BinaryBooleanPrimitiveLifetime
import Blotto.BinarySeedLookupTree
import Blotto.BinaryIndexWord
import Blotto.BinaryPRGOutputLifetime

/-! Concrete source lifetime for the executed Boolean seed Store and index
operations. The carry ruler, padded tree, reached reverse/tree lookup, fixed
increment and borrow comparison produce their data directly. Old reservations
stay live, including all counter versions and tree-result records. Exact
erasure needs no ownership, external execution or numeric-index premise.
Incoming seed/tree/index payloads are borrowed and counted separately. -/
set_option autoImplicit false
namespace Blotto.BinaryWordStoreLifetime
open BinarySeedPreparationSpace BinarySeedLookupTree

def carryWithTrace : List Bool → List Bool×Trace
  | [] => ([true],[.frames 1,.listAllocation 1,.arrayAllocation 4])
  | false::rest => (true::rest,[.frames 1,.listAllocation 1,.arrayAllocation 4])
  | true::rest =>
      let later := carryWithTrace rest
      (false::later.1,[.frames 1,.listAllocation 1,.arrayAllocation 4] ++ under 1 later.2)

@[simp] theorem carryWithTrace_erases (bits : List Bool) :
    (carryWithTrace bits).1=BinaryCarryCounter.increment bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [carryWithTrace,BinaryCarryCounter.increment,ih]

theorem carryWithTrace_bounds (bits : List Bool) :
    listCells (carryWithTrace bits).2+arraySlots (carryWithTrace bits).2=5*BinaryCarryCounter.carryCells bits ∧
    framePeak (carryWithTrace bits).2≤bits.length+1 := by
  induction bits with
  | nil => simp [carryWithTrace,listCells,arraySlots,framePeak,BinaryCarryCounter.carryCells]
  | cons bit rest ih =>
      cases bit
      · simp [carryWithTrace,listCells,arraySlots,framePeak,BinaryCarryCounter.carryCells]
      · have hf := framePeak_under 1 (carryWithTrace rest).2
        simp only [carryWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
          listCells_under,arraySlots_under,BinaryCarryCounter.carryCells,List.length_cons]
        exact ⟨by omega,by omega⟩

theorem carry_length (bits : List Bool) : (BinaryCarryCounter.increment bits).length≤bits.length+1 := by
  induction bits with
  | nil => simp [BinaryCarryCounter.increment]
  | cons bit rest ih => cases bit <;> simp [BinaryCarryCounter.increment,ih]

def countWithTrace {α : Type*} : List α → List Bool → List Bool×Trace
  | [],counter => (counter,[.frames 1,.arrayAllocation 4])
  | _::rest,counter =>
      let advanced := carryWithTrace counter
      let later := countWithTrace rest advanced.1
      (later.1,[.frames 2,.arrayAllocation 4] ++ under 2 advanced.2 ++ under 1 later.2)

@[simp] theorem countWithTrace_erases {α : Type*} (items : List α) (counter : List Bool) :
    (countWithTrace items counter).1=BinaryCarryCounter.count items counter := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih => simp only [countWithTrace,BinaryCarryCounter.count,ih,carryWithTrace_erases]

theorem countWithTrace_bounds {α : Type*} (items : List α) (counter : List Bool) :
    listCells (countWithTrace items counter).2+arraySlots (countWithTrace items counter).2=
      5*BinaryCarryCounter.countCarryCells items counter+4*(items.length+1) ∧
    framePeak (countWithTrace items counter).2≤2*items.length+counter.length+3 := by
  induction items generalizing counter with
  | nil => simp [countWithTrace,listCells,arraySlots,framePeak,BinaryCarryCounter.countCarryCells]
  | cons item rest ih =>
      have hCarry := carryWithTrace_bounds counter
      have hLater := ih (carryWithTrace counter).1
      have hCLength : (carryWithTrace counter).1.length≤counter.length+1 := by rw [carryWithTrace_erases]; exact carry_length counter
      have hCF := framePeak_under 2 (carryWithTrace counter).2
      have hLF := framePeak_under 1 (countWithTrace rest (carryWithTrace counter).1).2
      simp only [countWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,BinaryCarryCounter.countCarryCells,List.length_cons]
      rw [← carryWithTrace_erases] at ⊢
      exact ⟨by omega,by omega⟩

def buildWithTrace : (ruler : List Bool) → List Bool → (Tree ruler.length×List Bool)×Trace
  | [],[] => ((.leaf false,[]),[.frames 1,.arrayAllocation 8])
  | [],bit::rest => ((.leaf bit,rest),[.frames 1,.arrayAllocation 8])
  | _::ruler,seed =>
      let left := buildWithTrace ruler seed
      let right := buildWithTrace ruler left.1.2
      ((.branch left.1.1 right.1.1,right.1.2),[.frames 1,.arrayAllocation 8] ++ under 1 left.2 ++ under 1 right.2)

@[simp] theorem buildWithTrace_erases (ruler seed : List Bool) :
    (buildWithTrace ruler seed).1=BinarySeedLookupTree.build ruler seed := by
  induction ruler generalizing seed with
  | nil => cases seed <;> rfl
  | cons cell ruler ih => simp only [buildWithTrace,BinarySeedLookupTree.build,ih]

theorem buildWithTrace_bounds (ruler seed : List Bool) :
    listCells (buildWithTrace ruler seed).2+arraySlots (buildWithTrace ruler seed).2=
      8*BinarySeedLookupTree.cells (build ruler seed).1 ∧
    framePeak (buildWithTrace ruler seed).2≤ruler.length+1 := by
  induction ruler generalizing seed with
  | nil => cases seed <;> simp [buildWithTrace,build,cells,listCells,arraySlots,framePeak]
  | cons cell ruler ih =>
      have hl := ih seed
      have hr := ih (buildWithTrace ruler seed).1.2
      have hlf := framePeak_under 1 (buildWithTrace ruler seed).2
      have hrf := framePeak_under 1 (buildWithTrace ruler (buildWithTrace ruler seed).1.2).2
      simp only [buildWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,build,cells,List.length_cons]
      rw [buildWithTrace_erases] at hr hrf ⊢
      exact ⟨by omega,by omega⟩

def prepareWithTrace (seed : List Bool) : Store×Trace :=
  let ruler := countWithTrace seed []
  let built := buildWithTrace ruler.1 seed
  (⟨ruler.1.length,⟨ruler.1,rfl⟩,built.1.1⟩,[.frames (ruler.1.length+4),.arrayAllocation 8] ++ under 2 ruler.2 ++ under 2 built.2)

def assembledStore (ruler seed : List Bool) : Store :=
  ⟨ruler.length,⟨ruler,rfl⟩,(buildWithTrace ruler seed).1.1⟩

@[simp] theorem prepareWithTrace_erases (seed : List Bool) :
    (prepareWithTrace seed).1=prepare seed := by
  change assembledStore (countWithTrace seed []).1 seed=prepare seed
  rw [countWithTrace_erases]
  simp only [assembledStore,prepare,buildWithTrace_erases]

theorem prepareWithTrace_bounds (seed : List Bool) :
    listCells (prepareWithTrace seed).2+arraySlots (prepareWithTrace seed).2≤46*seed.length+20 ∧
    framePeak (prepareWithTrace seed).2≤2*seed.length+binaryWordWidth seed.length+12 := by
  have hCount := countWithTrace_bounds seed []
  have hCarry := BinaryCarryCounter.countCarryCells_bound seed []
  simp only [List.length_nil,BinaryCarryCounter.ones] at hCount hCarry
  have hTree := buildWithTrace_bounds (countWithTrace seed []).1 seed
  have hCountF := framePeak_under 2 (countWithTrace seed []).2
  have hTreeF := framePeak_under 2 (buildWithTrace (countWithTrace seed []).1 seed).2
  have hTreeCells := prepare_treeCells_bound seed
  have hWidth := prepare_width_bound seed
  unfold prepareWithTrace
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  change _≤46*seed.length+20 ∧ _
  change cells (build (BinaryCarryCounter.count seed []) seed).1≤4*seed.length+1 at hTreeCells
  have hTreeCellsTrace : cells (build (countWithTrace seed []).1 seed).1≤4*seed.length+1 := by
    rw [countWithTrace_erases]
    exact hTreeCells
  change (BinaryCarryCounter.count seed []).length≤binaryWordWidth seed.length at hWidth
  simp only [countWithTrace_erases] at hTree hWidth hTreeF ⊢
  exact ⟨by nlinarith only [hCount.1,hCarry,hTree.1,hTreeCellsTrace],by omega⟩

def storeCells (store : Store) : ℕ := 8+store.width+8*cells store.tree

theorem storeCells_prepare_bound (seed : List Bool) :
    storeCells (prepare seed)≤binaryWordWidth seed.length+32*seed.length+16 := by
  have ht := prepare_treeCells_bound seed
  have hw := prepare_width_bound seed
  unfold storeCells
  omega

def scanTreeWithTrace : {depth : ℕ} → Tree depth → List Bool → Bool×Trace
  | _,.leaf bit,_ => (bit,[.frames 1,.arrayAllocation 4])
  | _,.branch left _,[] =>
      let later := scanTreeWithTrace left []
      (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)
  | _,.branch left right,bit::rest =>
      let later := if bit then scanTreeWithTrace right rest else scanTreeWithTrace left rest
      (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)

@[simp] theorem scanTreeWithTrace_erases {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    (scanTreeWithTrace tree address).1=scan tree address := by
  induction tree generalizing address with
  | leaf bit => rfl
  | branch left right hl hr => cases address with
    | nil => exact hl []
    | cons bit rest => cases bit <;> simp [scanTreeWithTrace,scan,hl,hr]

theorem scanTreeWithTrace_bounds {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    listCells (scanTreeWithTrace tree address).2+arraySlots (scanTreeWithTrace tree address).2=4*(depth+1) ∧
    framePeak (scanTreeWithTrace tree address).2≤depth+1 := by
  induction tree generalizing address with
  | leaf bit => simp [scanTreeWithTrace,listCells,arraySlots,framePeak]
  | @branch depth left right hl hr =>
      cases address with
      | nil =>
          have hf := framePeak_under 1 (scanTreeWithTrace left []).2
          have h := hl []
          simp only [scanTreeWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under]
          exact ⟨by omega,by omega⟩
      | cons bit rest =>
          cases bit <;> simp only [scanTreeWithTrace,Bool.false_eq_true,ite_false,ite_true]
          · have hf := framePeak_under 1 (scanTreeWithTrace left rest).2
            have h := hl rest
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩
          · have hf := framePeak_under 1 (scanTreeWithTrace right rest).2
            have h := hr rest
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩

def lookupWithTrace (store : Store) (address : FixedBinaryWord store.width) : Bool×Trace :=
  let reversed := reverseWithTrace address.bits []
  let reached := scanTreeWithTrace store.tree reversed.1
  (reached.1,[.frames 2,.arrayAllocation 8] ++ under 2 reversed.2 ++ under 2 reached.2)

@[simp] theorem lookupWithTrace_erases (store : Store) (address : FixedBinaryWord store.width) :
    (lookupWithTrace store address).1=store.lookup address := by
  simp only [lookupWithTrace,scanTreeWithTrace_erases,reverseWithTrace_result]
  rfl

theorem lookupWithTrace_bounds (store : Store) (address : FixedBinaryWord store.width) :
    listCells (lookupWithTrace store address).2+arraySlots (lookupWithTrace store address).2≤5*store.width+12 ∧
    framePeak (lookupWithTrace store address).2≤store.width+3 := by
  have hr := reverseWithTrace_cells address.bits []
  have hra := reverseWithTrace_arrays address.bits []
  have hrf := reverseWithTrace_frames address.bits []
  rw [address.size] at hr hrf
  have hs := scanTreeWithTrace_bounds store.tree (reverseWithTrace address.bits []).1
  have hR := framePeak_under 2 (reverseWithTrace address.bits []).2
  have hS := framePeak_under 2 (scanTreeWithTrace store.tree (reverseWithTrace address.bits []).1).2
  simp only [lookupWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def incrementBitsWithTrace : List Bool → (List Bool×Bool)×Trace
  | [] => (([],true),[.frames 1,.arrayAllocation 4])
  | false::rest => ((true::rest,false),[.frames 1,.listAllocation 1,.arrayAllocation 4])
  | true::rest =>
      let later := incrementBitsWithTrace rest
      ((false::later.1.1,later.1.2),[.frames 1,.listAllocation 1,.arrayAllocation 4] ++ under 1 later.2)

@[simp] theorem incrementBitsWithTrace_erases (bits : List Bool) :
    (incrementBitsWithTrace bits).1=BinaryIndexWord.incrementBits bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [incrementBitsWithTrace,BinaryIndexWord.incrementBits,ih]

theorem incrementBitsWithTrace_bounds (bits : List Bool) :
    listCells (incrementBitsWithTrace bits).2+arraySlots (incrementBitsWithTrace bits).2≤5*(bits.length+1) ∧
    framePeak (incrementBitsWithTrace bits).2≤bits.length+1 := by
  induction bits with
  | nil => simp [incrementBitsWithTrace,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      cases bit
      · simp [incrementBitsWithTrace,listCells,arraySlots,framePeak]
      · have hf := framePeak_under 1 (incrementBitsWithTrace rest).2
        simp only [incrementBitsWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
          listCells_under,arraySlots_under,List.length_cons]
        exact ⟨by omega,by omega⟩

def incrementWithTrace {w : ℕ} (word : FixedBinaryWord w) : (FixedBinaryWord w×Bool)×Trace :=
  let next := incrementBitsWithTrace word.bits
  have hSize : next.1.1.length=w := by rw [incrementBitsWithTrace_erases,BinaryIndexWord.incrementBits_length,word.size]
  ((⟨next.1.1,hSize⟩,next.1.2),[.frames 2,.arrayAllocation 8] ++ under 2 next.2)

@[simp] theorem incrementWithTrace_erases {w : ℕ} (word : FixedBinaryWord w) :
    (incrementWithTrace word).1=BinaryIndexWord.increment word := by
  unfold incrementWithTrace BinaryIndexWord.increment
  simp only [incrementBitsWithTrace_erases]

theorem incrementWithTrace_bounds {w : ℕ} (word : FixedBinaryWord w) :
    listCells (incrementWithTrace word).2+arraySlots (incrementWithTrace word).2≤5*w+13 ∧
    framePeak (incrementWithTrace word).2≤w+3 := by
  have h := incrementBitsWithTrace_bounds word.bits
  rw [word.size] at h
  have hf := framePeak_under 2 (incrementBitsWithTrace word.bits).2
  simp only [incrementWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def ltWithTrace {w : ℕ} (first second : FixedBinaryWord w) : Bool×Trace :=
  let result := BinaryDivisionAllocation.borrowWithAllocation first.bits second.bits false []
  (result.1.2,[.frames (2*w+4),.arrayAllocation 8,
    .listAllocation (BinaryDivisionAllocation.borrowStorage first.bits second.bits)])

@[simp] theorem ltWithTrace_erases {w : ℕ} (first second : FixedBinaryWord w) :
    (ltWithTrace first second).1=BinaryIndexWord.lt first second := by
  rw [ltWithTrace,BinaryDivisionAllocation.borrowWithAllocation_refines]
  rfl

theorem ltWithTrace_bounds {w : ℕ} (first second : FixedBinaryWord w) :
    listCells (ltWithTrace first second).2+arraySlots (ltWithTrace first second).2≤6*(w+1)^2+8 ∧
    framePeak (ltWithTrace first second).2≤2*w+4 := by
  have hs := BinaryDivisionAllocation.borrowStorage_bound first.bits second.bits w first.size.le second.size.le
  simp only [ltWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

theorem prepare_all_prefix (seed : List Bool) (borrowedOtherCells steps : ℕ) :
    retainedHeap (seed.length+borrowedOtherCells) (prepareWithTrace seed).2 steps≤
      seed.length+borrowedOtherCells+46*seed.length+20 :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (prepareWithTrace_bounds seed).1

theorem lookup_all_prefix (store : Store) (address : FixedBinaryWord store.width)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (storeCells store+address.bits.length+originalSeedCells+borrowedOtherCells) (lookupWithTrace store address).2 steps≤
      storeCells store+address.bits.length+originalSeedCells+borrowedOtherCells+5*store.width+12 :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (lookupWithTrace_bounds store address).1

end Blotto.BinaryWordStoreLifetime

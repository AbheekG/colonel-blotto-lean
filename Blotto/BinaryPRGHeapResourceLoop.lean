import Blotto.BinaryPRGHeapResourcePair
import Blotto.BinaryPRGHeapResourceUpdate
import Blotto.BinaryPRGHeapPackedStore

/-! A reached resource phase retains tape heaps and Boolean active identifiers.
Its logical resource state exists only in an erased existential certificate,
including across recursive calls. Pair operands and selected writes use the
physical stores. Uniform whole-run costs, data-only observer erasure,
input/materialization and all-regime continuations/space remain separate. -/

namespace Blotto.BinaryPRGHeapResourceLoop
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourceLoop
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceUpdate (Physical)
open BinaryPRGWordStoreHeap (Heap Pointer Realizes Valid)
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

structure Finished (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value) where
  ruler : List Bool
  size : ruler.length = capacity.width
  heap : Heap
  root : Pointer
  valid : Valid heap
  active : List (Address capacity.width capacity.cap)
  certified : ∃ state : Certified capacity n hCount,
    Realizes heap.tape root state.state.resource ∧ active = state.state.active

noncomputable def Finished.reference (result : Finished capacity n hCount) : Certified capacity n hCount :=
  result.certified.choose

noncomputable def Finished.data (result : Finished capacity n hCount) : Physical result.reference.state :=
  ⟨⟨result.ruler,result.size,result.heap,result.root,result.valid,result.certified.choose_spec.1⟩,
    result.active,result.certified.choose_spec.2⟩

def Finished.packed (result : Finished capacity n hCount) : Packed capacity.width :=
  ⟨result.ruler,result.size,result.heap,result.root,result.valid,by
    obtain ⟨state,hRealizes,_⟩ := result.certified
    exact ⟨state.state.resource,hRealizes⟩⟩

theorem Finished.packed_realizes (result : Finished capacity n hCount) :
    Realizes result.packed.heap.tape result.packed.root result.reference.state.resource :=
  result.certified.choose_spec.1

def finished (state : Certified capacity n hCount) (data : Physical state.state) : Finished capacity n hCount :=
  ⟨data.resource.ruler,data.resource.size,data.resource.heap,data.resource.root,data.resource.valid,
    data.active,⟨state,data.resource.realizes,data.active_eq⟩⟩

theorem state_ext (first second : State capacity.width capacity.cap)
    (hResource : first.resource = second.resource) (hActive : first.active = second.active) : first = second := by
  cases first
  cases second
  cases hResource
  cases hActive
  rfl

theorem certified_ext (first second : Certified capacity n hCount) (h : first.state = second.state) : first = second := by
  cases first
  cases second
  cases h
  rfl

theorem finished_reference (state : Certified capacity n hCount) (data : Physical state.state) :
    (finished state data).reference = state := by
  apply certified_ext
  apply state_ext
  · exact BinaryPRGHeapStoredTree.realizes_unique (finished state data).certified.choose_spec.1 data.resource.realizes
  · exact (finished state data).certified.choose_spec.2.symm.trans data.active_eq

theorem Finished.reference_eq (result : Finished capacity n hCount)
    (candidate : Certified capacity n hCount)
    (hResource : Realizes result.heap.tape result.root candidate.state.resource)
    (hActive : result.active = candidate.state.active) : result.reference = candidate := by
  apply certified_ext
  apply state_ext
  · exact BinaryPRGHeapStoredTree.realizes_unique result.certified.choose_spec.1 hResource
  · exact result.certified.choose_spec.2.symm.trans hActive

theorem Finished.active_length_le (result : Finished capacity n hCount) :
    result.active.length ≤ n := by
  have h := result.reference.reference.nodup.length_le_card
  rw [result.reference.reference_state] at h
  change (result.reference.state.active.map
    (fun address => address.index n hCount)).length ≤ Fintype.card (Fin n) at h
  simp only [List.length_map,Fintype.card_fin] at h
  calc
    result.active.length = result.reference.state.active.length :=
      congrArg List.length result.certified.choose_spec.2
    _ ≤ n := h

abbrev Result (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value) :=
  Option (Finished capacity n hCount) × FixedBinaryWord seed.width

noncomputable def Result.reference {seed : BinarySeedLookupTree.Store}
    (result : Result seed capacity n hCount) : BinaryPRGWordControllerBooleanResourceLoop.Result seed capacity n hCount :=
  (result.1.map Finished.reference,result.2)

def sourceWithWork (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : BinaryRationalPairProgram.Source × ℕ :=
  let a := BinaryPRGHeapStoredTree.readWithWork limits first.word
  let b := BinaryPRGHeapStoredTree.readWithWork limits second.word
  let c := state.packed.readWithWork first.word
  let d := state.packed.readWithWork second.word
  (⟨a.1,b.1,c.1,d.1,
    (by simpa only [a,BinaryPRGHeapStoredTree.readWithWork_value] using hC first),
    (by simpa only [b,BinaryPRGHeapStoredTree.readWithWork_value] using hC second),
    (by simpa only [c,BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes] using state.reference.canonical first),
    (by simpa only [d,BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes] using state.reference.canonical second),
    (by
      have hm : first ∈ state.reference.state.active := by
        have hh : state.reference.state.active = first :: second :: tail := state.certified.choose_spec.2.symm.trans he
        rw [hh]
        simp
      have hi := state.reference.interior first hm
      simpa only [c,a,BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes,
        BinaryPRGHeapStoredTree.readWithWork_value] using hi),
    (by
      have hm : second ∈ state.reference.state.active := by
        have hh : state.reference.state.active = first :: second :: tail := state.certified.choose_spec.2.symm.trans he
        rw [hh]
        simp
      have hi := state.reference.interior second hm
      simpa only [d,b,BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes,
        BinaryPRGHeapStoredTree.readWithWork_value] using hi)⟩,
    a.2.work + b.2.work + c.2.work + d.2.work + 8)

theorem sourceWithWork_value (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (sourceWithWork (hC := hC) limits state first second tail he).1 =
      BinaryPRGWordControllerBooleanResourcePair.source capacity.tree state.reference.state
        first second tail hC state.reference.canonical state.reference.interior
        (state.certified.choose_spec.2.symm.trans he) := by
  unfold sourceWithWork BinaryPRGWordControllerBooleanResourcePair.source
  dsimp only
  simp only [BinaryPRGHeapStoredTree.readWithWork_value,
    BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes]

def pairWithWork (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : BinaryPRGWordControllerPairOutputs.Outputs × ℕ :=
  let input := sourceWithWork (hC := hC) limits state first second tail he
  let outputs := BinaryPRGWordControllerPairOutputs.prepareWithWork input.1
  (outputs.1,input.2 + input.1.sourcePayloadWork + outputs.2 + 4)

noncomputable def logicalChoice (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : Choice capacity n hCount hC :=
  Choice.prepare hC state.reference first second tail (state.data.active_eq.symm.trans he)

theorem prepare_pair (state : Certified capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.state.active = first :: second :: tail) :
    BinaryPRGWordControllerBooleanResourceLoop.prepare capacity n hCount hC state =
      .ask (Choice.prepare hC state first second tail he) := by
  cases state with
  | mk data certified =>
    cases data with
    | mk resource active =>
      cases he
      rfl

theorem prepare_nil (state : Certified capacity n hCount)
    (he : state.state.active = []) :
    BinaryPRGWordControllerBooleanResourceLoop.prepare capacity n hCount hC state = .done state := by
  cases state with
  | mk data certified =>
    cases data with
    | mk resource active =>
      cases he
      rfl

theorem prepare_singleton (state : Certified capacity n hCount)
    (first : Address capacity.width capacity.cap) (he : state.state.active = [first]) :
    BinaryPRGWordControllerBooleanResourceLoop.prepare capacity n hCount hC state = .done state := by
  cases state with
  | mk data certified =>
    cases data with
    | mk resource active =>
      cases he
      rfl

theorem pairWithWork_value (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (pairWithWork (hC := hC) limits state first second tail he).1 =
      (logicalChoice (hC := hC) state first second tail he).outputs := by
  unfold pairWithWork logicalChoice Choice.prepare
  rw [BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure,sourceWithWork_value]
  rfl

noncomputable def physicalChoice (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : Choice capacity n hCount hC :=
  { state := state.reference
    first := first
    second := second
    tail := tail
    head_pair := state.certified.choose_spec.2.symm.trans he
    outputs := (pairWithWork (hC := hC) limits state first second tail he).1
    outputs_correct := by
      rw [pairWithWork_value]
      rfl }

theorem choice_ext (first second : Choice capacity n hCount hC)
    (hs : first.state = second.state) (hf : first.first = second.first)
    (hb : first.second = second.second) (ht : first.tail = second.tail)
    (ho : first.outputs = second.outputs) : first = second := by
  cases first
  cases second
  cases hs
  cases hf
  cases hb
  cases ht
  cases ho
  rfl

theorem physicalChoice_eq (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    physicalChoice (hC := hC) limits state first second tail he =
      logicalChoice (hC := hC) state first second tail he := by
  apply choice_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact pairWithWork_value (hC := hC) limits state first second tail he

theorem prepare_physicalChoice (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    BinaryPRGWordControllerBooleanResourceLoop.prepare capacity n hCount hC state.reference =
      .ask (physicalChoice (hC := hC) limits state first second tail he) := by
  rw [physicalChoice_eq]
  exact prepare_pair (hC := hC) state.reference first second tail (state.certified.choose_spec.2.symm.trans he)

def fractionalWithWork (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : Bool × ℕ :=
  let bid := bids.readWithWork address.word
  let limit := BinaryPRGHeapStoredTree.readWithWork limits address.word
  ((!BinaryRationalArithmetic.lessEqual bid.1 BinaryRationalOpcode.zero) &&
    (!BinaryRationalArithmetic.lessEqual limit.1 bid.1),
    bid.2.work + limit.2.work + BinaryRationalArithmetic.lessEqualWork bid.1 BinaryRationalOpcode.zero +
      BinaryRationalArithmetic.lessEqualWork limit.1 bid.1 + 6)

theorem fractionalWithWork_value (limits : Stored capacity.tree) (bids : Packed capacity.width)
    {resource : BinaryPRGWordControllerWordStore.Tree capacity.width}
    (h : Realizes bids.heap.tape bids.root resource)
    (address : Address capacity.width capacity.cap) :
    (fractionalWithWork limits bids address).1 = fractional capacity.tree resource address := by
  simp only [fractionalWithWork,fractional,
    BinaryPRGHeapPackedStore.Packed.readWithWork_value bids h,
    BinaryPRGHeapStoredTree.readWithWork_value]

def fractionalWorkBoundRaw {depth : ℕ} {cap : FixedBinaryWord depth}
    {tree : BinaryPRGWordControllerWordStore.Tree depth}
    (limits : Stored tree) (bids : Packed depth) (address : Address depth cap) : ℕ :=
  let bid := bids.readWithWork address.word
  let limit := BinaryPRGHeapStoredTree.readWithWork limits address.word
  BinaryPRGHeapStoredTree.readBound bids.heap.tape.length address.word.bits.length +
    BinaryPRGHeapStoredTree.readBound limits.heap.tape.length address.word.bits.length +
    500 * (BinaryRationalArithmetic.pairWidth bid.1 BinaryRationalOpcode.zero + 1) ^ 2 +
    500 * (BinaryRationalArithmetic.pairWidth limit.1 bid.1 + 1) ^ 2 + 6

def fractionalWorkBound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : ℕ :=
  fractionalWorkBoundRaw limits bids address

theorem fractionalWithWork_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (fractionalWithWork limits bids address).2 ≤ fractionalWorkBound limits bids address := by
  have hBid := bids.readWithWork_bounds address.word
  have hLimit := BinaryPRGHeapStoredTree.readWithWork_bounds limits address.word
  have hFirst := BinaryRationalArithmetic.lessEqualWork_bound
    (bids.readWithWork address.word).1 BinaryRationalOpcode.zero
  have hSecond := BinaryRationalArithmetic.lessEqualWork_bound
    (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
    (bids.readWithWork address.word).1
  unfold fractionalWithWork fractionalWorkBound fractionalWorkBoundRaw
  dsimp only
  rw [address.word.size]
  omega

def scanWithWork (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) → List (Address capacity.width capacity.cap) × ℕ
  | [] => ([],1)
  | address :: rest =>
      let tested := fractionalWithWork limits bids address
      let later := scanWithWork limits bids rest
      (if tested.1 then address :: later.1 else later.1,
        tested.2 + later.2 + 2 * (address.word.bits.length + 1) + 3)

theorem scanWithWork_value (limits : Stored capacity.tree) (bids : Packed capacity.width)
    {resource : BinaryPRGWordControllerWordStore.Tree capacity.width}
    (h : Realizes bids.heap.tape bids.root resource)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithWork limits bids addresses).1 = addresses.filter (fractional capacity.tree resource) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanWithWork,fractionalWithWork_value limits bids h,List.filter_cons,ih]

def scanWorkBound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) : ℕ :=
  (addresses.map (fun address => fractionalWorkBound limits bids address +
    2 * (address.word.bits.length + 1) + 3)).sum + 1

def scanWorkBoundRaw {depth : ℕ} {cap : FixedBinaryWord depth}
    {tree : BinaryPRGWordControllerWordStore.Tree depth}
    (limits : Stored tree) (bids : Packed depth)
    (addresses : List (Address depth cap)) : ℕ :=
  (addresses.map (fun address => fractionalWorkBoundRaw limits bids address +
    2 * (address.word.bits.length + 1) + 3)).sum + 1

theorem scanWorkBound_eq_raw (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    scanWorkBound limits bids addresses = scanWorkBoundRaw limits bids addresses := by
  rfl

def fractionalWorkBoundPacked {depth : ℕ} {cap : FixedBinaryWord depth}
    (limits bids : Packed depth) (address : Address depth cap) : ℕ :=
  let bid := bids.readWithWork address.word
  let limit := limits.readWithWork address.word
  BinaryPRGHeapStoredTree.readBound bids.heap.tape.length address.word.bits.length +
    BinaryPRGHeapStoredTree.readBound limits.heap.tape.length address.word.bits.length +
    500 * (BinaryRationalArithmetic.pairWidth bid.1 BinaryRationalOpcode.zero + 1) ^ 2 +
    500 * (BinaryRationalArithmetic.pairWidth limit.1 bid.1 + 1) ^ 2 + 6

def scanWorkBoundPacked {depth : ℕ} {cap : FixedBinaryWord depth}
    (limits bids : Packed depth) (addresses : List (Address depth cap)) : ℕ :=
  (addresses.map (fun address => fractionalWorkBoundPacked limits bids address +
    2 * (address.word.bits.length + 1) + 3)).sum + 1

theorem scanWorkBound_eq_packed (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    scanWorkBound limits bids addresses =
      scanWorkBoundPacked (BinaryPRGHeapPackedStore.pack limits) bids addresses := by
  rfl

theorem scanWithWork_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithWork limits bids addresses).2 ≤ scanWorkBound limits bids addresses := by
  induction addresses with
  | nil => simp [scanWithWork,scanWorkBound]
  | cons address rest ih =>
      have hTest := fractionalWithWork_bound limits bids address
      unfold scanWorkBound at ih
      simp only [scanWithWork,scanWorkBound,List.map_cons,List.sum_cons]
      omega

def updateWithWork (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (Packed capacity.width × List (Address capacity.width capacity.cap)) × ℕ :=
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let intermediate := state.packed.writeWithWork first.word chosen
  let next := intermediate.1.writeWithWork second.word other.1
  let retained := scanWithWork limits next.1 [first,second]
  ((next.1,retained.1 ++ tail),
    a.2.work + b.2.work + total.2 + other.2 + intermediate.2.work + next.2.work + retained.2 +
      2 * (first.word.bits.length + 1) * (tail.length + 2) + 12)

theorem updateWithWork_refines (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    Realizes (updateWithWork limits state first second tail chosen).1.1.heap.tape
      (updateWithWork limits state first second tail chosen).1.1.root
      (update capacity.tree state.reference.state first second tail chosen).resource ∧
    (updateWithWork limits state first second tail chosen).1.2 =
      (update capacity.tree state.reference.state first second tail chosen).active := by
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let intermediate := state.packed.writeWithWork first.word chosen
  let next := intermediate.1.writeWithWork second.word other.1
  have hFirst := BinaryPRGHeapPackedStore.Packed.writeWithWork_realizes state.packed
    state.packed_realizes first.word chosen
  have hSecond := BinaryPRGHeapPackedStore.Packed.writeWithWork_realizes intermediate.1
    hFirst second.word other.1
  have hTree : BinaryPRGWordControllerWordStore.write
      (BinaryPRGWordControllerWordStore.write state.reference.state.resource first.word chosen)
      second.word other.1 =
      (update capacity.tree state.reference.state first second tail chosen).resource := by
    dsimp only [other,total,a,b]
    simp only [BinaryPRGWordControllerBooleanResourceUpdate.update,
      BinaryQuadraticData.apply_erasure,
      BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes]
  have hNext : Realizes next.1.heap.tape next.1.root
      (update capacity.tree state.reference.state first second tail chosen).resource := by
    rw [← hTree]
    exact hSecond
  have hActive : (scanWithWork limits next.1 [first,second]).1 ++ tail =
      (update capacity.tree state.reference.state first second tail chosen).active := by
    rw [scanWithWork_value limits next.1 hNext]
    rfl
  exact ⟨hNext,hActive⟩

def selectWithWork (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    Finished capacity n hCount × ℕ :=
  let chosen := if branch then outputs.upper else outputs.lower
  let selected := updateWithWork limits state first second tail chosen
  (⟨selected.1.1.ruler,selected.1.1.size,selected.1.1.heap,selected.1.1.root,
      selected.1.1.valid,selected.1.2,by
        let choice := logicalChoice (hC := hC) state first second tail he
        have hState : update capacity.tree state.reference.state first second tail chosen = (choice.select branch).state := by
          have ho := hOutputs
          change outputs = BinaryPRGWordControllerBooleanResourcePair.pair capacity.tree
            state.reference.state first second tail hC state.reference.canonical
            state.reference.interior (state.certified.choose_spec.2.symm.trans he) at ho
          dsimp [choice,logicalChoice,Choice.select,Choice.endpoint,Choice.prepare]
          simp only [chosen,ho]
        have hRefines := updateWithWork_refines limits state first second tail chosen
        refine ⟨choice.select branch,?_,?_⟩
        · exact hState ▸ hRefines.1
        · exact hState ▸ hRefines.2⟩,selected.2)

theorem selectWithWork_reference (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    (selectWithWork limits state first second tail he outputs hOutputs branch).1.reference =
      (logicalChoice (hC := hC) state first second tail he).select branch := by
  let chosen := if branch then outputs.upper else outputs.lower
  let selected := updateWithWork limits state first second tail chosen
  have hState : update capacity.tree state.reference.state first second tail chosen =
      ((logicalChoice (hC := hC) state first second tail he).select branch).state := by
    have ho := hOutputs
    change outputs = BinaryPRGWordControllerBooleanResourcePair.pair capacity.tree
      state.reference.state first second tail hC state.reference.canonical
      state.reference.interior (state.certified.choose_spec.2.symm.trans he) at ho
    dsimp [chosen,logicalChoice,Choice.select,Choice.endpoint,Choice.prepare]
    simp only [ho]
  have hRefines := updateWithWork_refines limits state first second tail chosen
  apply Finished.reference_eq
  · change Realizes selected.1.1.heap.tape selected.1.1.root
        ((logicalChoice (hC := hC) state first second tail he).select branch).state.resource
    exact hState ▸ hRefines.1
  · change selected.1.2 = ((logicalChoice (hC := hC) state first second tail he).select branch).state.active
    exact hState ▸ hRefines.2

theorem selectWithWork_progress (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    (selectWithWork limits state first second tail he outputs hOutputs branch).1.active.length < state.active.length := by
  let next := (selectWithWork limits state first second tail he outputs hOutputs branch).1
  have h := (logicalChoice (hC := hC) state first second tail he).select_progress branch
  rw [← selectWithWork_reference limits state first second tail he outputs hOutputs branch] at h
  change next.reference.state.active.length < state.reference.state.active.length at h
  rw [← next.data.active_eq,← state.data.active_eq] at h
  exact h

def runWithWork (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Result seed capacity n hCount × ℕ :=
  match he : state.active with
  | first :: second :: tail =>
      let prepared := pairWithWork (hC := hC) limits state first second tail he
      let coin := BinaryWordIndexCoinController.sample seed prepared.1.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),prepared.2 + coin.2 + 4)
      | some branch =>
          let selected := selectWithWork limits state first second tail he prepared.1 (pairWithWork_value _ _ _ _ _ _) branch
          let later := runWithWork seed limits hC selected.1 coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds seed prepared.1.probability pc hp).2
          (later.1,prepared.2 + coin.2 + selected.2 + later.2 + 8)
  | _ => ((some state,pc),2)
termination_by state.active.length
decreasing_by
  exact selectWithWork_progress limits state first second tail he prepared.1 _ branch

theorem runWithWork_value (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithWork seed limits hC state pc hp).1.reference =
      BinaryPRGWordControllerBooleanResourceLoop.run seed capacity n hCount hC state.reference pc hp := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount)
      (q : FixedBinaryWord seed.width) (hq : q.value ≤ seed.cap.value), s.active.length ≤ fuel →
      (runWithWork seed limits hC s q hq).1.reference =
        BinaryPRGWordControllerBooleanResourceLoop.run seed capacity n hCount hC s.reference q hq from
    h state.active.length state pc hp le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro state pc hp hSize
      conv_lhs => unfold runWithWork
      split
      · rename_i first second tail he
        have hPrepare := prepare_physicalChoice (hC := hC) limits state first second tail he
        conv_rhs => unfold BinaryPRGWordControllerBooleanResourceLoop.run
        rw [hPrepare]
        dsimp only
        simp only [← BinaryPRGWordControllerDataCoin.sample_erasure seed
          (physicalChoice (hC := hC) limits state first second tail he).probability pc hp]
        have hProbability : (physicalChoice (hC := hC) limits state first second tail he).probability =
            (pairWithWork (hC := hC) limits state first second tail he).1.probability := rfl
        simp only [hProbability]
        split
        · rename_i _ hCoin
          simp only [hCoin,Result.reference,Option.map_none]
        · rename_i _ branch hCoin
          simp only [hCoin,Result.reference]
          let outputs := (pairWithWork (hC := hC) limits state first second tail he).1
          let next := (selectWithWork limits state first second tail he outputs
            (pairWithWork_value (hC := hC) limits state first second tail he) branch).1
          have hNext : next.reference =
              (physicalChoice (hC := hC) limits state first second tail he).select branch := by
            calc
              next.reference = (logicalChoice (hC := hC) state first second tail he).select branch :=
                selectWithWork_reference limits state first second tail he outputs _ branch
              _ = (physicalChoice (hC := hC) limits state first second tail he).select branch := by
                rw [physicalChoice_eq]
          rw [← hNext]
          have hProgress : next.active.length < state.active.length :=
            selectWithWork_progress limits state first second tail he outputs _ branch
          have hFuel : next.active.length < fuel := hProgress.trans_le hSize
          exact ih next.active.length hFuel next
            (BinaryWordIndexCoinController.sample seed outputs.probability pc hp).1.2
            (BinaryWordIndexCoinController.sample_position_bounds seed outputs.probability pc hp).2 le_rfl
      · rename_i hNoPair
        have hShort : state.active = [] ∨ ∃ first : Address capacity.width capacity.cap, state.active = [first] := by
          cases ha : state.active with
          | nil => exact Or.inl rfl
          | cons first rest =>
              cases rest with
              | nil => exact Or.inr ⟨first,rfl⟩
              | cons second tail => exact False.elim (hNoPair first second tail ha)
        cases hShort with
        | inl hNil =>
            have hRef : state.reference.state.active = [] := state.certified.choose_spec.2.symm.trans hNil
            conv_rhs => unfold BinaryPRGWordControllerBooleanResourceLoop.run
            rw [prepare_nil (hC := hC) state.reference hRef]
            rfl
        | inr hSingle =>
            obtain ⟨first,hSingle⟩ := hSingle
            have hRef : state.reference.state.active = [first] := state.certified.choose_spec.2.symm.trans hSingle
            conv_rhs => unfold BinaryPRGWordControllerBooleanResourceLoop.run
            rw [prepare_singleton (hC := hC) state.reference first hRef]
            rfl

theorem runWithWork_position (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    pc.value ≤ (runWithWork seed limits hC state pc hp).1.2.value ∧
      (runWithWork seed limits hC state pc hp).1.2.value ≤ seed.cap.value := by
  change pc.value ≤ (runWithWork seed limits hC state pc hp).1.reference.2.value ∧
    (runWithWork seed limits hC state pc hp).1.reference.2.value ≤ seed.cap.value
  rw [runWithWork_value]
  exact BinaryPRGWordControllerBooleanResourceLoop.run_position seed capacity n hCount hC state.reference pc hp

noncomputable def Result.original {seed : BinarySeedLookupTree.Store}
    (result : Result seed capacity n hCount) :
    BinaryPRGWordControllerResource.Result seed
      (BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount) :=
  result.reference.original

theorem runWithWork_original (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((runWithWork seed limits hC state pc hp).1).original =
      BinaryPRGWordControllerResource.run seed
        (BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount)
        (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
        state.reference.reference pc hp := by
  unfold Result.original
  rw [runWithWork_value]
  exact BinaryPRGWordControllerBooleanResourceLoop.run_original
    seed capacity n hCount hC state.reference pc hp

end Blotto.BinaryPRGHeapResourceLoop

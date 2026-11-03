import Blotto.BinaryQuadraticResourcePairLifetime
import Blotto.BinaryWordCoinLifetime
import Blotto.BinaryPRGWordControllerBooleanResourceSourceWork

/-! Source reservations for the actual Boolean resource initialization and
selected path-copy updates. Arithmetic uses the quadratic producer, tests use
the unchanged signed cross-product comparison, and identifiers/cursors stay
Boolean words. Every old region remains retained; proof-only native views
derive widths but execute no native SSA. Reservations count list/reference
slots and source activations, not physical integer or pointer encodings. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticResourceStateLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerBooleanResourceUpdate BinaryPRGWordControllerBooleanResourceLoop

def cells (trace : Trace) : ℕ := listCells trace + arraySlots trace
@[simp] theorem cells_append (a b : Trace) : cells (a ++ b) = cells a + cells b := by
  simp [cells]; omega
@[simp] theorem cells_under (depth : ℕ) (trace : Trace) : cells (under depth trace) = cells trace := by simp [cells]

def compareWithTrace (first second : SignedWord) : Bool × Trace :=
  let result := BinaryRationalOpcodeAllocation.lessEqualWithAllocation first second
  (result.1,[.frames (200 * (BinaryRationalArithmetic.pairWidth first second + 1)^2 + 8),
    .arrayAllocation 16,.listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage first second)])

@[simp] theorem compareWithTrace_erases (first second : SignedWord) :
    (compareWithTrace first second).1 = BinaryRationalArithmetic.lessEqual first second :=
  BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state _ _

def compareBound (W : ℕ) : ℕ := 2500 * (W + 1)^3 + 16
def compareFrames (W : ℕ) : ℕ := 200 * (W + 1)^2 + 8
theorem compareWithTrace_bounds (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) :
    cells (compareWithTrace first second).2 ≤ compareBound W ∧
      framePeak (compareWithTrace first second).2 ≤ compareFrames W := by
  have hWidth : BinaryRationalArithmetic.pairWidth first second ≤ W := max_le hA hB
  have h := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound first second).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right hWidth 1) 3))
  have hf := Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (Nat.add_le_add_right hWidth 1) 2)
  simp only [compareWithTrace,cells,listCells,arraySlots,framePeak,compareBound,compareFrames]
  exact ⟨by omega,by omega⟩

def fractionalWithTrace {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w)
    (address : Address w cap) : Bool × Trace :=
  let bid := BinaryQuadraticResourcePairLifetime.lookupWithTrace resource address.word
  let limit := BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity address.word
  let positive := compareWithTrace bid.1 BinaryRationalOpcode.zero
  let below := compareWithTrace limit.1 bid.1
  ((!positive.1) && (!below.1),[.frames 2,.arrayAllocation 16] ++
    under 2 bid.2 ++ under 2 limit.2 ++ under 2 positive.2 ++ under 2 below.2)

@[simp] theorem fractionalWithTrace_erases {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w)
    (address : Address w cap) : (fractionalWithTrace capacity resource address).1 = fractional capacity resource address := by
  simp only [fractionalWithTrace,BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,compareWithTrace_erases,fractional]

def fractionalBound (w W : ℕ) : ℕ := 10 * w + 40 + 2 * compareBound W
def fractionalFrames (w W : ℕ) : ℕ := w + compareFrames W + 7
theorem fractionalWithTrace_bounds {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w)
    (address : Address w cap) (W : ℕ) (hW : 1 ≤ W)
    (hC : width (lookup capacity address.word) ≤ W) (hR : width (lookup resource address.word) ≤ W) :
    cells (fractionalWithTrace capacity resource address).2 ≤ fractionalBound w W ∧
      framePeak (fractionalWithTrace capacity resource address).2 ≤ fractionalFrames w W := by
  have hb := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds resource address.word
  have hl := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds capacity address.word
  have hp := compareWithTrace_bounds (lookup resource address.word) BinaryRationalOpcode.zero W hR hW
  have hc := compareWithTrace_bounds (lookup capacity address.word) (lookup resource address.word) W hC hR
  have bf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace resource address.word).2
  have lf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity address.word).2
  have pf := framePeak_under 2 (compareWithTrace (lookup resource address.word) BinaryRationalOpcode.zero).2
  have cf := framePeak_under 2 (compareWithTrace (lookup capacity address.word) (lookup resource address.word)).2
  simp only [cells] at hp hc
  unfold fractionalWithTrace fractionalBound fractionalFrames
  simp only [BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,cells_append,cells_under,
    cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

def scanWithTrace {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w) :
    List (Address w cap) → List (Address w cap) × Trace
  | [] => ([],[.frames 1,.arrayAllocation 4])
  | address :: rest =>
      let tested := fractionalWithTrace capacity resource address
      let later := scanWithTrace capacity resource rest
      (if tested.1 then address :: later.1 else later.1,
        [.frames 2,.arrayAllocation 8,.listAllocation (if tested.1 then 1 else 0)] ++ under 2 tested.2 ++ under 1 later.2)

@[simp] theorem scanWithTrace_erases {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w)
    (addresses : List (Address w cap)) : (scanWithTrace capacity resource addresses).1 = addresses.filter (fractional capacity resource) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [scanWithTrace,fractionalWithTrace_erases,List.filter_cons,ih]

theorem scanWithTrace_bounds {w : ℕ} {cap : FixedBinaryWord w} (capacity resource : Tree w)
    (addresses : List (Address w cap)) (W : ℕ) (hW : 1 ≤ W)
    (hC : ∀ address ∈ addresses,width (lookup capacity address.word) ≤ W)
    (hR : ∀ address ∈ addresses,width (lookup resource address.word) ≤ W) :
    cells (scanWithTrace capacity resource addresses).2 ≤ addresses.length * (fractionalBound w W + 9) + 4 ∧
      framePeak (scanWithTrace capacity resource addresses).2 ≤ addresses.length + fractionalFrames w W + 3 := by
  induction addresses with
  | nil => simp [scanWithTrace,cells,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have hc := fractionalWithTrace_bounds capacity resource address W hW (hC address (by simp)) (hR address (by simp))
      have hr := ih (fun address hm => hC address (by simp [hm])) (fun address hm => hR address (by simp [hm]))
      have cf := framePeak_under 2 (fractionalWithTrace capacity resource address).2
      have rf := framePeak_under 1 (scanWithTrace capacity resource rest).2
      simp only [cells] at hc hr
      simp only [scanWithTrace,cells_append,cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,List.length_cons]
      split <;> exact ⟨by nlinarith only [hc.1,hr.1],by omega⟩

def updateWithTrace {w : ℕ} {cap : FixedBinaryWord w} (capacity : Tree w) (state : State w cap)
    (first second : Address w cap) (tail : List (Address w cap)) (chosen : SignedWord) : State w cap × Trace :=
  let a := BinaryQuadraticResourcePairLifetime.lookupWithTrace state.resource first.word
  let b := BinaryQuadraticResourcePairLifetime.lookupWithTrace state.resource second.word
  let total := BinaryQuadraticLifetime.applyWithTrace .add a.1 b.1
  let other := BinaryQuadraticLifetime.applyWithTrace .sub total.1 chosen
  let intermediate := BinaryQuadraticResourcePairLifetime.writeWithTrace state.resource first.word chosen
  let next := BinaryQuadraticResourcePairLifetime.writeWithTrace intermediate.1 second.word other.1
  let retained := scanWithTrace capacity next.1 [first,second]
  (⟨next.1,retained.1 ++ tail⟩,[.frames 2,.arrayAllocation 32,.listAllocation (2 + retained.1.length)] ++
    under 2 a.2 ++ under 2 b.2 ++ under 2 total.2 ++ under 2 other.2 ++
    under 2 intermediate.2 ++ under 2 next.2 ++ under 2 retained.2)

@[simp] theorem updateWithTrace_erases {w : ℕ} {cap : FixedBinaryWord w} (capacity : Tree w) (state : State w cap)
    (first second : Address w cap) (tail : List (Address w cap)) (chosen : SignedWord) :
    (updateWithTrace capacity state first second tail chosen).1 = BinaryPRGWordControllerBooleanResourceUpdate.update capacity state first second tail chosen := by
  simp only [updateWithTrace,BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,
    BinaryQuadraticResourcePairLifetime.writeWithTrace_erases,BinaryQuadraticLifetime.applyWithTrace_erases,scanWithTrace_erases,
    BinaryPRGWordControllerBooleanResourceUpdate.update]

def updateBound (w W : ℕ) : ℕ := 28*w + 120 + 2*BinaryQuadraticLifetime.opcodeBound W + 2*fractionalBound w W
def updateFrames (w W : ℕ) : ℕ := w + BinaryQuadraticLifetime.opcodeFrames W + fractionalFrames w W + 10
theorem updateWithTrace_bounds {w : ℕ} {cap : FixedBinaryWord w} (capacity : Tree w) (state : State w cap)
    (first second : Address w cap) (tail : List (Address w cap)) (chosen : SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hBefore : ∀ address : Address w cap,width (lookup state.resource address.word) ≤ W)
    (hCap : ∀ address : Address w cap,width (lookup capacity address.word) ≤ W)
    (hChosen : width chosen ≤ W)
    (hTotal : width (BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)) ≤ W)
    (hOther : width (BinaryQuadraticData.apply .sub
      (BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)) chosen) ≤ W) :
    cells (updateWithTrace capacity state first second tail chosen).2 ≤ updateBound w W ∧
      framePeak (updateWithTrace capacity state first second tail chosen).2 ≤ updateFrames w W := by
  let added := BinaryQuadraticData.apply .add (lookup state.resource first.word) (lookup state.resource second.word)
  let other := BinaryQuadraticData.apply .sub added chosen
  let next := write (write state.resource first.word chosen) second.word other
  have hAfter : ∀ address : Address w cap,width (lookup next address.word) ≤ W := by
    intro address
    dsimp only [next]
    rw [lookup_write,lookup_write]
    split
    · exact hOther
    · split
      · exact hChosen
      · exact hBefore address
  have ha := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds state.resource first.word
  have hb := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds state.resource second.word
  have ht := BinaryQuadraticLifetime.applyWithTrace_bounds .add _ _ W (hBefore first) (hBefore second)
  have ho := BinaryQuadraticLifetime.applyWithTrace_bounds .sub added chosen W hTotal hChosen
  have hf := BinaryQuadraticResourcePairLifetime.writeWithTrace_bounds state.resource first.word chosen
  have hs := BinaryQuadraticResourcePairLifetime.writeWithTrace_bounds (write state.resource first.word chosen) second.word other
  have hr := scanWithTrace_bounds capacity next [first,second] W hW (fun address _ => hCap address) (fun address _ => hAfter address)
  have hLen : (scanWithTrace capacity next [first,second]).1.length ≤ 2 := by
    rw [scanWithTrace_erases]
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have af := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.resource first.word).2
  have bf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.resource second.word).2
  have tf := framePeak_under 2 (BinaryQuadraticLifetime.applyWithTrace .add (lookup state.resource first.word) (lookup state.resource second.word)).2
  have ofr := framePeak_under 2 (BinaryQuadraticLifetime.applyWithTrace .sub added chosen).2
  have ff := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.writeWithTrace state.resource first.word chosen).2
  have sf := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.writeWithTrace (write state.resource first.word chosen) second.word other).2
  have rf := framePeak_under 2 (scanWithTrace capacity next [first,second]).2
  simp only [cells] at hr
  unfold updateWithTrace updateBound updateFrames
  simp only [BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,BinaryQuadraticResourcePairLifetime.writeWithTrace_erases,
    BinaryQuadraticLifetime.applyWithTrace_erases,cells_append,cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  change _ ≤ _ ∧ _
  dsimp only [added,other,next] at ha hb ht ho hf hs hr hLen af bf tf ofr ff sf rf
  simp only [List.length_cons,List.length_nil] at hr
  exact ⟨by omega,by omega⟩

def addressesWithTrace (store : Store) (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) :
    List (Address store.width store.cap) × Trace :=
  let guard := BinaryWordStoreLifetime.ltWithTrace pc store.cap
  if hRead : guard.1 = true then
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryWordStoreLifetime.ltWithTrace_erases pc store.cap).symm.trans hRead
    let advanced := BinaryWordStoreLifetime.incrementWithTrace pc
    have hAdvance : advanced.1.1 = advance store pc hData := by simp only [advanced,BinaryWordStoreLifetime.incrementWithTrace_erases,advance]
    let later := addressesWithTrace store advanced.1.1 (hAdvance.symm ▸ advance_bound store pc hData)
    (⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hData⟩ :: later.1,
      [.frames 2,.arrayAllocation 16,.listAllocation 1] ++ under 2 guard.2 ++ under 2 advanced.2 ++ under 1 later.2)
  else ([],[.frames 2,.arrayAllocation 8] ++ under 2 guard.2)
termination_by store.cap.value - pc.value
decreasing_by
  rw [hAdvance]
  have hn := advance_value store pc hData
  have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

@[simp] theorem addressesWithTrace_erases (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (addressesWithTrace store pc hp).1 = BinaryPRGWordControllerBooleanResourceInitial.addresses store pc hp := by
  conv_lhs => unfold addressesWithTrace
  conv_rhs => unfold BinaryPRGWordControllerBooleanResourceInitial.addresses
  simp only [BinaryWordStoreLifetime.ltWithTrace_erases,BinaryWordStoreLifetime.incrementWithTrace_erases]
  split
  · rename_i hRead
    exact congrArg ((⟨pc,(BinaryIndexWord.lt_value pc store.cap).mp hRead⟩ : Address store.width store.cap) :: ·)
      (addressesWithTrace_erases store (advance store pc hRead) (advance_bound store pc hRead))
  · rfl
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hn := advance_value store pc hRead
  have hv := (BinaryIndexWord.lt_value pc store.cap).mp hRead
  omega

def addressStep (w : ℕ) : ℕ := 6*(w+1)^2 + 5*w + 50
theorem addressesWithTrace_bounds (store : Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    cells (addressesWithTrace store pc hp).2 ≤ (store.cap.value-pc.value+1)*addressStep store.width ∧
      framePeak (addressesWithTrace store pc hp).2 ≤ store.cap.value-pc.value + 2*store.width + 10 := by
  have hg := BinaryWordStoreLifetime.ltWithTrace_bounds pc store.cap
  have hi := BinaryWordStoreLifetime.incrementWithTrace_bounds pc
  unfold addressesWithTrace
  dsimp only
  split
  · rename_i hRead
    have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryWordStoreLifetime.ltWithTrace_erases pc store.cap).symm.trans hRead
    have ih := addressesWithTrace_bounds store (advance store pc hData) (advance_bound store pc hData)
    have hn := advance_value store pc hData
    have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
    have hRemain : store.cap.value-pc.value = (store.cap.value-(advance store pc hData).value)+1 := by omega
    have gf := framePeak_under 2 (BinaryWordStoreLifetime.ltWithTrace pc store.cap).2
    have inf := framePeak_under 2 (BinaryWordStoreLifetime.incrementWithTrace pc).2
    have lf := framePeak_under 1 (addressesWithTrace store (advance store pc hData) (advance_bound store pc hData)).2
    simp only [cells] at ih
    simp only [BinaryWordStoreLifetime.incrementWithTrace_erases,cells,cells_append,cells_under,listCells_append,arraySlots_append,
      listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
    change _ ≤ _ ∧ _
    unfold advance at ih lf
    dsimp only [advance] at hRemain hn
    unfold addressStep at ih ⊢
    rw [hRemain]
    exact ⟨by nlinarith only [hg.1,hi.1,ih.1],by omega⟩
  · have gf := framePeak_under 2 (BinaryWordStoreLifetime.ltWithTrace pc store.cap).2
    simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
    unfold addressStep
    exact ⟨by nlinarith only [hg.1],by omega⟩
termination_by store.cap.value - pc.value
decreasing_by
  have hRead : (BinaryWordStoreLifetime.ltWithTrace pc store.cap).1 = true := by assumption
  have hData : BinaryIndexWord.lt pc store.cap = true := (BinaryWordStoreLifetime.ltWithTrace_erases pc store.cap).symm.trans hRead
  have hn := advance_value store pc hData
  have hv := (BinaryIndexWord.lt_value pc store.cap).mp hData
  omega

def initialWithTrace (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (_hCap : resource.cap = hWidth.symm ▸ capacity.cap) : State capacity.width capacity.cap × Trace :=
  let addresses := addressesWithTrace capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  let scanned := scanWithTrace capacity.tree (hWidth ▸ resource.tree) addresses.1
  (⟨hWidth ▸ resource.tree,scanned.1⟩,
    [.frames (capacity.width+2),.arrayAllocation 16,.listAllocation capacity.width] ++ under 2 addresses.2 ++ under 2 scanned.2)

@[simp] theorem initialWithTrace_erases (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) :
    (initialWithTrace capacity resource hWidth hCap).1 = BinaryPRGWordControllerBooleanResourceInitial.initial capacity resource hWidth hCap := by
  simp only [initialWithTrace,addressesWithTrace_erases,scanWithTrace_erases,
    BinaryPRGWordControllerBooleanResourceInitial.initial,BinaryPRGWordControllerBooleanResourceInitial.allAddresses]

def initialBound (w W n : ℕ) : ℕ := (n+1)*addressStep w + n*(fractionalBound w W+9) + w + 20
def initialFrames (w W n : ℕ) : ℕ := n + 2*w + fractionalFrames w W + 15
theorem initialWithTrace_bounds (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) (W : ℕ) (hW : 1 ≤ W)
    (hC : ∀ address : Address capacity.width capacity.cap,width (lookup capacity.tree address.word) ≤ W)
    (hR : ∀ address : Address capacity.width capacity.cap,width (lookup (hWidth ▸ resource.tree) address.word) ≤ W) :
    cells (initialWithTrace capacity resource hWidth hCap).2 ≤ initialBound capacity.width W capacity.cap.value ∧
      framePeak (initialWithTrace capacity resource hWidth hCap).2 ≤ initialFrames capacity.width W capacity.cap.value := by
  let addresses := addressesWithTrace capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have ha := addressesWithTrace_bounds capacity (zeroIndex capacity) (by rw [zeroIndex_value]; exact Nat.zero_le _)
  have hLength : addresses.1.length = capacity.cap.value := by
    dsimp only [addresses]
    rw [addressesWithTrace_erases,BinaryPRGWordControllerBooleanResourceInitial.addresses_length,zeroIndex_value,Nat.sub_zero]
  have hs := scanWithTrace_bounds capacity.tree (hWidth ▸ resource.tree) addresses.1 W hW (fun address _ => hC address) (fun address _ => hR address)
  rw [hLength] at hs
  simp only [zeroIndex_value,Nat.sub_zero,cells] at ha hs
  have af := framePeak_under 2 addresses.2
  have sf := framePeak_under 2 (scanWithTrace capacity.tree (hWidth ▸ resource.tree) addresses.1).2
  unfold initialWithTrace initialBound initialFrames
  change _ ≤ _ ∧ _
  dsimp only [addresses] at hLength ha hs af sf
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

end Blotto.BinaryQuadraticResourceStateLifetime

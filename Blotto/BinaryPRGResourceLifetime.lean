import Blotto.BinaryPRGFrameCostJoin
import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryRationalOpcodeAllocation
import Blotto.BinaryRationalRegisterStorage

/-! Retained source workspace reservations for the data-only resource program.
Ghost work/allocation observers may be erased: exact data-result/position
correspondence is retained. Registers use the actual opcode allocation producer;
selected updates reserve both opcode workspaces, comparison buffers and old/new
arrays. Coin buffers and active-list construction are separate allocations.
All reservations remain live until return, without unique ownership or GC.
These are abstract Boolean/payload/reference slots and source activations;
finite-binary scalar/record and native backend interpretations remain explicit.
-/
set_option autoImplicit false

namespace Blotto.BinaryPRGResourceLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryGeneralResourceRun BinaryGeneralResourceChoice BinaryResourcePair
open BinaryGeneralResourceLattice BinaryGeneralResourceExecution BinaryPRGResourceWork
open BinaryRationalRegisterProgram RationalLottoResourceSystem
open scoped BigOperators

-- The arithmetic call comes from the existing structural allocation producer.
-- Pushing may copy the complete reference array; all versions remain reserved.
def registersWithTrace : List RealArithmeticInstruction → Array SignedWord → Array SignedWord × Trace
  | [], registers => (registers,[.frames 1])
  | instruction :: rest, registers =>
      let left := read registers instruction.left
      let right := read registers instruction.right
      let result := BinaryRationalOpcodeAllocation.applyWithAllocation instruction.op left right
      let next := registers.push result.1
      let later := registersWithTrace rest next
      (later.1,[.frames 1,.listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage instruction.op left right),
        .arrayAllocation (next.size+1)] ++ under 1 later.2)

theorem registersWithTrace_state (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    (registersWithTrace program registers).1 = BinaryRationalRegisterProgram.run program registers := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [registersWithTrace,ih,BinaryRationalOpcodeAllocation.applyWithAllocation_state,
        BinaryRationalRegisterProgram.run,execute]

theorem registersWithTrace_cells (program : List RealArithmeticInstruction) (registers : Array SignedWord)
    (W : ℕ) (h : TraceWordBounds program registers W) :
    listCells (registersWithTrace program registers).2 ≤ program.length*2000000*(W+2)^4 := by
  induction program generalizing registers with
  | nil => simp [registersWithTrace,listCells]
  | cons instruction rest ih =>
      have hCall := (BinaryRationalOpcodeAllocation.opcodeStorage_bound instruction.op
        (read registers instruction.left) (read registers instruction.right)).trans
        (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left
          (Nat.add_le_add_right (max_le (h.1 _) (h.1 _)) 2) 4))
      have hLater := ih (execute instruction registers) h.2
      simp only [registersWithTrace,listCells_append,listCells,listCells_under,
        BinaryRationalOpcodeAllocation.applyWithAllocation_state,List.length_cons]
      change _ ≤ _
      change listCells (registersWithTrace rest (registers.push
        (BinaryRationalOpcode.apply instruction.op (read registers instruction.left) (read registers instruction.right)))).2 ≤ _ at hLater
      nlinarith

theorem registersWithTrace_slots (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    arraySlots (registersWithTrace program registers).2 ≤ program.length*(registers.size+program.length+1) := by
  induction program generalizing registers with
  | nil => simp [registersWithTrace,arraySlots]
  | cons instruction rest ih =>
      have hLater := ih (registers.push
        (BinaryRationalOpcodeAllocation.applyWithAllocation instruction.op
          (read registers instruction.left) (read registers instruction.right)).1)
      simp only [registersWithTrace,arraySlots_append,arraySlots,arraySlots_under,Array.size_push,List.length_cons] at hLater ⊢
      nlinarith

theorem registersWithTrace_frames (program : List RealArithmeticInstruction) (registers : Array SignedWord) :
    framePeak (registersWithTrace program registers).2 ≤ program.length+1 := by
  induction program generalizing registers with
  | nil => simp [registersWithTrace,framePeak]
  | cons instruction rest ih =>
      have hu := framePeak_under 1 (registersWithTrace rest (registers.push
        (BinaryRationalOpcodeAllocation.applyWithAllocation instruction.op
          (read registers instruction.left) (read registers instruction.right)).1)).2
      have hLater := ih (registers.push
        (BinaryRationalOpcodeAllocation.applyWithAllocation instruction.op
          (read registers instruction.left) (read registers instruction.right)).1)
      simp only [registersWithTrace,framePeak_append,framePeak,List.length_cons]
      omega

def pairTrace {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : Trace :=
  [.frames 8,.arrayAllocation 14] ++ under 8
    (registersWithTrace RealPairProgram.code
      (pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair).inputs).2

-- Original resource pair fields derive every intermediate register width.
theorem pairTrace_bounds {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D)
    (hL : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) :
    listCells (pairTrace choice)+arraySlots (pairTrace choice) ≤
      7*2000000*(5+2*binaryWordWidth D)^4+105 ∧ framePeak (pairTrace choice) ≤ 16 := by
  let source := pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair
  have ht := pair_trace_wordBounds hC choice.state choice.first choice.second choice.tail choice.head_pair
    D hD hL (fun j => (hBox j).2) hs
  have hl := registersWithTrace_cells RealPairProgram.code source.inputs (3+2*binaryWordWidth D) ht
  have ha := registersWithTrace_slots RealPairProgram.code source.inputs
  have hf := registersWithTrace_frames RealPairProgram.code source.inputs
  have hu := framePeak_under 8 (registersWithTrace RealPairProgram.code source.inputs).2
  have hSize : source.inputs.size = 5 := rfl
  rw [RealPairProgram.operations,hSize] at ha
  rw [RealPairProgram.operations] at hl hf
  simp only [pairTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  dsimp only [source] at hl ha hf hu
  have hW : 3+2*binaryWordWidth D+2 = 5+2*binaryWordWidth D := by omega
  rw [hW] at hl
  exact ⟨by omega,by omega⟩

def fractionalStorage {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) (j : Fin n) : ℕ :=
  BinaryRationalOpcodeAllocation.lessEqualStorage (resource.read j) BinaryRationalOpcode.zero +
    BinaryRationalOpcodeAllocation.lessEqualStorage (capacity.read j) (resource.read j)

theorem fractionalStorage_bound {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) (j : Fin n)
    (W : ℕ) (hW : 1≤W) (hc : width (capacity.read j)≤W) (hr : width (resource.read j)≤W) :
    fractionalStorage capacity resource j ≤ 5000*(W+1)^3 := by
  have hz : width BinaryRationalOpcode.zero = 1 := rfl
  have hA := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (resource.read j) BinaryRationalOpcode.zero).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hr (by rw [hz]; exact hW)) 1) 3))
  have hB := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (capacity.read j) (resource.read j)).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hc hr) 1) 3))
  unfold fractionalStorage
  omega

def selectTrace {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : Trace :=
  let first := choice.state.state.resource.read choice.first
  let second := choice.state.state.resource.read choice.second
  let total := BinaryRationalOpcode.apply .add first second
  let chosen := choice.endpoint branch
  let next := (choice.select branch).state.resource
  [.frames 8,
    .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .add first second),
    .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .sub total chosen),
    .arrayAllocation (2*(tablePayload choice.state.state.resource+tablePayload next)+16),
    .listAllocation (fractionalStorage capacity next choice.first),
    .listAllocation (fractionalStorage capacity next choice.second),.listAllocation 6]

theorem selectTrace_bound {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) (D : ℕ) (hD : 0<D)
    (hL : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) :
    listCells (selectTrace choice branch)+arraySlots (selectTrace choice branch) ≤
      4000000*(5+2*binaryWordWidth D)^4+10000*(4+2*binaryWordWidth D)^3+
        4*n*(7+4*binaryWordWidth D)+22 := by
  let W := 3+2*binaryWordWidth D
  have hW : 1≤W := by dsimp [W]; omega
  have hResource : ∀ j,width (choice.state.state.resource.read j) ≤ W := fun j =>
    (state_wordWidth choice.state D hD (fun j => (hBox j).2) hs j).trans (by dsimp [W]; omega)
  have hCapacity : ∀ j,width (capacity.read j) ≤ W := fun j =>
    (capacity_wordWidth capacity hC D hD hL hBox j).trans (by dsimp [W]; omega)
  have hChosen : width (choice.endpoint branch) ≤ W :=
    (selected_endpoint_width choice D hD hL (fun j => (hBox j).2) hs branch).trans (by dsimp [W]; omega)
  have hTotal := selected_total_width choice D hD hL (fun j => (hBox j).2) hs
  have hNext : ∀ j,width ((choice.select branch).state.resource.read j) ≤ W := fun j =>
    (state_wordWidth (choice.select branch) D hD (fun j => (hBox j).2)
      (choice_select_invariant choice D hL hs branch) j).trans (by dsimp [W]; omega)
  have hAdd := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .add
    (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)).trans
    (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hResource _) (hResource _)) 2) 4))
  have hSub := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .sub
    (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second))
    (choice.endpoint branch)).trans
    (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hTotal hChosen) 2) 4))
  have hCmpA := fractionalStorage_bound capacity (choice.select branch).state.resource choice.first W hW (hCapacity _) (hNext _)
  have hCmpB := fractionalStorage_bound capacity (choice.select branch).state.resource choice.second W hW (hCapacity _) (hNext _)
  have hOld := tablePayload_bound choice.state.state.resource W hResource
  have hNew := tablePayload_bound (choice.select branch).state.resource W hNext
  unfold selectTrace
  simp only [listCells,arraySlots]
  dsimp only [W] at hAdd hSub hCmpA hCmpB hOld hNew
  nlinarith


def paddingTrace {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : Trace :=
  let w := max choice.probability.numerator.length choice.probability.denominator.length
  [.frames (w+8),.listAllocation (2*w+8)]

theorem paddingTrace_bound {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D)
    (hL : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) :
    listCells (paddingTrace choice)+arraySlots (paddingTrace choice) ≤ 2*(3+2*binaryWordWidth D)+8 ∧
    framePeak (paddingTrace choice) ≤ 3+2*binaryWordWidth D+8 := by
  have hw := prepared_coin_buffer_width choice D hD hL (fun j => (hBox j).2) hs
  simp only [paddingTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

-- Restoring division with incoming false is exactly the coin digit/residual.
-- Its existing storage contract includes borrow frames, both buffers,
-- reversed accumulators and the high-bit drop's terminal reversal.
theorem coin_step_allocation_state {w : ℕ} (a b : FixedBinaryWord w) :
    (BinaryDivisionAllocation.stepWithAllocation false a.bits b.bits).1 = BinaryCoinWord.step a.bits b.bits := by
  rw [BinaryDivisionAllocation.stepWithAllocation_state]
  rfl

def coinTrace {w : ℕ} (a b : FixedBinaryWord w) : Trace :=
  [.frames (w+8),.listAllocation (BinaryDivisionAllocation.stepStorage false a.bits b.bits)]

theorem coinTrace_bound {w : ℕ} (a b : FixedBinaryWord w) (W : ℕ) (hw : w≤W) :
    listCells (coinTrace a b)+arraySlots (coinTrace a b) ≤ 50*(W+2)^2 ∧
    framePeak (coinTrace a b) ≤ W+8 := by
  have hs := BinaryDivisionAllocation.stepStorage_bound false a.bits b.bits (a.size.trans b.size.symm)
  rw [b.size] at hs
  have hp := hs.trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 2) 2))
  simp only [coinTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def stepBound (n D : ℕ) : ℕ :=
  7*2000000*(5+2*binaryWordWidth D)^4+105+
  (4000000*(5+2*binaryWordWidth D)^4+10000*(4+2*binaryWordWidth D)^3+
    4*n*(7+4*binaryWordWidth D)+22)+
  (2*(3+2*binaryWordWidth D)+8)+50*(5+2*binaryWordWidth D)^2+32

def potential {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N pos : ℕ) (cursor : Cursor capacity hC) : ℕ := N-pos+cursor.rank

-- Data transitions exactly match the unmeasured Boolean controller. Local
-- reservations are ghost annotations and all old reservations are retained.
def resourceWithTrace {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N) :
    (Option (Certified capacity)×ℕ)×Trace :=
  match cursor with
  | .ready state =>
      match hs : BinaryGeneralResourceChoice.prepare capacity hC state with
      | .done result => ((some result,pos),[.frames 1,.arrayAllocation 16])
      | .ask choice =>
          let later := resourceWithTrace N bits (pending choice) pos hp
          (later.1,[.frames 1,.arrayAllocation 16] ++ pairTrace choice ++ paddingTrace choice ++ under 1 later.2)
  | .coin (w:=w) choice a b hb hab =>
      let body : Trace := [.frames (w+8),.arrayAllocation 16]
      if hz : a.isZero=true then
        let later := resourceWithTrace N bits (.ready (choice.select false) : Cursor capacity hC) pos hp
        (later.1,body ++ selectTrace choice false ++ under 1 later.2)
      else if he : a.same b=true then
        let later := resourceWithTrace N bits (.ready (choice.select true) : Cursor capacity hC) pos hp
        (later.1,body ++ selectTrace choice true ++ under 1 later.2)
      else if hRead : pos<N then
        let next := a.coinStep b
        have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
        if bits ⟨pos,hRead⟩=next.1 then
          let later := resourceWithTrace N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le)
            (pos+1) (by omega)
          (later.1,body ++ coinTrace a b ++ under 1 later.2)
        else
          let later := resourceWithTrace N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC)
            (pos+1) (by omega)
          (later.1,body ++ coinTrace a b ++ selectTrace choice (!bits ⟨pos,hRead⟩) ++ under 1 later.2)
      else ((none,pos),body)
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hs
      split at hs
      · cases Preparation.ask.inj hs; rfl
      · cases hs
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega

theorem resourceWithTrace_state {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N) :
    (resourceWithTrace N bits cursor pos hp).1 = BinaryGeneralResourceRun.runIndexed N bits cursor pos hp := by
  cases cursor with
  | ready state =>
      conv_lhs => unfold resourceWithTrace
      conv_rhs => unfold BinaryGeneralResourceRun.runIndexed
      dsimp only
      cases hs : BinaryGeneralResourceChoice.prepare capacity hC state with
      | done result => rfl
      | ask choice => exact resourceWithTrace_state N bits (pending choice) pos hp
  | coin choice a b hb hab =>
      conv_lhs => unfold resourceWithTrace
      conv_rhs => unfold BinaryGeneralResourceRun.runIndexed
      dsimp only
      split
      · exact resourceWithTrace_state N bits _ pos hp
      · split
        · exact resourceWithTrace_state N bits _ pos hp
        · split
          · split
            · exact resourceWithTrace_state N bits _ (pos+1) _
            · exact resourceWithTrace_state N bits _ (pos+1) _
          · rfl
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hs
      split at hs
      · cases Preparation.ask.inj hs; rfl
      · cases hs
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega


theorem selectTrace_frames {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : framePeak (selectTrace choice branch) ≤ 8 := by
  simp [selectTrace,framePeak]

set_option maxHeartbeats 1000000 in
theorem resourceWithTrace_bounds {n : ℕ} {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) (hD : 0<D) (hL : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N)
    (hs : BinaryGeneralResourceRunWork.BoundedCursor D cursor) :
    listCells (resourceWithTrace N bits cursor pos hp).2+arraySlots (resourceWithTrace N bits cursor pos hp).2 ≤
      (potential N pos cursor+1)*stepBound n D ∧
    framePeak (resourceWithTrace N bits cursor pos hp).2 ≤ potential N pos cursor+3+2*binaryWordWidth D+20 := by
  cases cursor with
  | ready state =>
      change StateInvariant capacity D state at hs
      unfold resourceWithTrace
      dsimp only
      cases hPrep : BinaryGeneralResourceChoice.prepare capacity hC state with
      | done result =>
          simp only [listCells,arraySlots,framePeak,potential,Cursor.rank]
          have hStep : 16≤stepBound n D := by unfold stepBound; omega
          constructor
          · nlinarith only [hStep]
          · omega
      | ask choice =>
          have hState : choice.state=state := by
            unfold BinaryGeneralResourceChoice.prepare at hPrep
            split at hPrep
            · cases Preparation.ask.inj hPrep; rfl
            · cases hPrep
          have hChoice : StateInvariant capacity D choice.state := by rw [hState]; exact hs
          have hPending := BinaryGeneralResourceRunWork.pending_bounded choice D hD hL hBox hChoice
          have ih := resourceWithTrace_bounds D hD hL hBox N bits (pending choice) pos hp hPending
          have hPair := pairTrace_bounds choice D hD hL hBox hChoice
          have hPadding := paddingTrace_bound choice D hD hL hBox hChoice
          have hProgress : potential N pos (pending choice)+1 ≤ potential N pos (.ready state : Cursor capacity hC) := by
            unfold potential pending
            dsimp only [Cursor.rank]
            rw [hState]
            omega
          have hRest := ih.1.trans (Nat.mul_le_mul_right (stepBound n D) hProgress)
          have hFrames := framePeak_under 1 (resourceWithTrace N bits (pending choice) pos hp).2
          have hLocal : listCells (pairTrace choice)+arraySlots (pairTrace choice)+
              (listCells (paddingTrace choice)+arraySlots (paddingTrace choice))+16≤stepBound n D := by
            unfold stepBound
            nlinarith only [hPair.1,hPadding.1]
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under]
          constructor
          · nlinarith only [hRest,hLocal]
          · omega
  | coin choice a b hb hab =>
      rename_i w
      change StateInvariant capacity D choice.state ∧ w≤1+2*binaryWordWidth D at hs
      unfold resourceWithTrace
      dsimp only
      have hSelect (branch : Bool) := selectTrace_bound choice branch D hD hL hBox hs.1
      have hSelectFrames (branch : Bool) := selectTrace_frames choice branch
      have hSelected (branch : Bool) : BinaryGeneralResourceRunWork.BoundedCursor D
          (.ready (choice.select branch) : Cursor capacity hC) := choice_select_invariant choice D hL hs.1 branch
      have hCoin := coinTrace_bound a b (3+2*binaryWordWidth D) (by omega)
      have hSelectedProgress (branch : Bool) : potential N pos (.ready (choice.select branch) : Cursor capacity hC)+1 ≤
          potential N pos (.coin choice a b hb hab) := by
        have hr := selected_rank_lt choice a b hb hab branch
        unfold potential
        omega
      have hSelectLocal (branch : Bool) : listCells (selectTrace choice branch)+arraySlots (selectTrace choice branch)+16≤stepBound n D := by
        have h := hSelect branch
        unfold stepBound
        nlinarith only [h]
      split
      · have ih := resourceWithTrace_bounds D hD hL hBox N bits
          (.ready (choice.select false) : Cursor capacity hC) pos hp (hSelected false)
        have hr := ih.1.trans (Nat.mul_le_mul_right (stepBound n D) (hSelectedProgress false))
        have hf := framePeak_under 1 (resourceWithTrace N bits (.ready (choice.select false) : Cursor capacity hC) pos hp).2
        have hl := hSelectLocal false
        have ht := hSelectFrames false
        have hp' := hSelectedProgress false
        simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
          listCells_under,arraySlots_under]
        exact ⟨by nlinarith only [hr,hl],by omega⟩
      · split
        · have ih := resourceWithTrace_bounds D hD hL hBox N bits
            (.ready (choice.select true) : Cursor capacity hC) pos hp (hSelected true)
          have hr := ih.1.trans (Nat.mul_le_mul_right (stepBound n D) (hSelectedProgress true))
          have hf := framePeak_under 1 (resourceWithTrace N bits (.ready (choice.select true) : Cursor capacity hC) pos hp).2
          have hl := hSelectLocal true
          have ht := hSelectFrames true
          have hp' := hSelectedProgress true
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under]
          exact ⟨by nlinarith only [hr,hl],by omega⟩
        · split
          · rename_i hRead
            have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h => by
              have hSame : a.same b=true := (a.same_value b).mpr h
              contradiction)
            have hPos : pos+1≤N := by omega
            have hReadProgress : potential N (pos+1)
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le : Cursor capacity hC)+1 ≤
                potential N pos (.coin choice a b hb hab) := by unfold potential; dsimp only [Cursor.rank]; omega
            split
            · have ih := resourceWithTrace_bounds D hD hL hBox N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le : Cursor capacity hC)
                (pos+1) hPos ⟨hs.1,hs.2⟩
              have hr := ih.1.trans (Nat.mul_le_mul_right (stepBound n D) hReadProgress)
              have hf := framePeak_under 1 (resourceWithTrace N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le : Cursor capacity hC) (pos+1) hPos).2
              have hLocal : listCells (coinTrace a b)+arraySlots (coinTrace a b)+16≤stepBound n D := by
                unfold stepBound
                nlinarith only [hCoin.1]
              simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                listCells_under,arraySlots_under]
              exact ⟨by nlinarith only [hr,hLocal],by omega⟩
            · let hBranch := !bits ⟨pos,hRead⟩
              have ih := resourceWithTrace_bounds D hD hL hBox N bits
                (.ready (choice.select hBranch) : Cursor capacity hC) (pos+1) hPos (hSelected hBranch)
              have hProgress : potential N (pos+1) (.ready (choice.select hBranch) : Cursor capacity hC)+1 ≤
                  potential N pos (.coin choice a b hb hab) := by
                have ht := hSelectedProgress hBranch
                unfold potential at ht ⊢
                omega
              have hr := ih.1.trans (Nat.mul_le_mul_right (stepBound n D) hProgress)
              have hf := framePeak_under 1 (resourceWithTrace N bits
                (.ready (choice.select hBranch) : Cursor capacity hC) (pos+1) hPos).2
              have hLocal : listCells (coinTrace a b)+arraySlots (coinTrace a b)+
                  (listCells (selectTrace choice hBranch)+arraySlots (selectTrace choice hBranch))+16≤stepBound n D := by
                have ht := hSelect hBranch
                unfold stepBound
                nlinarith only [hCoin.1,ht]
              have ht := hSelectFrames hBranch
              simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                listCells_under,arraySlots_under]
              dsimp only [hBranch] at ih hr hf hProgress hLocal ht
              exact ⟨by nlinarith only [hr,hLocal],by omega⟩
          · have hStep : 16≤stepBound n D := by unfold stepBound; omega
            simp only [listCells,arraySlots,framePeak]
            exact ⟨by nlinarith,by omega⟩
termination_by (N-pos,cursor.rank)
decreasing_by
  all_goals subst cursor
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hPrep
      split at hPrep
      · cases Preparation.ask.inj hPrep; rfl
      · cases hPrep
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega


theorem listCells_reservation_ofFn (n : ℕ) (f : Fin n→ℕ) :
    listCells (List.ofFn (fun j => Event.listAllocation (f j))) = ∑ j,f j := by
  induction n with
  | zero => simp [listCells]
  | succ n ih => rw [List.ofFn_succ]; simp only [listCells,ih,Fin.sum_univ_succ]

theorem arraySlots_reservation_ofFn (n : ℕ) (f : Fin n→ℕ) :
    arraySlots (List.ofFn (fun j => Event.listAllocation (f j))) = 0 := by
  induction n with
  | zero => simp [arraySlots]
  | succ n ih => rw [List.ofFn_succ]; simp only [arraySlots,ih]

theorem framePeak_reservation_ofFn (n : ℕ) (f : Fin n→ℕ) :
    framePeak (List.ofFn (fun j => Event.listAllocation (f j))) = 0 := by
  induction n with
  | zero => simp [framePeak]
  | succ n ih => rw [List.ofFn_succ]; simp only [framePeak,ih]

def initialTrace {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) : Trace :=
  [.frames (n+4),.listAllocation (2*n),.arrayAllocation 16] ++
    List.ofFn (fun j => Event.listAllocation (fractionalStorage capacity resource j))

theorem initialTrace_bound {n : ℕ} (capacity resource : FixedArrayTable n SignedWord) (W : ℕ)
    (hW : 1≤W) (hc : ∀ j,width (capacity.read j)≤W) (hr : ∀ j,width (resource.read j)≤W) :
    listCells (initialTrace capacity resource)+arraySlots (initialTrace capacity resource) ≤
      n*5000*(W+1)^3+2*n+16 ∧ framePeak (initialTrace capacity resource)≤n+4 := by
  have hEach := fun j => fractionalStorage_bound capacity resource j W hW (hc j) (hr j)
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hEach j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  simp only [initialTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_reservation_ofFn,arraySlots_reservation_ofFn,framePeak_reservation_ofFn]
  exact ⟨by nlinarith,by omega⟩

def initialWithTrace {n : ℕ} (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (N : ℕ) (bits : Fin N→Bool) : (Option (Certified capacity)×ℕ)×Trace :=
  let later := resourceWithTrace N bits (.ready (initial capacity resource hC hR) : Cursor capacity hC) 0 (Nat.zero_le N)
  (later.1,initialTrace capacity resource ++ under 2 later.2)

theorem initialWithTrace_state {n : ℕ} (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (N : ℕ) (bits : Fin N→Bool) :
    (initialWithTrace capacity resource hC hR N bits).1 = BinaryGeneralResourceRun.initialRun capacity resource hC hR N bits := by
  unfold initialWithTrace BinaryGeneralResourceRun.initialRun BinaryGeneralResourceRun.run
  exact resourceWithTrace_state N bits _ 0 (Nat.zero_le N)

theorem initialWithTrace_bounds {n : ℕ} (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0<D) (hL : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hRL : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hResourceBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j))
    (N : ℕ) (bits : Fin N→Bool) :
    listCells (initialWithTrace capacity resource hC hR N bits).2+arraySlots (initialWithTrace capacity resource hC hR N bits).2 ≤
      n*5000*(4+2*binaryWordWidth D)^3+2*n+16+(N+2*n+2)*stepBound n D ∧
    framePeak (initialWithTrace capacity resource hC hR N bits).2 ≤ N+2*n+2*binaryWordWidth D+26 := by
  let state := initial capacity resource hC hR
  have hState := initial_invariant capacity resource hC hR D hRL hResourceBox
  have hs : BinaryGeneralResourceRunWork.BoundedCursor D (.ready state : Cursor capacity hC) := hState
  have hLater := resourceWithTrace_bounds D hD hL hBox N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N) hs
  have hCw : ∀ j,width (capacity.read j)≤3+2*binaryWordWidth D := fun j =>
    (capacity_wordWidth capacity hC D hD hL hBox j).trans (by omega)
  have hRw : ∀ j,width (resource.read j)≤3+2*binaryWordWidth D := fun j =>
    (state_wordWidth state D hD (fun j => (hBox j).2) hState j).trans (by omega)
  have hInitial := initialTrace_bound capacity resource (3+2*binaryWordWidth D) (by omega) hCw hRw
  have hActive := active_length_le state
  dsimp only [state] at hActive
  have hPotential : potential N 0 (.ready state : Cursor capacity hC)+1≤N+2*n+2 := by
    unfold potential
    simp only [Nat.sub_zero,Cursor.rank]
    dsimp only [state]
    omega
  have hRest := hLater.1.trans (Nat.mul_le_mul_right (stepBound n D) hPotential)
  have hFrames := framePeak_under 2 (resourceWithTrace N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)).2
  unfold initialWithTrace
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells_under,arraySlots_under]
  dsimp only [state] at hRest hFrames hLater
  constructor
  · nlinarith only [hRest,hInitial.1]
  · unfold potential at hLater
    simp only [Nat.sub_zero,Cursor.rank] at hLater
    omega

-- Actual accepted PRG fields instantiate the complete resource lifetime model.
def requestWithTrace {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool) :
    (Option (Certified (resourceInput request rich).length)×ℕ)×Trace :=
  initialWithTrace (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 N bits

theorem requestWithTrace_erases {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool) :
    (requestWithTrace request rich N bits).1 = (resourceWork request rich N bits).1 := by
  unfold requestWithTrace resourceWork
  rw [initialWithTrace_state,BinaryGeneralResourceRunWork.initialRun_state]

-- This is the old arithmetic allocation backend. Its space trace is not an
-- allocation certificate for a different GCD/arithmetic realization.
def sourceStepBound (n S : ℕ) : ℕ :=
  7*2000000*(5+2*(S+1))^4+105+
  (4000000*(5+2*(S+1))^4+10000*(4+2*(S+1))^3+4*n*(7+4*(S+1))+22)+
  (2*(3+2*(S+1))+8)+50*(5+2*(S+1))^2+32

def requestBound (n S N : ℕ) : ℕ := n*5000*(6+2*S)^3+2*n+16+(N+2*n+2)*sourceStepBound n S

theorem stepBound_source_le (n D S : ℕ) (h : binaryWordWidth D≤S+1) : stepBound n D ≤ sourceStepBound n S := by
  unfold stepBound sourceStepBound
  gcongr

theorem requestWithTrace_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool) :
    listCells (requestWithTrace request rich N bits).2+arraySlots (requestWithTrace request rich N bits).2 ≤
      requestBound n request.source.originalInputWordWidth N ∧
    framePeak (requestWithTrace request rich N bits).2 ≤ N+2*n+2*request.source.originalInputWordWidth+28 := by
  obtain ⟨hL,hRL,hBox,hResourceBox⟩ := resource_lattice_boxes request rich
  have h := initialWithTrace_bounds (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
    request.source.normalizedInput.latticeDenominator request.source.normalizedInput.latticeDenominator_pos
    hL hRL hBox hResourceBox N bits
  have hWidth := request.source.normalized_lattice_wordWidth_original
  have hStep := stepBound_source_le n request.source.normalizedInput.latticeDenominator request.source.originalInputWordWidth (by omega)
  have hRest := Nat.mul_le_mul_left (N+2*n+2) hStep
  have hInitial := Nat.mul_le_mul_left (n*5000) (Nat.pow_le_pow_left
    (show 4+2*binaryWordWidth request.source.normalizedInput.latticeDenominator≤6+2*request.source.originalInputWordWidth by omega) 3)
  unfold requestWithTrace requestBound
  exact ⟨by nlinarith only [h.1,hRest,hInitial],by omega⟩

theorem request_all_prefix_heap {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (borrowedSeedCells retainedInputCells steps : ℕ) :
    retainedHeap (borrowedSeedCells+retainedInputCells) (requestWithTrace request rich N bits).2 steps ≤
      borrowedSeedCells+retainedInputCells+requestBound n request.source.originalInputWordWidth N := by
  have h := (requestWithTrace_bound request rich N bits).1
  have hl := listCells_take_le (requestWithTrace request rich N bits).2 steps
  have ha := arraySlots_take_le (requestWithTrace request rich N bits).2 steps
  unfold retainedHeap
  omega

theorem request_all_prefix_controller_frames {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (steps : ℕ) : framePeak ((requestWithTrace request rich N bits).2.take steps) ≤
      N+2*n+2*request.source.originalInputWordWidth+28 :=
  (framePeak_take_le _ _).trans (requestWithTrace_bound request rich N bits).2


theorem requestWithTrace_position {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool) :
    (requestWithTrace request rich N bits).1.2 ≤ N := by
  rw [requestWithTrace_erases]
  exact resourceWork_position request rich N bits

theorem requestWithTrace_position_width {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool) :
    binaryWordWidth (requestWithTrace request rich N bits).1.2 ≤ binaryWordWidth N :=
  binaryWordWidth_mono (requestWithTrace_position request rich N bits)

theorem requestBound_mono {n m S T N M : ℕ} (hn : n≤m) (hS : S≤T) (hN : N≤M) :
    requestBound n S N ≤ requestBound m T M := by
  unfold requestBound sourceStepBound
  gcongr

def frameWidth (length : ℕ) : ℕ := 3*length+6
def frameBound (length : ℕ) : ℕ := requestBound length (frameWidth length) (8*length+3025)

theorem parsed_request_source_width (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) :
    parsed.1.2.request.source.originalInputWordWidth≤frameWidth frame.length := by
  exact BinaryPRGFrameCostJoin.read_source_width frame parsed h

theorem parsed_resource_bound (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision) :
    listCells (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2+
      arraySlots (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 ≤ frameBound frame.length ∧
    framePeak (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 ≤
      10*frame.length+2*frameWidth frame.length+3053 := by
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h
  have hS := parsed_request_source_width frame parsed h
  have hCount := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed h
  have hChoice : coinBitBudget parsed.1.1 parsed.1.2.request.precision≤8*frame.length+3025 := by
    have hC : coinBitBudget parsed.1.1 parsed.1.2.request.precision≤sampleBitBudget parsed.1.1 parsed.1.2.request.precision := by
      unfold sampleBitBudget innerBitBudget
      omega
    exact hC.trans hCount
  have hb := requestWithTrace_bound parsed.1.2.request rich
    (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read
  refine ⟨hb.1.trans (requestBound_mono hn hS hChoice),?_⟩
  omega

theorem parsed_resource_all_prefix_heap (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (originalSeedLength retainedInputCells steps : ℕ) :
    retainedHeap (originalSeedLength+retainedInputCells)
      (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps ≤
        originalSeedLength+retainedInputCells+frameBound frame.length := by
  have hb := (parsed_resource_bound frame parsed h rich tables).1
  have hl := listCells_take_le
    (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps
  have ha := arraySlots_take_le
    (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps
  unfold retainedHeap
  omega


def polynomialBound (length : ℕ) : ℕ := 2^56*(length+1)^5

set_option maxHeartbeats 1000000 in
theorem frameBound_polynomial (length : ℕ) : frameBound length≤polynomialBound length := by
  let t := length+1
  have ht : 1≤t := by dsimp [t]; omega
  have hn : length≤t := by dsimp [t]; omega
  have hS : frameWidth length+1≤7*t := by unfold frameWidth; dsimp [t]; omega
  have hN : 8*length+3025≤3025*t := by dsimp [t]; omega
  have hA : 5+2*(frameWidth length+1)≤19*t := by omega
  have hB : 4+2*(frameWidth length+1)≤18*t := by omega
  have hC : 7+4*(frameWidth length+1)≤35*t := by omega
  have hE : 3+2*(frameWidth length+1)≤17*t := by omega
  have hInitial : 6+2*frameWidth length≤18*t := by omega
  have hController : 8*length+3025+2*length+2≤3029*t := by omega
  have hStep : sourceStepBound length (frameWidth length) ≤
      18000000*(19*t)^4+10000*(18*t)^3+4*t*(35*t)+2*(17*t)+50*(19*t)^2+167 := by
    unfold sourceStepBound
    have h4 := Nat.pow_le_pow_left hA 4
    have h3 := Nat.pow_le_pow_left hB 3
    have h2 := Nat.pow_le_pow_left hA 2
    have hProduct := Nat.mul_le_mul hn hC
    nlinarith only [h4,h3,h2,hProduct,hE]
  have hTop : frameBound length ≤
      t*5000*(18*t)^3+2*t+16+
      3029*t*(18000000*(19*t)^4+10000*(18*t)^3+4*t*(35*t)+2*(17*t)+50*(19*t)^2+167) := by
    unfold frameBound requestBound
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul (Nat.mul_le_mul_right 5000 hn) (Nat.pow_le_pow_left hInitial 3))
        (Nat.mul_le_mul_left 2 hn)) le_rfl)
      (Nat.mul_le_mul hController hStep)
  have h0 : 1≤t^5 := Nat.one_le_pow 5 t ht
  have h1 : t≤t^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<t) (by decide : 1≤5)
  have h2 : t^2≤t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : t^3≤t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : t^4≤t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold polynomialBound
  change frameBound length≤2^56*t^5
  norm_num only [Nat.reducePow] at ⊢
  ring_nf at hTop
  nlinarith only [hTop,h0,h1,h2,h3,h4]

theorem parsed_resource_all_prefix_polynomial (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (originalSeedLength retainedInputCells steps : ℕ) :
    retainedHeap (originalSeedLength+retainedInputCells)
      (requestWithTrace parsed.1.2.request rich (coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).2 steps ≤
        originalSeedLength+retainedInputCells+2^56*(frame.length+1)^5 :=
  (parsed_resource_all_prefix_heap frame parsed h rich tables originalSeedLength retainedInputCells steps).trans
    (Nat.add_le_add_left (frameBound_polynomial frame.length) _)

end Blotto.BinaryPRGResourceLifetime

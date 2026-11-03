import Blotto.BinaryCompleteTraceHeaders

/-! All complete returned traces have representation-weighted every-prefix
bounds, including zero-slot array headers. Prices remain the explicit source
representation parameters of BinarySeedPreparationSpace. This does not supply
native scalar/reference/record/allocator implementations or a GC certificate. -/
namespace Blotto.BinaryCompleteRepresentationSpace
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1500000

def units (prices : Representation) : ℕ :=
  prices.listCellUnits+prices.arraySlotUnits+prices.arrayHeaderUnits+prices.frameUnits

theorem zero_array_header (prices : Representation) :
    representedWorkspace prices [.arrayAllocation 0] 1 = prices.arrayHeaderUnits := by
  simp [representedWorkspace,listCells,arraySlots,arrayRecords,framePeak]

theorem represented_prefix (prices : Representation) (trace : Trace) (steps : ℕ) :
    representedWorkspace prices trace steps ≤ units prices*(usage trace+arrayRecords trace) := by
  have hl := listCells_take_le trace steps
  have ha := arraySlots_take_le trace steps
  have hh := arrayRecords_take_le trace steps
  have hf := framePeak_take_le trace steps
  have huL : prices.listCellUnits ≤ units prices := by unfold units; omega
  have huA : prices.arraySlotUnits ≤ units prices := by unfold units; omega
  have huH : prices.arrayHeaderUnits ≤ units prices := by unfold units; omega
  have huF : prices.frameUnits ≤ units prices := by unfold units; omega
  calc
    representedWorkspace prices trace steps ≤
        units prices*listCells (trace.take steps)+units prices*arraySlots (trace.take steps)+
          units prices*arrayRecords (trace.take steps)+units prices*framePeak (trace.take steps) := by
      unfold representedWorkspace
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_right _ huL) (Nat.mul_le_mul_right _ huA))
        (Nat.mul_le_mul_right _ huH)) (Nat.mul_le_mul_right _ huF)
    _ = units prices*(listCells (trace.take steps)+arraySlots (trace.take steps)+
        arrayRecords (trace.take steps)+framePeak (trace.take steps)) := by ring
    _ ≤ units prices*(usage trace+arrayRecords trace) := by
      apply Nat.mul_le_mul_left
      unfold usage BinaryPRGHeapPrimitiveLifetime.cells
      omega

theorem represented_le (prices : Representation) (trace : Trace) (B steps : ℕ)
    (h : usage trace+arrayRecords trace ≤ B) :
    representedWorkspace prices trace steps ≤ units prices*B :=
  (represented_prefix prices trace steps).trans (Nat.mul_le_mul_left _ h)

theorem represented_address (prices : Representation) (trace : Trace) (B borrowed steps address : ℕ)
    (h : usage trace+arrayRecords trace ≤ B)
    (hAddress : address < borrowed+representedWorkspace prices trace steps) :
    address < 2^binaryWordWidth (borrowed+units prices*B) := by
  exact (hAddress.trans_le (Nat.add_le_add_left (represented_le prices trace B steps h) borrowed)).trans
    (lt_pow_binaryWordWidth _)

attribute [local irreducible] BinaryPRGHeapTraceUsage.usage BinarySamplerExecutionCharges.total
  BinaryGenerationExecutionCharges.total BinaryBigEndian.littleValue
attribute [local irreducible] BinaryPromiseOpcodeRequest.rawWithFactoryExtras BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras BinaryPromiseOpcodeRequest.generatedWithFactoryExtras BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras BinaryPromiseOpcodeRequest.pairWithFactoryExtras BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras

theorem raw_headers : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    usage (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.raw_complete_joint
  refine ⟨C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have hl := BinaryCompleteTraceHeaders.raw_length rich frame bits
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem raw_represented : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) (frame bits : List Bool) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := raw_headers
  exact ⟨C,d,fun prices rich frame bits steps => represented_le prices _ _ steps (h rich frame bits)⟩

theorem raw_address : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) (frame bits : List Bool) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.rawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := raw_headers
  exact ⟨C,d,fun prices rich frame bits borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h rich frame bits) hAddress⟩

theorem parsedRaw_headers : ∃ C d : ℕ,∀ (rich : Bool) (frame bits : List Bool),
    usage (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.parsedRaw_complete_joint
  refine ⟨C,d,?_⟩
  intro rich frame bits
  have ho := hOld rich frame bits
  have hl := BinaryCompleteTraceHeaders.parsedRaw_length rich frame bits
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem parsedRaw_represented : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) (frame bits : List Bool) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedRaw_headers
  exact ⟨C,d,fun prices rich frame bits steps => represented_le prices _ _ steps (h rich frame bits)⟩

theorem parsedRaw_address : ∃ C d : ℕ,∀ (prices : Representation) (rich : Bool) (frame bits : List Bool) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedRawWithFactoryExtras rich frame bits).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := parsedRaw_headers
  exact ⟨C,d,fun prices rich frame bits borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h rich frame bits) hAddress⟩

theorem generated_headers : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S),
    usage (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.generated_complete_joint
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have hl := BinaryCompleteTraceHeaders.generated_length next rich frame state
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem generated_represented : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := generated_headers
  exact ⟨C,d,fun prices S next rich frame state steps => represented_le prices _ _ steps (h next rich frame state)⟩

theorem generated_address : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := generated_headers
  exact ⟨C,d,fun prices S next rich frame state borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h next rich frame state) hAddress⟩

theorem parsedGenerated_headers : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S),
    usage (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.parsedGenerated_complete_joint
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have hl := BinaryCompleteTraceHeaders.parsedGenerated_length next rich frame state
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem parsedGenerated_represented : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_headers
  exact ⟨C,d,fun prices S next rich frame state steps => represented_le prices _ _ steps (h next rich frame state)⟩

theorem parsedGenerated_address : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras next rich frame state).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := parsedGenerated_headers
  exact ⟨C,d,fun prices S next rich frame state borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h next rich frame state) hAddress⟩

theorem pair_headers : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    usage (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.pair_complete_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have hl := BinaryCompleteTraceHeaders.pair_length next frame state
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem pair_represented : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := pair_headers
  exact ⟨C,d,fun prices S next frame state steps => represented_le prices _ _ steps (h next frame state)⟩

theorem pair_address : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.pairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := pair_headers
  exact ⟨C,d,fun prices S next frame state borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h next frame state) hAddress⟩

theorem parsedPair_headers : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    usage (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2+arrayRecords (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryReturnedFactoryExtras.parsedPair_complete_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have hl := BinaryCompleteTraceHeaders.parsedPair_length next frame state
  have hh := BinaryCompleteTraceHeaders.arrayRecords_le_length (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2
  dsimp only at ho hl ⊢
  omega

theorem parsedPair_represented : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (steps : ℕ),
    representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 steps ≤ units prices*(C*(frame.length+1)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_headers
  exact ⟨C,d,fun prices S next frame state steps => represented_le prices _ _ steps (h next frame state)⟩

theorem parsedPair_address : ∃ C d : ℕ,∀ (prices : Representation) {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (borrowed steps address : ℕ),
    address < borrowed+representedWorkspace prices (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras next frame state).1.1.1.1.1.1.1.1.2 steps →
      address < 2^binaryWordWidth (borrowed+units prices*(C*(frame.length+1)^d)) := by
  obtain ⟨C,d,h⟩ := parsedPair_headers
  exact ⟨C,d,fun prices S next frame state borrowed steps address hAddress =>
    represented_address prices _ _ borrowed steps address (h next frame state) hAddress⟩

end Blotto.BinaryCompleteRepresentationSpace

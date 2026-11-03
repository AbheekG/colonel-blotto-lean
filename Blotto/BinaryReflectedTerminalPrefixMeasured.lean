import Blotto.BinaryReflectedResourceMeasured
import Blotto.BinaryReflectedTerminalInputMeasured
import Blotto.BinaryReflectedTerminalPrefixLifetime

/-! Returned measured setup/resource data feed the measured reached terminal
input at the returned absolute cursor. Resource exhaustion is preserved. The
current resource source charge joins new preparation/focus/input charges;
nested factories and native model costs remain separate. -/
namespace Blotto.BinaryReflectedTerminalPrefixMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 700000

abbrev Terminal := BinaryNestedParameters.Input × Equiv.Perm (Fin 3)
abbrev Reached (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) :=
  ((BinaryReflectedPreparationLifetime.Prepared input ×
    BinaryPRGWordControllerThreeResource.Result store (BinaryReflectedFourSetup.prepare input).capacity) × Trace) × ℕ
abbrev Result (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) :=
  (((BinaryReflectedPreparationLifetime.Prepared input × Option Terminal) × FixedBinaryWord store.width) × Trace) × ℕ

def after (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (reached : Reached store input) : Result store input :=
  match reached.1.1.2.1 with
  | none => ((((reached.1.1.1,none),reached.1.1.2.2),wrap 24 2 [reached.1.2]),reached.2+4)
  | some result =>
      let terminal := BinaryReflectedTerminalInputMeasured.terminal reached.1.1.1 result.state
      ((((reached.1.1.1,some terminal.1.1),reached.1.1.2.2),wrap 24 2 [reached.1.2,terminal.1.2]),reached.2+terminal.2+8)

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store input :=
  let reached := BinaryReflectedResourceMeasured.run store input hC pc hp
  after store input reached

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).1.1 = (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1 := by
  simp only [run,after,BinaryReflectedTerminalPrefixLifetime.runWithTrace,
    BinaryReflectedResourceMeasured.run_data,BinaryReflectedTerminalInputMeasured.terminal_erases]
  cases (BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp).1.2.1 <;> rfl

theorem run_view (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((run store input hC pc hp).1.1.1.2,(run store input hC pc hp).1.1.2) =
      ((BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1.map (fun result =>
        (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
          BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state)),
        (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2) := by
  rw [run_data]
  exact BinaryReflectedTerminalPrefixLifetime.runWithTrace_erasure store input hC pc hp

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC pc hp).1.1.2.value ∧ (run store input hC pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryReflectedTerminalPrefixLifetime.runWithTrace_position store input hC pc hp

def widthEnvelope (s : ℕ) : ℕ := 2*expressionHeightBudget s 21+1

def workEnvelope (s i cap : ℕ) : ℕ := BinaryReflectedResourceMeasured.workEnvelope s i cap+
  BinaryReflectedTerminalInputMeasured.terminalPrice (widthEnvelope s)+8

def envelope (s i cap : ℕ) : ℕ := BinaryReflectedResourceMeasured.envelope s i cap+
  BinaryReflectedTerminalInputLifetime.terminalEnvelope (widthEnvelope s)+40

theorem after_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hOld : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (R H : ℕ) (hReached : reached.2 ≤ R ∧ usage reached.1.2 ≤ H) :
    (after store input reached).2 ≤ R+BinaryReflectedTerminalInputMeasured.terminalPrice (widthEnvelope s)+8 ∧
      usage (after store input reached).1.2 ≤ H+BinaryReflectedTerminalInputLifetime.terminalEnvelope (widthEnvelope s)+40 := by
  unfold after
  split
  · have hw := wrap_usage 24 2 [reached.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change reached.2+4 ≤ _ ∧ usage (wrap 24 2 [reached.1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · rename_i result hSome
    have hOldSome : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result := by
      rw [← hOld]; exact hSome
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hOldSome
    let terminal := BinaryReflectedTerminalInputMeasured.terminal reached.1.1.1 result.state
    have hTerminal := BinaryReflectedTerminalInputMeasured.reached_bounds input source hC hR hCase s hs hH
      (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess reached.1.1.1
    change terminal.2 ≤ BinaryReflectedTerminalInputMeasured.terminalPrice (widthEnvelope s) ∧
      usage terminal.1.2 ≤ BinaryReflectedTerminalInputLifetime.terminalEnvelope (widthEnvelope s) at hTerminal
    have hw := wrap_usage 24 2 [reached.1.2,terminal.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change reached.2+terminal.2+8 ≤ _ ∧ usage (wrap 24 2 [reached.1.2,terminal.1.2]) ≤ _
    exact ⟨by omega,by omega⟩

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).2 ≤ workEnvelope s store.width store.cap.value ∧
      usage (run store input hC pc hp).1.2 ≤ envelope s store.width store.cap.value := by
  have hPrefix := BinaryReflectedResourceMeasured.run_bounds store input source hC hR hCase s hs hH pc hp
  unfold run workEnvelope envelope
  exact after_bounds store input source hC hR hCase s hs hH pc hp _
    (BinaryReflectedResourceMeasured.run_resource store input hC pc hp) _ _ hPrefix

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC pc hp).1.2 steps ≤ borrowed+envelope s store.width store.cap.value ∧
      framePeak ((run store input hC pc hp).1.2.take steps) ≤ envelope s store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase s hs hH pc hp).2 borrowed steps

end Blotto.BinaryReflectedTerminalPrefixMeasured

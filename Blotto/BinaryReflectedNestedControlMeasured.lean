import Blotto.BinaryNestedControlMeasured
import Blotto.BinaryReflectedTerminalPrefixMeasured
import Blotto.BinaryReflectedRegimePrefixLifetime

/-! The actual measured reflected terminal feeds complete measured nested
boundary/control execution. Original fields derive the joined source bounds;
selected interior factories and the complete reflected draw remain separate. -/
namespace Blotto.BinaryReflectedNestedControlMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 900000

abbrev Terminal := BinaryReflectedTerminalPrefixLifetime.Terminal
abbrev Prior := BinaryReflectedTerminalPrefixMeasured.Result
abbrev Result (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) :=
  (((BinaryReflectedPreparationLifetime.Prepared input × Option (Terminal × BinaryNestedControlMeasured.Result)) ×
    FixedBinaryWord store.width) × Trace) × ℕ

def after (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (prior : Prior store input) : Result store input :=
  match prior.1.1.1.2 with
  | none => ((((prior.1.1.1.1,none),prior.1.1.2),wrap 24 2 [prior.1.2]),prior.2+4)
  | some terminal =>
      let controlled := BinaryNestedControlMeasured.run terminal.1
      ((((prior.1.1.1.1,some (terminal,controlled.1.1)),prior.1.1.2),wrap 24 2 [prior.1.2,controlled.1.2]),prior.2+controlled.2+8)

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store input :=
  after store input (BinaryReflectedTerminalPrefixMeasured.run store input hC pc hp)

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).1.1 = (BinaryReflectedRegimePrefixLifetime.runWithTrace store input hC pc hp).1 := by
  simp only [run,after,BinaryReflectedRegimePrefixLifetime.runWithTrace,BinaryReflectedTerminalPrefixMeasured.run_data,
    BinaryNestedControlMeasured.run_data]
  cases (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1.1.2 <;> rfl

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC pc hp).1.1.2.value ∧ (run store input hC pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryReflectedRegimePrefixLifetime.runWithTrace_position store input hC pc hp

def workEnvelope (s i cap : ℕ) : ℕ := BinaryReflectedTerminalPrefixMeasured.workEnvelope s i cap+
  BinaryNestedControlMeasured.workEnvelope (expressionHeightBudget s 23)+8

def envelope (s i cap : ℕ) : ℕ := BinaryReflectedTerminalPrefixMeasured.envelope s i cap+
  BinaryNestedControlMeasured.envelope (expressionHeightBudget s 23)+40

theorem after_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (prior : Prior store input)
    (hData : prior.1.1 = (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1)
    (C U : ℕ) (hPrior : prior.2 ≤ C ∧ usage prior.1.2 ≤ U) :
    (after store input prior).2 ≤ C+BinaryNestedControlMeasured.workEnvelope (expressionHeightBudget s 23)+8 ∧
      usage (after store input prior).1.2 ≤ U+BinaryNestedControlMeasured.envelope (expressionHeightBudget s 23)+40 := by
  unfold after
  split
  · have hw := wrap_usage 24 2 [prior.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+4 ≤ _ ∧ usage (wrap 24 2 [prior.1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · rename_i terminal hSome
    have hOldSome : (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1.1.2 = some terminal := by
      rw [← hData]; exact hSome
    have hContract := BinaryReflectedBoundaryPrefixLifetime.reached_terminal_contract store input source hC hR hCase s hs hH pc hp terminal hOldSome
    have hs' : 3 ≤ expressionHeightBudget s 23 := by unfold expressionHeightBudget; omega
    have hControl := BinaryNestedControlMeasured.run_bounds terminal.1 hContract.1 _ hs' hContract.2
    have hw := wrap_usage 24 2 [prior.1.2,(BinaryNestedControlMeasured.run terminal.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+(BinaryNestedControlMeasured.run terminal.1).2+8 ≤ _ ∧ usage (wrap 24 2 [prior.1.2,_]) ≤ _
    exact ⟨by omega,by omega⟩

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).2 ≤ workEnvelope s store.width store.cap.value ∧
      usage (run store input hC pc hp).1.2 ≤ envelope s store.width store.cap.value := by
  have hPrior := BinaryReflectedTerminalPrefixMeasured.run_bounds store input source hC hR hCase s hs hH pc hp
  unfold run workEnvelope envelope
  exact after_bounds store input source hC hR hCase s hs hH pc hp _
    (BinaryReflectedTerminalPrefixMeasured.run_data store input hC pc hp) _ _ hPrior

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC pc hp).1.2 steps ≤ borrowed+envelope s store.width store.cap.value ∧
      framePeak ((run store input hC pc hp).1.2.take steps) ≤ envelope s store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase s hs hH pc hp).2 borrowed steps

end Blotto.BinaryReflectedNestedControlMeasured

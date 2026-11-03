import Blotto.BinaryNestedBoundaryMeasured
import Blotto.BinaryNestedRegimeMeasured
import Blotto.BinaryNestedProfileLifetime

/-! Boundary factories or one actual measured sorted input, shared parameter
table and reached regime. Original nested fields bound the full control prefix.
The selected interior profile factories remain separate continuations. -/
namespace Blotto.BinaryNestedControlMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev Input := BinaryNestedParameters.Input
abbrev Classified := BinaryNestedClassifyLifetime.Result
abbrev Prepared := BinaryNestedSelectedRegimePrefixLifetime.Prepared
abbrev Result := BinaryNestedSelectedRegimePrefixLifetime.Result

set_option cleanup.letToHave false in
def classifyWithExtras (input : Input) : ((Classified × Trace) × ℕ) × ℕ :=
  let boundary := BinaryNestedBoundaryMeasured.boundaryWithExtras input
  match boundary.1.1.1 with
  | some table => (((Sum.inl table,wrap 24 2 [boundary.1.1.2]),boundary.1.2+4),boundary.2)
  | none =>
      let ordered := BinaryNestedOrderMeasured.orderWithExtras input
      (((Sum.inr ordered.1.1.1,wrap 24 2 [boundary.1.1.2,ordered.1.1.2]),boundary.1.2+ordered.1.2+8),boundary.2+ordered.2)

def classify (input : Input) : (Classified × Trace) × ℕ :=
  (classifyWithExtras input).1

theorem classifyWithExtras_compat (input : Input) :
    (classifyWithExtras input).1 = classify input := rfl

theorem classify_record (input : Input) :
    classify input =
  let boundary := BinaryNestedBoundaryMeasured.boundary input
  match boundary.1.1 with
  | some table => ((Sum.inl table,wrap 24 2 [boundary.1.2]),boundary.2+4)
  | none =>
      let ordered := BinaryNestedOrderMeasured.order input
      ((Sum.inr ordered.1.1,wrap 24 2 [boundary.1.2,ordered.1.2]),boundary.2+ordered.2+8) := by
  simp only [classify,classifyWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedBoundaryMeasured.childWithExtras_compat,BinaryNestedBoundaryMeasured.boundaryWithExtras_compat]
  cases h : (BinaryNestedBoundaryMeasured.boundary input).1.1 <;> simp only [h]

theorem classify_data (input : Input) : (classify input).1.1 = (BinaryNestedClassifyLifetime.classifyWithTrace input).1 := by
  simp only [classify_record,BinaryNestedClassifyLifetime.classifyWithTrace,BinaryNestedBoundaryMeasured.boundary_data,
    BinaryNestedOrderMeasured.order_erases]
  cases (BinaryNestedBoundaryLifetime.boundaryWithTrace input).1 <;> rfl

set_option cleanup.letToHave false in
def interiorWithExtras (input : Input) : ((BinaryNestedInteriorPrefixLifetime.Result × Trace) × ℕ) × ℕ :=
  let classified := classifyWithExtras input
  match classified.1.1.1 with
  | Sum.inl table => (((Sum.inl table,wrap 24 2 [classified.1.1.2]),classified.1.2+4),classified.2)
  | Sum.inr ordered =>
      let parameters := BinaryNestedParameterMeasured.prepareWithExtras ordered.1
      (((Sum.inr (ordered,parameters.1.1.1),wrap 24 2 [classified.1.1.2,parameters.1.1.2]),classified.1.2+parameters.1.2+8),classified.2+parameters.2)

def interior (input : Input) : (BinaryNestedInteriorPrefixLifetime.Result × Trace) × ℕ :=
  (interiorWithExtras input).1

theorem interiorWithExtras_compat (input : Input) :
    (interiorWithExtras input).1 = interior input := rfl

theorem interior_record (input : Input) :
    interior input =
  let classified := classify input
  match classified.1.1 with
  | Sum.inl table => ((Sum.inl table,wrap 24 2 [classified.1.2]),classified.2+4)
  | Sum.inr ordered =>
      let parameters := BinaryNestedParameterMeasured.prepare ordered.1
      ((Sum.inr (ordered,parameters.1.1),wrap 24 2 [classified.1.2,parameters.1.2]),classified.2+parameters.2+8) := by
  simp only [interior,interiorWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedBoundaryMeasured.childWithExtras_compat,BinaryNestedBoundaryMeasured.boundaryWithExtras_compat,classifyWithExtras_compat]
  cases h : (classify input).1.1 <;> simp only [h]

theorem interior_data (input : Input) : (interior input).1.1 = (BinaryNestedInteriorPrefixLifetime.runWithTrace input).1 := by
  simp only [interior_record,BinaryNestedInteriorPrefixLifetime.runWithTrace,classify_data,BinaryNestedParameterMeasured.prepare_data]
  cases (BinaryNestedClassifyLifetime.classifyWithTrace input).1 <;> rfl

set_option cleanup.letToHave false in
def runWithExtras (input : Input) : ((Result × Trace) × ℕ) × ℕ :=
  let prior := interiorWithExtras input
  match prior.1.1.1 with
  | Sum.inl table => (((Sum.inl table,wrap 24 2 [prior.1.1.2]),prior.1.2+4),prior.2)
  | Sum.inr prepared =>
      let selected := BinaryNestedRegimeMeasured.select prepared.1.1 prepared.2
      (((Sum.inr (prepared,selected.1.1),wrap 24 2 [prior.1.1.2,selected.1.2]),prior.1.2+selected.2+8),prior.2)

def run (input : Input) : (Result × Trace) × ℕ :=
  (runWithExtras input).1

theorem runWithExtras_compat (input : Input) :
    (runWithExtras input).1 = run input := rfl

theorem run_record (input : Input) :
    run input =
  let prior := interior input
  match prior.1.1 with
  | Sum.inl table => ((Sum.inl table,wrap 24 2 [prior.1.2]),prior.2+4)
  | Sum.inr prepared =>
      let selected := BinaryNestedRegimeMeasured.select prepared.1.1 prepared.2
      ((Sum.inr (prepared,selected.1.1),wrap 24 2 [prior.1.2,selected.1.2]),prior.2+selected.2+8) := by
  simp only [run,runWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedBoundaryMeasured.childWithExtras_compat,BinaryNestedBoundaryMeasured.boundaryWithExtras_compat,classifyWithExtras_compat,interiorWithExtras_compat]
  cases h : (interior input).1.1 <;> simp only [h]

theorem run_data (input : Input) : (run input).1.1 = (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 := by
  simp only [run_record,BinaryNestedSelectedRegimePrefixLifetime.runWithTrace,interior_data,BinaryNestedRegimeMeasured.select_erases]
  cases (BinaryNestedInteriorPrefixLifetime.runWithTrace input).1 <;> rfl

theorem selected_contract (input : Input) (hC : input.Canonical)
    (selected : BinaryNestedProfileLifetime.Selected) (hSelected : (run input).1.1 = Sum.inr selected) :
    selected.1.1.1 = BinaryNestedTerminalInput.sortedInput input ∧
      selected.1.1.2 = BinaryNestedTerminalInput.ordered input ∧
      selected.1.2 = BinaryNestedProfileCompiler.parameters selected.1.1.1 ∧
      selected.2 = BinaryNestedRegimeLifetime.oldSelect selected.1.1.1 selected.1.2 := by
  apply BinaryNestedProfileLifetime.selected_contract input hC selected
  rw [← run_data]
  exact hSelected

def classifyPrice (s : ℕ) : ℕ := BinaryNestedBoundaryMeasured.workEnvelope s+BinaryNestedOrderMeasured.workEnvelope s+8

def classifyEnvelope (s : ℕ) : ℕ := BinaryNestedBoundaryMeasured.envelope s+BinaryNestedOrderLifetime.orderEnvelope s+64

def interiorPrice (s : ℕ) : ℕ := classifyPrice s+BinaryNestedParameterMeasured.workEnvelope 9 s+8

def interiorEnvelope (s : ℕ) : ℕ := classifyEnvelope s+BinaryNestedParameterMeasured.envelope 9 s 128 10+64

def workEnvelope (s : ℕ) : ℕ := interiorPrice s+BinaryNestedRegimeMeasured.workEnvelope (BinaryNestedRegimeMeasured.widthEnvelope s)+8

def envelope (s : ℕ) : ℕ := interiorEnvelope s+BinaryNestedRegimeLifetime.envelope (BinaryNestedRegimeMeasured.widthEnvelope s)+64

theorem classify_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (classify input).2 ≤ classifyPrice s ∧ usage (classify input).1.2 ≤ classifyEnvelope s := by
  let boundary := BinaryNestedBoundaryMeasured.boundary input
  have hBoundary := BinaryNestedBoundaryMeasured.boundary_bounds input hC s hs hH
  change boundary.2 ≤ _ ∧ usage boundary.1.2 ≤ _ at hBoundary
  simp only [classify_record]

  split
  · have hw := wrap_usage 24 2 [boundary.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change boundary.2+4 ≤ _ ∧ usage (wrap 24 2 [boundary.1.2]) ≤ _
    unfold classifyPrice classifyEnvelope
    exact ⟨by omega,by omega⟩
  · have hOrder := BinaryNestedOrderMeasured.order_bounds input hC s hH
    have hw := wrap_usage 24 2 [boundary.1.2,(BinaryNestedOrderMeasured.order input).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change boundary.2+(BinaryNestedOrderMeasured.order input).2+8 ≤ _ ∧ usage (wrap 24 2 [boundary.1.2,_]) ≤ _
    unfold classifyPrice classifyEnvelope
    exact ⟨by omega,by omega⟩

theorem interior_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (interior input).2 ≤ interiorPrice s ∧ usage (interior input).1.2 ≤ interiorEnvelope s := by
  let classified := classify input
  have hClassified := classify_bounds input hC s hs hH
  change classified.2 ≤ _ ∧ usage classified.1.2 ≤ _ at hClassified
  simp only [interior_record]

  split
  · have hw := wrap_usage 24 2 [classified.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change classified.2+4 ≤ _ ∧ usage (wrap 24 2 [classified.1.2]) ≤ _
    unfold interiorPrice interiorEnvelope
    exact ⟨by omega,by omega⟩
  · rename_i ordered hInterior
    have hOld : (BinaryNestedClassifyLifetime.classifyWithTrace input).1 = Sum.inr ordered := by
      rw [← classify_data]; exact hInterior
    have hSorted := BinaryNestedInteriorPrefixLifetime.classified_interior_sorted input hC ordered hOld
    have hOrderedC : ordered.1.Canonical := by rw [hSorted]; exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hOrderedH : BinaryNestedParameterWork.InputHeight ordered.1 s := by
      rw [hSorted]; exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hParams := BinaryNestedParameterMeasured.prepare_bounds ordered.1 hOrderedC s hs hOrderedH
    have hw := wrap_usage 24 2 [classified.1.2,(BinaryNestedParameterMeasured.prepare ordered.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change classified.2+(BinaryNestedParameterMeasured.prepare ordered.1).2+8 ≤ _ ∧ usage (wrap 24 2 [classified.1.2,_]) ≤ _
    unfold interiorPrice interiorEnvelope
    exact ⟨by omega,by omega⟩

theorem run_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (run input).2 ≤ workEnvelope s ∧ usage (run input).1.2 ≤ envelope s := by
  let prior := interior input
  have hPrior := interior_bounds input hC s hs hH
  change prior.2 ≤ _ ∧ usage prior.1.2 ≤ _ at hPrior
  simp only [run_record]

  split
  · have hw := wrap_usage 24 2 [prior.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+4 ≤ _ ∧ usage (wrap 24 2 [prior.1.2]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩
  · rename_i prepared hInterior
    have hOld : (BinaryNestedInteriorPrefixLifetime.runWithTrace input).1 = Sum.inr prepared := by
      rw [← interior_data]; exact hInterior
    have hContract := BinaryNestedSelectedRegimePrefixLifetime.interior_contract input hC prepared hOld
    have hPreparedC : prepared.1.1.Canonical := by rw [hContract.1]; exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hPreparedH : BinaryNestedParameterWork.InputHeight prepared.1.1 s := by
      rw [hContract.1]; exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hSelected := BinaryNestedRegimeMeasured.prepared_bounds prepared.1.1 prepared.2 hPreparedC hContract.2 s hs hPreparedH
    have hw := wrap_usage 24 2 [prior.1.2,(BinaryNestedRegimeMeasured.select prepared.1.1 prepared.2).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+(BinaryNestedRegimeMeasured.select prepared.1.1 prepared.2).2+8 ≤ _ ∧ usage (wrap 24 2 [prior.1.2,_]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (run input).1.2 steps ≤ borrowed+envelope s ∧ framePeak ((run input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds input hC s hs hH).2 borrowed steps

end Blotto.BinaryNestedControlMeasured

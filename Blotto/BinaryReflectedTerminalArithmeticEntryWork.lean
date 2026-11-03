import Blotto.BinaryNestedProfileArithmeticEntryWork
import Blotto.BinaryReflectedDrawMeasured

/-! Terminal focus, reached nested factory, categorical selection, physical
point and reflected output supply the complete post-resource entry class.
All source values/cursors and conditional branches are the actual returned ones. -/
namespace Blotto.BinaryReflectedTerminalArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound quadratic_bound comparison_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def fractional (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) : ℕ :=
  BinaryArithmeticEntryWork.comparison (resource.read j) BinaryRationalOpcode.zero+
    BinaryArithmeticEntryWork.comparison (capacity.read j) (resource.read j)

theorem fractional_bound (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) :
    fractional capacity resource j ≤ 2*listCells (BinaryReflectedFocusMeasured.fractional capacity resource j).1.2 := by
  have hp := comparison_bound (resource.read j) BinaryRationalOpcode.zero
  have hb := comparison_bound (capacity.read j) (resource.read j)
  simp only [fractional,BinaryReflectedFocusMeasured.fractional,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def focus (capacity resource : FixedArrayTable 3 SignedWord) : ℕ := fractional capacity resource 0+
  if (BinaryReflectedFocusMeasured.fractional capacity resource 0).1.1 then 0 else fractional capacity resource 1

theorem focus_bound (capacity resource : FixedArrayTable 3 SignedWord) :
    focus capacity resource ≤ 2*listCells (BinaryReflectedFocusMeasured.focus capacity resource).1.2 := by
  have h0 := fractional_bound capacity resource 0
  have h1 := fractional_bound capacity resource 1
  simp only [focus,BinaryReflectedFocusMeasured.focus]
  split_ifs <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def terminal {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : ℕ :=
  let selected := BinaryReflectedFocusMeasured.preparedFocus cached state
  focus cached.capacity state.resource+
    BinaryArithmeticEntryWork.raw .div (state.resource.read selected.1.1) (cached.capacity.read selected.1.1)

theorem terminal_bound {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    terminal cached state ≤ 2*listCells (BinaryReflectedTerminalInputMeasured.terminal cached state).1.2 := by
  have hf := focus_bound cached.capacity state.resource
  have hd := quadratic_bound .div (state.resource.read (BinaryReflectedFocusMeasured.preparedFocus cached state).1.1)
    (cached.capacity.read (BinaryReflectedFocusMeasured.preparedFocus cached state).1.1)
  change focus cached.capacity state.resource ≤ 2*listCells (BinaryReflectedFocusMeasured.preparedFocus cached state).1.2 at hf
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,terminal,BinaryReflectedTerminalInputMeasured.terminal_record,BinaryReflectedTerminalInputMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def table {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity) (K : ℕ) (outer : BinaryScalarTape K) : ℕ :=
  terminal cached result.state+BinaryNestedProfileArithmeticEntryWork.profile
    (BinaryReflectedTerminalInputMeasured.terminal cached result.state).1.1.1 K outer

theorem table_bound {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity) (K : ℕ) (outer : BinaryScalarTape K) :
    table cached result K outer ≤ 2*listCells (BinaryReflectedTerminalFactoryMeasured.table cached result K outer).1.2 := by
  have ht := terminal_bound cached result.state
  have hn := BinaryNestedProfileArithmeticEntryWork.profile_bound (BinaryReflectedTerminalInputMeasured.terminal cached result.state).1.1.1 K outer
  simp only [table,BinaryReflectedTerminalFactoryMeasured.table_record,BinaryReflectedTerminalFactoryMeasured.fromTerminal_record,
    BinaryReflectedTerminalFactoryMeasured.collect,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    table cached result K outer ≤ 2*listCells (BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached N bits result hSuccess K outer).1.2  := by
  rw [BinaryReflectedTerminalFactoryMeasured.prepared_record]
  simpa only [BinaryReflectedTerminalFactoryMeasured.attach] using table_bound cached result K outer

def reflect (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) : ℕ :=
  tableCost 3 (fun j => BinaryArithmeticEntryWork.raw .sub ((BinaryReflectedFourSetup.originalLengths input).read j) (row.read j))

theorem reflect_bound (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    reflect input row ≤ 2*listCells (BinaryReflectedEmissionMeasured.reflect input row).1.2 := by
  have h := build_bound 3
    (fun j => BinaryQuadraticMeasured.apply .sub ((BinaryReflectedFourSetup.originalLengths input).read j) (row.read j))
    (fun j => BinaryArithmeticEntryWork.raw .sub ((BinaryReflectedFourSetup.originalLengths input).read j) (row.read j))
    (fun _j => quadratic_bound .sub _ _)
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,reflect,BinaryReflectedEmissionMeasured.reflect_record,BinaryReflectedEmissionMeasured.collectRow,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def emission (input : BinaryFourParameters.Input) (segment : BinaryStoredOverlapEnvironment.Segment 3 18)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) : ℕ :=
  BinaryPhysicalArithmeticEntryWork.point segment slot K scalar+
    reflect input (BinaryPhysicalPointMeasured.sample segment slot K scalar).1.1

theorem emission_bound (input : BinaryFourParameters.Input) (segment : BinaryStoredOverlapEnvironment.Segment 3 18)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    emission input segment slot K scalar ≤ 2*listCells (BinaryReflectedEmissionMeasured.sample input segment slot K scalar).1.2 := by
  have hp := BinaryPhysicalArithmeticEntryWork.point_bound segment slot K scalar
  have hr := reflect_bound input (BinaryPhysicalPointMeasured.sample segment slot K scalar).1.1
  simp only [emission,BinaryReflectedEmissionMeasured.sample_record,BinaryReflectedEmissionMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def tableDraw (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  BinaryCategoricalArithmeticEntryWork.select store prepared (0 : Fin 18) pc hp+
    match (BinaryWordSegmentMeasured.select store prepared (0 : Fin 18) pc hp).1.1.1 with
    | none => 0
    | some slot => emission input prepared.table slot K scalar

theorem tableDraw_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    tableDraw store input prepared K scalar pc hp ≤ 2*listCells (BinaryReflectedTableDrawMeasured.run store input prepared K scalar pc hp).1.2 := by
  have hs := BinaryCategoricalArithmeticEntryWork.select_bound store prepared (0 : Fin 18) pc hp
  simp only [tableDraw,BinaryReflectedTableDrawMeasured.run_record]
  cases h : (BinaryWordSegmentMeasured.select store prepared (0 : Fin 18) pc hp).1.1.1 with
  | none => simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  | some slot =>
    have he := emission_bound input prepared.table slot K scalar
    simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega

def afterResource (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (BinaryReflectedFourSetup.prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : ℕ :=
  match hResult : resource.1 with
  | none => 0
  | some result =>
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
      let prepared := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      table cached result K outer+tableDraw store input prepared.1.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)

theorem afterResource_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (BinaryReflectedFourSetup.prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    afterResource store input hC hAd cached pc hp resource hResource K outer scalar ≤
      2*listCells (BinaryReflectedDrawMeasured.afterResource store input hC hAd cached pc hp resource hResource K outer scalar).1.2 := by
  rw [BinaryReflectedDrawMeasured.afterResource_record]
  unfold afterResource
  dsimp only
  split
  · rename_i hNone
    split
    · omega
    · rename_i other hOther
      rw [hNone] at hOther
      cases hOther
  · rename_i result hSome
    split
    · rename_i hNone
      rw [hNone] at hSome
      cases hSome
    · rename_i other hOther
      have hEqual : other = result := Option.some.inj (hOther.symm.trans hSome)
      subst other
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hSome)
      let prepared := BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached
        (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      have ht := prepared_bound input hC hAd cached (store.cap.value-pc.value)
        (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
      have hd := tableDraw_bound store input prepared.1.1 K scalar resource.2
        (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
      dsimp only [prepared] at hd
      simp only [wrap,combine,listCells_append,listCells_under,listCells]
      omega


theorem afterResource_input_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (BinaryReflectedFourSetup.prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (source : RationalFourInput) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    afterResource store input hC hAd cached pc hp resource hResource K outer scalar ≤
      2*BinaryReflectedDrawMeasured.afterEnvelope s K store.width store.cap.value := by
  have he := afterResource_bound store input hC hAd cached pc hp resource hResource K outer scalar
  have hu := (BinaryReflectedDrawMeasured.afterResource_bounds store input source hC hR hCase hAd s hs hH
    cached pc hp resource hResource K outer scalar).2
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hu
  omega

end Blotto.BinaryReflectedTerminalArithmeticEntryWork

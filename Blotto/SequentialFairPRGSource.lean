import Blotto.FreshBitStateTransport

/-! Four concrete complete request runners use the sequential Boolean source.
The deterministic square preserves every output/trace/cost field; the fair
interpretation fixes the finite fair-tape law internally. Native pointer and
allocator prices are not assigned here. -/
namespace Blotto.SequentialFairPRGSource
open BinarySeedPreparationSpace FreshBitStateTransport FreshBitSeedLifetime
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Single (S : Type) := ((((((((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (BinaryPromiseOpcodeRequest.Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ

abbrev Pair (S : Type) := (((((((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (BinaryPromiseOpcodeRequest.Prices × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)))) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ

def generated (rich : Bool) (frame tape : List Bool) : Single (List Bool) :=
  BinaryPromiseOpcodeRequest.generatedWithFactoryExtras SequentialFairBitSource.next rich frame tape

def parsedGenerated (rich : Bool) (frame tape : List Bool) : Single (List Bool) :=
  BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras SequentialFairBitSource.next rich frame tape

def pair (frame tape : List Bool) : Pair (List Bool) :=
  BinaryPromiseOpcodeRequest.pairWithFactoryExtras SequentialFairBitSource.next frame tape

def parsedPair (frame tape : List Bool) : Pair (List Bool) :=
  BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras SequentialFairBitSource.next frame tape

theorem tape_vector {N : ℕ} (bits : Fin N → Bool) :
    (fun position => (List.ofFn bits).getD position false) = vectorTape bits := by
  funext position
  by_cases h : position < N
  · simp [vectorTape,h,List.getD_eq_getElem?_getD]
  · simp [vectorTape,h,List.getD_eq_getElem?_getD]

theorem generated_transport (rich : Bool) (frame tape : List Bool) (position : ℕ) :
    generated rich frame (tape.drop position) =
      mapState (fun i => tape.drop i)
        (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras
          (tapeFresh (fun i => tape.getD i false)) rich frame position) := by
  exact FreshBitStateTransport.generated BinaryPromiseOpcodeRequest.backend
    (tapeFresh (fun i => tape.getD i false)) SequentialFairBitSource.next
    (fun i => tape.drop i) (fun i => SequentialFairBitSource.next_drop tape i) rich frame position

theorem generated_vector {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    generated rich frame (List.ofFn bits) =
      mapState (fun i => (List.ofFn bits).drop i)
        (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0) := by
  simpa only [List.drop_zero,tape_vector] using generated_transport rich frame (List.ofFn bits) 0

theorem generated_observables {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    mapState (fun _ : List Bool => ()) (generated rich frame (List.ofFn bits)) =
      mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0) := by
  rw [generated_vector]
  rfl

theorem generated_mean (N : ℕ) (rich : Bool) (frame : List Bool) (test : Single Unit → ℝ) :
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : List Bool => ()) (generated rich frame (List.ofFn bits)))) =
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0))) := by
  simp only [generated_observables]

theorem parsedGenerated_transport (rich : Bool) (frame tape : List Bool) (position : ℕ) :
    parsedGenerated rich frame (tape.drop position) =
      mapState (fun i => tape.drop i)
        (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras
          (tapeFresh (fun i => tape.getD i false)) rich frame position) := by
  exact FreshBitStateTransport.parsedGenerated BinaryPromiseOpcodeRequest.backend
    (tapeFresh (fun i => tape.getD i false)) SequentialFairBitSource.next
    (fun i => tape.drop i) (fun i => SequentialFairBitSource.next_drop tape i) rich frame position

theorem parsedGenerated_vector {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    parsedGenerated rich frame (List.ofFn bits) =
      mapState (fun i => (List.ofFn bits).drop i)
        (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0) := by
  simpa only [List.drop_zero,tape_vector] using parsedGenerated_transport rich frame (List.ofFn bits) 0

theorem parsedGenerated_observables {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    mapState (fun _ : List Bool => ()) (parsedGenerated rich frame (List.ofFn bits)) =
      mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0) := by
  rw [parsedGenerated_vector]
  rfl

theorem parsedGenerated_mean (N : ℕ) (rich : Bool) (frame : List Bool) (test : Single Unit → ℝ) :
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : List Bool => ()) (parsedGenerated rich frame (List.ofFn bits)))) =
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (tapeFresh (vectorTape bits)) rich frame 0))) := by
  simp only [parsedGenerated_observables]

theorem pair_transport (frame tape : List Bool) (position : ℕ) :
    pair frame (tape.drop position) =
      mapState (fun i => tape.drop i)
        (BinaryPromiseOpcodeRequest.pairWithFactoryExtras
          (tapeFresh (fun i => tape.getD i false)) frame position) := by
  exact FreshBitStateTransport.pair BinaryPromiseOpcodeRequest.backend
    (tapeFresh (fun i => tape.getD i false)) SequentialFairBitSource.next
    (fun i => tape.drop i) (fun i => SequentialFairBitSource.next_drop tape i) frame position

theorem pair_vector {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    pair frame (List.ofFn bits) =
      mapState (fun i => (List.ofFn bits).drop i)
        (BinaryPromiseOpcodeRequest.pairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0) := by
  simpa only [List.drop_zero,tape_vector] using pair_transport frame (List.ofFn bits) 0

theorem pair_observables {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    mapState (fun _ : List Bool => ()) (pair frame (List.ofFn bits)) =
      mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.pairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0) := by
  rw [pair_vector]
  rfl

theorem pair_mean (N : ℕ) (frame : List Bool) (test : Pair Unit → ℝ) :
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : List Bool => ()) (pair frame (List.ofFn bits)))) =
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.pairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0))) := by
  simp only [pair_observables]

theorem parsedPair_transport (frame tape : List Bool) (position : ℕ) :
    parsedPair frame (tape.drop position) =
      mapState (fun i => tape.drop i)
        (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras
          (tapeFresh (fun i => tape.getD i false)) frame position) := by
  exact FreshBitStateTransport.parsedPair BinaryPromiseOpcodeRequest.backend
    (tapeFresh (fun i => tape.getD i false)) SequentialFairBitSource.next
    (fun i => tape.drop i) (fun i => SequentialFairBitSource.next_drop tape i) frame position

theorem parsedPair_vector {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    parsedPair frame (List.ofFn bits) =
      mapState (fun i => (List.ofFn bits).drop i)
        (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0) := by
  simpa only [List.drop_zero,tape_vector] using parsedPair_transport frame (List.ofFn bits) 0

theorem parsedPair_observables {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    mapState (fun _ : List Bool => ()) (parsedPair frame (List.ofFn bits)) =
      mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0) := by
  rw [parsedPair_vector]
  rfl

theorem parsedPair_mean (N : ℕ) (frame : List Bool) (test : Pair Unit → ℝ) :
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : List Bool => ()) (parsedPair frame (List.ofFn bits)))) =
    (fairBitKernel N).mean (fun bits =>
      test (mapState (fun _ : ℕ => ())
        (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras (tapeFresh (vectorTape bits)) frame 0))) := by
  simp only [parsedPair_observables]

attribute [local irreducible] BinaryCacheFinishRequest.seedWithFactoryExtras BinaryPromiseOpcodeRequest.backend


-- Observer only: the four runners neither call this nor parse twice.
def drawCount (frame : List Bool) : ℕ :=
  match (BinaryPromiseOpcodeRequest.backend.run frame).1.1.1.1 with
  | none => 0
  | some parsed => if parsed.2 = [] then
      RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision else 0

theorem drawCount_bound (frame : List Bool) :
    drawCount frame ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  unfold drawCount
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · have hPhys := (congrArg Prod.fst
          (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).symm.trans hRead
      have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
      rw [hPhys,Option.map_some] at hRef
      exact BinaryPRGSeedRequestBound.read_seedCount_bound frame
        (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRef.symm
    · exact Nat.zero_le _


theorem generated_remaining (rich : Bool) (frame tape : List Bool) :
    (generated rich frame tape).1.1.1.1.1.1.1.1.1.1.2 = tape.drop (drawCount frame) := by
  unfold generated BinaryPromiseOpcodeRequest.generatedWithFactoryExtras
    BinaryRawParserContinuation.generatedWithFactoryExtras drawCount
  dsimp only
  split
  · rename_i hRead
    simp only [hRead,List.drop_zero]
  · rename_i parsed hRead
    simp only [hRead]
    split
    · rename_i hTail
      simpa only [ite_eq_left hTail] using SequentialFairBitSource.planned_remaining parsed.1.2.logical tape
    · rename_i hTail
      simp only [ite_eq_right hTail,List.drop_zero]


theorem parsedGenerated_remaining (rich : Bool) (frame tape : List Bool) :
    (parsedGenerated rich frame tape).1.1.1.1.1.1.1.1.1.1.2 = tape.drop (drawCount frame) := by
  unfold parsedGenerated BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras
    BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras drawCount
  dsimp only
  split
  · rename_i hRead
    simp only [hRead,List.drop_zero]
  · rename_i parsed hRead
    simp only [hRead]
    split
    · rename_i hTail
      simpa only [ite_eq_left hTail] using SequentialFairBitSource.planned_remaining parsed.1.2.logical tape
    · rename_i hTail
      simp only [ite_eq_right hTail,List.drop_zero]


theorem pair_remaining (frame tape : List Bool) :
    (pair frame tape).1.1.1.1.1.1.1.1.1.1.2 = tape.drop (drawCount frame+drawCount frame) := by
  change (generated false frame (generated true frame tape).1.1.1.1.1.1.1.1.1.1.2).1.1.1.1.1.1.1.1.1.1.2 = _
  rw [generated_remaining,generated_remaining,List.drop_drop]


theorem parsedPair_remaining (frame tape : List Bool) :
    (parsedPair frame tape).1.1.1.1.1.1.1.1.1.1.2 = tape.drop (drawCount frame+drawCount frame) := by
  change (parsedGenerated false frame (parsedGenerated true frame tape).1.1.1.1.1.1.1.1.1.1.2).1.1.1.1.1.1.1.1.1.1.2 = _
  rw [parsedGenerated_remaining,parsedGenerated_remaining,List.drop_drop]

theorem generated_counted {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S × ℕ) :
    (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (countedFresh next) rich frame state).1.1.1.1.1.1.1.1.1.1.2.2 =
      state.2+drawCount frame := by
  unfold BinaryPromiseOpcodeRequest.generatedWithFactoryExtras
    BinaryRawParserContinuation.generatedWithFactoryExtras drawCount
  dsimp only
  split
  · rename_i hRead
    simp only [hRead,Nat.add_zero]
  · rename_i parsed hRead
    simp only [hRead]
    split
    · rename_i hTail
      simp only [ite_eq_left hTail,BinaryFreshGenerationPlan.generateWithEmission_compat]
      exact congrArg (fun out => out.2.2)
        (BinaryPRGRulerSeedMeasured.generate_counted next parsed.1.2.logical state.1 state.2)
    · rename_i hTail
      simp only [ite_eq_right hTail,Nat.add_zero]

theorem parsedGenerated_counted {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S × ℕ) :
    (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (countedFresh next) rich frame state).1.1.1.1.1.1.1.1.1.1.2.2 =
      state.2+drawCount frame := by
  unfold BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras
    BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras drawCount
  dsimp only
  split
  · rename_i hRead
    simp only [hRead,Nat.add_zero]
  · rename_i parsed hRead
    simp only [hRead]
    split
    · rename_i hTail
      simp only [ite_eq_left hTail,BinaryFreshGenerationPlan.generateWithEmission_compat]
      exact congrArg (fun out => out.2.2)
        (BinaryPRGRulerSeedMeasured.generate_counted next parsed.1.2.logical state.1 state.2)
    · rename_i hTail
      simp only [ite_eq_right hTail,Nat.add_zero]

theorem pair_counted {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S × ℕ) :
    (BinaryPromiseOpcodeRequest.pairWithFactoryExtras (countedFresh next) frame state).1.1.1.1.1.1.1.1.1.1.2.2 =
      state.2+drawCount frame+drawCount frame := by
  change (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (countedFresh next) false frame
    (BinaryPromiseOpcodeRequest.generatedWithFactoryExtras (countedFresh next) true frame state).1.1.1.1.1.1.1.1.1.1.2).1.1.1.1.1.1.1.1.1.1.2.2 = _
  rw [generated_counted,generated_counted]

theorem parsedPair_counted {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S × ℕ) :
    (BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras (countedFresh next) frame state).1.1.1.1.1.1.1.1.1.1.2.2 =
      state.2+drawCount frame+drawCount frame := by
  change (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (countedFresh next) false frame
    (BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras (countedFresh next) true frame state).1.1.1.1.1.1.1.1.1.1.2).1.1.1.1.1.1.1.1.1.1.2.2 = _
  rw [parsedGenerated_counted,parsedGenerated_counted]

theorem generated_exhausts (rich : Bool) (frame : List Bool) (bits : Fin (drawCount frame) → Bool) :
    (generated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.2 = [] := by
  rw [generated_remaining]
  exact List.drop_eq_nil_of_le (by simp [List.length_ofFn])

theorem parsedGenerated_exhausts (rich : Bool) (frame : List Bool) (bits : Fin (drawCount frame) → Bool) :
    (parsedGenerated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.2 = [] := by
  rw [parsedGenerated_remaining]
  exact List.drop_eq_nil_of_le (by simp [List.length_ofFn])

theorem pair_exhausts (frame : List Bool) (bits : Fin (drawCount frame+drawCount frame) → Bool) :
    (pair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.2 = [] := by
  rw [pair_remaining]
  exact List.drop_eq_nil_of_le (by simp [List.length_ofFn])

theorem parsedPair_exhausts (frame : List Bool) (bits : Fin (drawCount frame+drawCount frame) → Bool) :
    (parsedPair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.2 = [] := by
  rw [parsedPair_remaining]
  exact List.drop_eq_nil_of_le (by simp [List.length_ofFn])

theorem single_tape_bound (frame : List Bool) (bits : Fin (drawCount frame) → Bool) :
    (List.ofFn bits).length ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  simpa only [List.length_ofFn] using drawCount_bound frame

theorem pair_tape_bound (frame : List Bool) (bits : Fin (drawCount frame+drawCount frame) → Bool) :
    (List.ofFn bits).length ≤ 2*BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  have h := drawCount_bound frame
  simp only [List.length_ofFn]
  omega

end Blotto.SequentialFairPRGSource

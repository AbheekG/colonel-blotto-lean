import Blotto.BinaryPhysicalHeapInitialLifetime
import Blotto.BinaryPRGHeapRequestLifetime

/-! The seeded resource loop can start from the parser's physically read-back
numerical words. This route keeps the old logical request as its refinement
index; no second numerical tree is built by its initializer. -/
namespace Blotto.BinaryPhysicalHeapRequestLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapResourceSource (capStore count)
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- An algebraic initial-preparation allowance driven only by the two
retained physical object tapes. No second tree is constructed. -/
def preparationAllowance (request : Request n) : ℕ :=
  BinaryPRGHeapResourceInputBounds.preparationBound n
    (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)

/-- The portion of preparation work outside the two physical tree builds. -/
def preparationResidualAllowance (request : Request n) : ℕ :=
  BinaryPRGHeapResourceInputBounds.preparationResidualBound n
    (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request)

theorem preparationResidualAllowance_le_preparationAllowance
    (request : Request n) :
    preparationResidualAllowance request ≤ preparationAllowance request := by
  unfold preparationResidualAllowance preparationAllowance
  rw [BinaryPRGHeapResourceInputBounds.preparationBound_split]
  omega

theorem readback_build_plus_residual_le_preparationAllowance
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
      words.1 (if rich then words.1 else words.2)).2 +
      preparationResidualAllowance request ≤ preparationAllowance request := by
  have hBuild := BinaryPhysicalHeapInitialLifetime.request_readback_build_work_bound
    request rich
  unfold preparationResidualAllowance preparationAllowance
  rw [BinaryPRGHeapResourceInputBounds.preparationBound_split]
  omega

theorem native_initial_work_le_preparationAllowance
    (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (BinaryPRGHeapResourceSource.initialWithWork
      selected.length selected.resource
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
        preparationAllowance request := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW : 1 ≤ W :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have hNative := BinaryPRGHeapResourceSource.initialWithWork_bound
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
  have hInput := BinaryPRGHeapResourceInputBounds.initialWorkEnvelope_input_bound
    selected.length selected.resource W hW hCapacity hResource
  exact hNative.trans hInput

theorem native_initial_work_le_readback_build_plus_residual
    (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (BinaryPRGHeapResourceSource.initialWithWork
      selected.length selected.resource
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 +
      preparationResidualAllowance request := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hW : 1 ≤ W :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_pos request
  obtain ⟨hl,hr⟩ :=
    BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth_inputs request
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    cases rich <;> exact hl
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    cases rich
    · exact hr
    · exact hl
  have hNative := BinaryPRGHeapResourceInputBounds.initialWithWork_le_nativeBuild_plus_residual
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    W hW hCapacity hResource
  have hBuild := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_covers_native
    selected.length.data.toList selected.resource.data.toList
  have hRuler :
      (BinaryPRGHeapAllocationLifetime.countWithTrace selected.length.data.toList []).1 =
        BinaryCarryCounter.count selected.length.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure
      selected.length.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure
        selected.length.data.toList [])
  dsimp only at hBuild
  rw [hRuler] at hBuild
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  have hCombined :
      (BinaryPRGHeapResourceSource.initialWithWork
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        selected.length.data.toList selected.resource.data.toList).2 +
      BinaryPRGHeapResourceInputBounds.preparationResidualBound n W := by
    dsimp only at hNative
    omega
  dsimp only
  rw [hWords]
  cases rich <;> simpa [selected,W,preparationResidualAllowance,
    BinaryPRGResourceWork.resourceInput,
    BinaryPRGPreparation.Prepared.rich,BinaryPRGPreparation.Prepared.poor] using hCombined

theorem uniform_preparationAllowance_bound : ∃ C d : ℕ,
    ∀ {n : ℕ} (request : Request n),
      preparationAllowance request ≤
        C*(n+BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request+2)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPRGHeapResourcePolynomial.nativeBound_polynomial
  refine ⟨C,d,?_⟩
  intro n request
  let W := BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth request
  have hNative := hBound
    (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)
  have hPrep : BinaryPRGHeapResourceInputBounds.preparationBound n W ≤
      BinaryPRGHeapResourceInputCost.nativeBound n W 0 0 0 := by
    unfold BinaryPRGHeapResourceInputCost.nativeBound
    omega
  unfold BinaryPRGHeapResourcePolynomial.inputSize at hNative
  simp only [binaryWordWidth,Nat.log2_zero,Nat.zero_add,Nat.add_zero] at hNative
  unfold preparationAllowance
  simpa only [W,Nat.add_assoc,show (1:ℕ)+1=2 by omega] using
    hPrep.trans hNative

theorem accepted_preparationAllowance_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      preparationAllowance parsed.1.2 ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hPrep⟩ := uniform_preparationAllowance_bound
  refine ⟨C*130^d,2*d,?_⟩
  intro frame parsed hParsed
  let x := frame.length+3
  have hx : 3 ≤ x := by dsimp only [x]; omega
  have hDimension :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_dimension frame parsed hParsed
  have hWidth :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_physicalWordWidth_bound
      frame parsed hParsed
  have hHeap : PRGPhysicalArrayInterface.heapCap frame.length ≤ 128*x^2 := by
    unfold PRGPhysicalArrayInterface.heapCap
    dsimp only [x]
    nlinarith
  have hSize : parsed.1.1+
      BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2+2 ≤
        130*x^2 := by
    have hX : x ≤ x^2 := by nlinarith
    have hThree : 3 ≤ x^2 := by nlinarith
    omega
  have hBound := hPrep parsed.1.2
  calc
    _ ≤ C*(parsed.1.1+
          BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2+2)^d := hBound
    _ ≤ C*(130*x^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
    _ = (C*130^d)*x^(2*d) := by
      rw [mul_pow,pow_mul]
      ring

/-- Every accepted frame has a polynomial retained-source envelope for the
actual two-builder trace reached after physical numerical readback. -/
theorem accepted_readback_rawArrays_usage_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool,
      let request := parsed.1.2
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[])
      usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
        words.1 (if rich then words.1 else words.2)).2 ≤
        C*(frame.length+3)^d := by
  obtain ⟨P,e,hPrepBound⟩ := accepted_preparationAllowance_polynomial
  refine ⟨33*P+532,max e 2,?_⟩
  intro frame parsed hParsed rich
  let Q := frame.length+3
  let D := max e 2
  have hDimension :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_dimension frame parsed hParsed
  have hPrep := hPrepBound frame parsed hParsed
  have hUsage := BinaryPhysicalHeapInitialLifetime.request_readback_rawArrays_usage_input_bound
    parsed.1.2 rich
  change usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
    ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])).1
    (if rich then ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])).1 else
      ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])).2)).2 ≤
    33 * (BinaryPRGWordStoreHeapMachine.countBound parsed.1.1 0 +
      preparationAllowance parsed.1.2) + 6*parsed.1.1 + 130 at hUsage
  have hQ : 1 ≤ Q := by dsimp only [Q]; omega
  have hN : parsed.1.1+1 ≤ Q := by dsimp only [Q]; omega
  have hN2 := Nat.mul_le_mul hN hN
  have hCount : BinaryPRGWordStoreHeapMachine.countBound parsed.1.1 0 ≤
      12*Q^2 := by
    unfold BinaryPRGWordStoreHeapMachine.countBound
    nlinarith
  have h2 : Q^2 ≤ Q^D :=
    Nat.pow_le_pow_right (by omega : 0<Q) (Nat.le_max_right e 2)
  have he : Q^e ≤ Q^D :=
    Nat.pow_le_pow_right (by omega : 0<Q) (Nat.le_max_left e 2)
  have hCountTop : 33*BinaryPRGWordStoreHeapMachine.countBound parsed.1.1 0 ≤
      396*Q^D := by
    have h := Nat.mul_le_mul_left 33 hCount
    omega
  have hPrepTop : 33*preparationAllowance parsed.1.2 ≤
      (33*P)*Q^D := by
    change preparationAllowance parsed.1.2 ≤ P*Q^e at hPrep
    have hp := Nat.mul_le_mul_left (33*P) he
    calc
      _ ≤ 33*(P*Q^e) := Nat.mul_le_mul_left 33 hPrep
      _ = (33*P)*Q^e := by ring
      _ ≤ (33*P)*Q^D := hp
  have hLinear : 6*parsed.1.1+130 ≤ 136*Q^D := by
    have hOne : 1 ≤ Q^D := Nat.one_le_pow D Q hQ
    have hQ2 : Q ≤ Q^2 := by nlinarith
    have hNTop : parsed.1.1 ≤ Q^D := by omega
    omega
  dsimp only
  change usage (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
    ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])).1
    (if rich then ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
      parsed.1.2).1.1.getD ([],[])).1 else
      ((BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        parsed.1.2).1.1.getD ([],[])).2)).2 ≤
    (33*P+532)*Q^D
  calc
    _ ≤ 33 * (BinaryPRGWordStoreHeapMachine.countBound parsed.1.1 0 +
      preparationAllowance parsed.1.2) + 6*parsed.1.1 + 130 := hUsage
    _ ≤ 396*Q^D + (33*P)*Q^D + 136*Q^D := by omega
    _ = (33*P+532)*Q^D := by ring

theorem accepted_readback_rawArrays_all_prefix_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (rich : Bool) (borrowed steps : ℕ),
      let request := parsed.1.2
      let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[])
      let trace := (BinaryPhysicalHeapInputLifetime.rawArraysWithTrace
        words.1 (if rich then words.1 else words.2)).2
      retainedHeap borrowed trace steps ≤ borrowed+C*(frame.length+3)^d ∧
        framePeak (trace.take steps) ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_readback_rawArrays_usage_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed rich) borrowed steps

/-- The actual selected initializer's source trace, with its two physical
tree builds, has a uniform polynomial envelope in the retained tape width. -/
theorem uniform_physical_initial_trace_envelope : ∃ C d : ℕ,
    ∀ n W : ℕ,
      BinaryPRGHeapInitialLifetimeBound.envelope n W (binaryWordWidth n) ≤
        C*(n+W+2)^d := by
  obtain ⟨C,d,hBound⟩ :=
    BinaryPRGHeapNativeLifetimePolynomial.array_envelope_polynomial
  refine ⟨C,d,?_⟩
  intro n W
  have hNative : BinaryPRGHeapInitialLifetimeBound.envelope n W
      (binaryWordWidth n) ≤
      BinaryPRGHeapNativeLifetimeBound.envelope n W 0 0 0 := by
    unfold BinaryPRGHeapNativeLifetimeBound.envelope
    omega
  have h := hBound
    (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize
      (⟨n,W,0,0,0⟩ : BinaryPRGHeapResourcePolynomial.Parameters)+1 =
      n+W+2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hNative.trans h

theorem accepted_physical_initial_trace_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,Request n) × List Bool),
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) →
      ∀ rich : Bool,
      usage (BinaryPhysicalHeapInitialLifetime.initialFromParsedWithTrace
        frame parsed hParsed rich).2 ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hEnvelope⟩ := uniform_physical_initial_trace_envelope
  refine ⟨2000000200+C*130^d+38,max 7 (2*d),?_⟩
  intro frame parsed hParsed rich
  let x := frame.length+3
  let D := max 7 (2*d)
  have hx : 3 ≤ x := by dsimp only [x]; omega
  have hDimension :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_dimension frame parsed hParsed
  have hWidth :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_physicalWordWidth_bound
      frame parsed hParsed
  have hHeap : PRGPhysicalArrayInterface.heapCap frame.length ≤ 128*x^2 := by
    unfold PRGPhysicalArrayInterface.heapCap
    dsimp only [x]
    nlinarith
  have hSize : parsed.1.1+
      BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2+2 ≤
        130*x^2 := by
    have hX : x ≤ x^2 := by nlinarith
    have hThree : 3 ≤ x^2 := by nlinarith
    omega
  have hEnv : BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1
      (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2)
      (binaryWordWidth parsed.1.1) ≤ (C*130^d)*x^(2*d) := by
    have h := hEnvelope parsed.1.1
      (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2)
    calc
      _ ≤ C*(parsed.1.1+
          BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2+2)^d := h
      _ ≤ C*(130*x^2)^d :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
      _ = (C*130^d)*x^(2*d) := by rw [mul_pow,pow_mul]; ring
  have hUsage := BinaryPhysicalHeapInitialLifetime.initialFromParsed_physical_usage
    frame parsed hParsed rich
  have h7 : x^7 ≤ x^D :=
    Nat.pow_le_pow_right (by omega : 0<x) (Nat.le_max_left 7 (2*d))
  have he : x^(2*d) ≤ x^D :=
    Nat.pow_le_pow_right (by omega : 0<x) (Nat.le_max_right 7 (2*d))
  have hOne : 1 ≤ x^D := Nat.one_le_pow D x (by omega)
  have hFirst := Nat.mul_le_mul_left 2000000200 h7
  have hSecond := Nat.mul_le_mul_left (C*130^d) he
  have hThird : 38 ≤ 38*x^D := by nlinarith only [hOne]
  change usage (BinaryPhysicalHeapInitialLifetime.initialFromParsedWithTrace
    frame parsed hParsed rich).2 ≤ (2000000200+C*130^d+38)*x^D
  calc
    _ ≤ 2000000200*x^7+
        BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1
          (BinaryPhysicalNumericalReadbackLifetime.physicalWordWidth parsed.1.2)
          (binaryWordWidth parsed.1.1)+38 := hUsage
    _ ≤ 2000000200*x^D+(C*130^d)*x^D+38*x^D := by omega
    _ = (2000000200+C*130^d+38)*x^D := by ring

theorem accepted_physical_initial_trace_prefix_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,Request n) × List Bool),
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) →
      ∀ (rich : Bool) (borrowed steps : ℕ),
      retainedHeap borrowed
        (BinaryPhysicalHeapInitialLifetime.initialFromParsedWithTrace
          frame parsed hParsed rich).2 steps ≤
          borrowed+C*(frame.length+3)^d ∧
      framePeak ((BinaryPhysicalHeapInitialLifetime.initialFromParsedWithTrace
        frame parsed hParsed rich).2.take steps) ≤
          C*(frame.length+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_physical_initial_trace_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich borrowed steps
  exact BinaryPRGHeapTraceUsage.all_prefix _ _
    (hUsage frame parsed hParsed rich) borrowed steps

def sourceAtWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × Trace) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork request rich
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.ruler,prepared.1.1.1.size⟩
  let completed := BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed prepared.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.2 pc hp
  (((capWord,completed.1.1),wrap 32 2 [prepared.1.2,completed.1.2]),
    prepared.2+completed.2)

/-- Resource source with the work of the same two physical builds carried
from its one-pass initializer. -/
def sourceAtWithTraceAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    ((FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × Trace) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndBuildWork
    request rich
  let capWord : FixedBinaryWord (capStore selected.length).width :=
    ⟨prepared.1.1.1.ruler,prepared.1.1.1.size⟩
  let completed := BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed prepared.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.2 pc hp
  (((capWord,completed.1.1),wrap 32 2 [prepared.1.2,completed.1.2]),
    prepared.2+completed.2)

theorem sourceAtWithTraceAndBuildWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndBuildWork seed request rich pc hp).1 =
      (sourceAtWithTraceAndWork seed request rich pc hp).1 := by
  rfl

theorem sourceAtWithTraceAndBuildWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (sourceAtWithTraceAndBuildWork seed request rich pc hp).2 =
      (sourceAtWithTraceAndWork seed request rich pc hp).2+
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2 := by
  unfold sourceAtWithTraceAndBuildWork sourceAtWithTraceAndWork
  dsimp only
  rw [BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndBuildWork_charge]
  simp only [BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndBuildWork_erases]
  omega

theorem sourceAtWithTraceAndWork_le_buildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndWork seed request rich pc hp).2 ≤
      (sourceAtWithTraceAndBuildWork seed request rich pc hp).2 := by
  rw [sourceAtWithTraceAndBuildWork_charge]
  omega

theorem sourceAtWithTraceAndBuildWork_bound (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndBuildWork seed request rich pc hp).2 ≤
      (sourceAtWithTraceAndWork seed request rich pc hp).2+
        preparationAllowance request := by
  unfold sourceAtWithTraceAndBuildWork sourceAtWithTraceAndWork
  dsimp only
  have h := BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndBuildWork_bound
    request rich
  simp only [BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndBuildWork_erases]
  unfold preparationAllowance
  omega

def sourceAtWithTrace (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (FixedBinaryWord (capStore selected.length).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore selected.length) n
        (count selected.length)) × Trace :=
  (sourceAtWithTraceAndWork seed request rich pc hp).1

theorem sourceAtWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndWork seed request rich pc hp).2 =
      BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource +
      (2*n+5) +
      (BinaryPRGHeapResourceLoop.runWithWork seed
        (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTrace request rich).1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
          (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
          (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
        (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTrace request rich).1.2
        pc hp).2 := by
  unfold sourceAtWithTraceAndWork
  dsimp only
  rw [BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork_charge]
  rw [BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork_charge]
  rfl

theorem sourceAtWithTraceAndWork_le_native (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndWork seed request rich pc hp).2 ≤
      (BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork seed
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
        pc hp).2 := by
  unfold sourceAtWithTraceAndWork BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork
  dsimp only
  have hPrepared := BinaryPhysicalHeapInitialLifetime.initialFromRequest_erasure request rich
  change (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork request rich).1.1 = _
    at hPrepared
  have hNative := BinaryPRGHeapInitialLifetime.initialWithTrace_erasure
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
  have hScan := BinaryPRGHeapInitialLifetime.initialPhysicalScanWork_plus_control_le_initialWithWork
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
  rw [BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork_charge]
  rw [hPrepared,hNative]
  omega

theorem sourceAt_erasure (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTrace seed request rich pc hp).1 =
      (BinaryPRGHeapNativeLifetime.sourceWithTrace seed
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
        pc hp).1 := by
  unfold sourceAtWithTrace sourceAtWithTraceAndWork BinaryPRGHeapNativeLifetime.sourceWithTrace
    BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork
    BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork
  dsimp only
  have hPrepared := BinaryPhysicalHeapInitialLifetime.initialFromRequest_erasure request rich
  apply Prod.ext
  · exact congrArg (fun prepared =>
      (⟨prepared.1.ruler,prepared.1.size⟩ : FixedBinaryWord
        (capStore (BinaryPRGResourceWork.resourceInput request.logical.request rich).length).width))
      hPrepared
  · exact congrArg (fun prepared =>
      (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
          (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
          (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
        prepared.2 pc hp).1) hPrepared

theorem sourceAt_cap (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTrace seed request rich pc hp).1.1 =
      (capStore (BinaryPRGResourceWork.resourceInput request.logical.request rich).length).cap := by
  rw [sourceAt_erasure]
  exact BinaryPRGHeapNativeLifetime.sourceWithTrace_cap seed
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2 pc hp

theorem sourceAtWithTraceAndBuildWork_cap (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTraceAndBuildWork seed request rich pc hp).1.1.1 =
      (capStore (BinaryPRGResourceWork.resourceInput request.logical.request rich).length).cap := by
  rw [sourceAtWithTraceAndBuildWork_erases]
  exact sourceAt_cap seed request rich pc hp

private def materializationCharge (seed : BinarySeedLookupTree.Store)
    (capacity : FixedArrayTable n SignedWord)
    (drawn : {d : FixedBinaryWord (capStore capacity).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity) //
        d.1 = (capStore capacity).cap}) : ℕ :=
  match drawn.1.2.1 with
  | none => 0
  | some state =>
      (BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1 drawn.2 state).2

def nativeAtWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let drawn := sourceAtWithTraceAndWork seed request rich pc hp
  match drawn.1.1.2.1 with
  | none => (((none,drawn.1.1.2.2),wrap 16 2 [drawn.1.2]),drawn.2+2)
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1 (sourceAt_cap seed request rich pc hp) state
      let terminalCharge := (BinaryPRGHeapResourceMaterialization.materializeWithWork
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1 (sourceAt_cap seed request rich pc hp) state).2
      (((some terminal.1,drawn.1.1.2.2),wrap 24 2 [drawn.1.2,terminal.2]),
        drawn.2+terminalCharge+4)

def nativeAtWithTraceAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let drawn := sourceAtWithTraceAndBuildWork seed request rich pc hp
  match drawn.1.1.2.1 with
  | none => (((none,drawn.1.1.2.2),wrap 16 2 [drawn.1.2]),drawn.2+2)
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1 (sourceAtWithTraceAndBuildWork_cap seed request rich pc hp) state
      let terminalCharge := (BinaryPRGHeapResourceMaterialization.materializeWithWork
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1 (sourceAtWithTraceAndBuildWork_cap seed request rich pc hp) state).2
      (((some terminal.1,drawn.1.1.2.2),wrap 24 2 [drawn.1.2,terminal.2]),
        drawn.2+terminalCharge+4)

theorem nativeAtWithTraceAndBuildWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTraceAndBuildWork seed request rich pc hp).1 =
      (nativeAtWithTraceAndWork seed request rich pc hp).1 := by
  unfold nativeAtWithTraceAndBuildWork nativeAtWithTraceAndWork
  simp only [sourceAtWithTraceAndBuildWork_erases]
  cases hState : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;>
    rfl

theorem nativeAtWithTraceAndBuildWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (nativeAtWithTraceAndBuildWork seed request rich pc hp).2 =
      (nativeAtWithTraceAndWork seed request rich pc hp).2+
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2 := by
  have hSource := sourceAtWithTraceAndBuildWork_charge seed request rich pc hp
  unfold nativeAtWithTraceAndBuildWork nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAtWithTraceAndBuildWork_erases]
  cases hState : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;>
    dsimp only <;> omega

theorem nativeAtWithTraceAndBuildWork_bound (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTraceAndBuildWork seed request rich pc hp).2 ≤
      (nativeAtWithTraceAndWork seed request rich pc hp).2+
        preparationAllowance request := by
  have hSource := sourceAtWithTraceAndBuildWork_bound seed request rich pc hp
  unfold nativeAtWithTraceAndBuildWork nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAtWithTraceAndBuildWork_erases]
  cases hState : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;>
    dsimp only <;> omega

theorem nativeAtWithTraceAndWork_le_buildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTraceAndWork seed request rich pc hp).2 ≤
      (nativeAtWithTraceAndBuildWork seed request rich pc hp).2 := by
  have hSource := sourceAtWithTraceAndWork_le_buildWork seed request rich pc hp
  unfold nativeAtWithTraceAndBuildWork nativeAtWithTraceAndWork
  dsimp only
  simp only [sourceAtWithTraceAndBuildWork_erases]
  cases hState : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;>
    dsimp only <;> omega

theorem nativeAtWithTraceAndWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    let drawn := sourceAtWithTraceAndWork seed request rich pc hp
    (nativeAtWithTraceAndWork seed request rich pc hp).2 =
      match drawn.1.1.2.1 with
      | none => drawn.2+2
      | some state => drawn.2+
          (BinaryPRGHeapResourceMaterialization.materializeWithWork
            selected.length
            (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
            drawn.1.1.1 (sourceAt_cap seed request rich pc hp) state).2+4 := by
  unfold nativeAtWithTraceAndWork
  dsimp only
  cases h : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;> rfl

def nativeAtWithTrace (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let drawn := sourceAtWithTrace seed request rich pc hp
  match drawn.1.2.1 with
  | none => ((none,drawn.1.2.2),wrap 16 2 [drawn.2])
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1 (sourceAt_cap seed request rich pc hp) state
      ((some terminal.1,drawn.1.2.2),wrap 24 2 [drawn.2,terminal.2])

theorem nativeAtWithTraceAndWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTraceAndWork seed request rich pc hp).1 =
      nativeAtWithTrace seed request rich pc hp := by
  unfold nativeAtWithTraceAndWork nativeAtWithTrace sourceAtWithTrace
  dsimp only
  cases h : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 <;>
    rfl

theorem nativeAtWithTraceAndWork_le_native (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTraceAndWork seed request rich pc hp).2 ≤
      (BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork seed
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
        pc hp).2 := by
  have hSource := sourceAtWithTraceAndWork_le_native seed request rich pc hp
  have hData := sourceAt_erasure seed request rich pc hp
  simp only [sourceAtWithTrace,BinaryPRGHeapNativeLifetime.sourceWithTrace] at hData
  have hOption := congrArg (fun d => d.2.1) hData
  let capacity := (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
  have hSubtype :
      (⟨(sourceAtWithTraceAndWork seed request rich pc hp).1.1,
        sourceAt_cap seed request rich pc hp⟩ :
        {d : FixedBinaryWord (capStore capacity).width ×
          BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity) //
            d.1 = (capStore capacity).cap}) =
      ⟨(BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork seed
        capacity
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
        pc hp).1.1,
        BinaryPRGHeapNativeLifetime.sourceWithTrace_cap seed capacity
          (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
          (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
          (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
          pc hp⟩ := by
    apply Subtype.ext
    exact hData
  have hCharge := congrArg (materializationCharge seed capacity) hSubtype
  unfold nativeAtWithTraceAndWork BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork
  dsimp only
  cases h : (sourceAtWithTraceAndWork seed request rich pc hp).1.1.2.1 with
  | none =>
      have hLogical := hOption.symm.trans h
      simp only [hLogical]
      omega
  | some state =>
      have hLogical := hOption.symm.trans h
      simp only [hLogical]
      dsimp only [capacity] at hCharge
      simp only [materializationCharge,h,hLogical] at hCharge
      omega

private def materializedResult (seed : BinarySeedLookupTree.Store)
    (capacity : FixedArrayTable n SignedWord)
    (drawn : {d : FixedBinaryWord (capStore capacity).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity) //
        d.1 = (capStore capacity).cap}) :
    BinaryPRGWordControllerResource.Result seed capacity :=
  match drawn.1.2.1 with
  | none => (none,drawn.1.2.2)
  | some state =>
      let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        drawn.1.1 drawn.2 state
      (some terminal.1,drawn.1.2.2)

theorem nativeAt_erasure (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (nativeAtWithTrace seed request rich pc hp).1 =
      (BinaryPRGHeapNativeLifetime.nativeWithTrace seed
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
        pc hp).1 := by
  let capacity := (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
  let resource := (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
  let hC := (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
  let hR := (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
  let current := sourceAtWithTrace seed request rich pc hp
  let previous := BinaryPRGHeapNativeLifetime.sourceWithTrace seed capacity resource
    hC hR pc hp
  have hCurrent : (nativeAtWithTrace seed request rich pc hp).1 =
      materializedResult seed capacity ⟨current.1,sourceAt_cap seed request rich pc hp⟩ := by
    cases h : (sourceAtWithTrace seed request rich pc hp).1.2.1 <;>
      simp [nativeAtWithTrace,materializedResult,current,capacity,h]
  have hPrevious : (BinaryPRGHeapNativeLifetime.nativeWithTrace seed
      capacity resource hC hR pc hp).1 =
      materializedResult seed capacity
        ⟨previous.1,BinaryPRGHeapNativeLifetime.sourceWithTrace_cap
          seed capacity resource hC hR pc hp⟩ := by
    cases h : (BinaryPRGHeapNativeLifetime.sourceWithTrace seed
        capacity resource hC hR pc hp).1.2.1 <;>
      simp [BinaryPRGHeapNativeLifetime.nativeWithTrace,materializedResult,
        previous,h]
  have hSubtype :
      (⟨current.1,sourceAt_cap seed request rich pc hp⟩ :
        {d : FixedBinaryWord (capStore capacity).width ×
          BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity) //
            d.1 = (capStore capacity).cap}) =
      ⟨previous.1,BinaryPRGHeapNativeLifetime.sourceWithTrace_cap
        seed capacity resource hC hR pc hp⟩ := by
    apply Subtype.ext
    exact sourceAt_erasure seed request rich pc hp
  exact hCurrent.trans ((congrArg (materializedResult seed capacity) hSubtype).trans
    hPrevious.symm)

def runAtWithTrace (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace :=
  let drawn := nativeAtWithTrace seed request rich pc hp
  (drawn.1,wrap 24 2 [drawn.2])

def runAtWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := nativeAtWithTraceAndWork seed request rich pc hp
  ((drawn.1.1,wrap 24 2 [drawn.1.2]),drawn.2)

def runAtWithTraceAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := nativeAtWithTraceAndBuildWork seed request rich pc hp
  ((drawn.1.1,wrap 24 2 [drawn.1.2]),drawn.2)

theorem runAtWithTraceAndBuildWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndBuildWork seed request rich pc hp).1 =
      (runAtWithTraceAndWork seed request rich pc hp).1 := by
  unfold runAtWithTraceAndBuildWork runAtWithTraceAndWork
  dsimp only
  rw [nativeAtWithTraceAndBuildWork_erases]

theorem runAtWithTraceAndBuildWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (runAtWithTraceAndBuildWork seed request rich pc hp).2 =
      (runAtWithTraceAndWork seed request rich pc hp).2+
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2 :=
  nativeAtWithTraceAndBuildWork_charge seed request rich pc hp

theorem runAtWithTraceAndBuildWork_bound (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndBuildWork seed request rich pc hp).2 ≤
      (runAtWithTraceAndWork seed request rich pc hp).2+
        preparationAllowance request :=
  nativeAtWithTraceAndBuildWork_bound seed request rich pc hp

theorem runAtWithTraceAndWork_le_buildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndWork seed request rich pc hp).2 ≤
      (runAtWithTraceAndBuildWork seed request rich pc hp).2 :=
  nativeAtWithTraceAndWork_le_buildWork seed request rich pc hp

theorem runAtWithTraceAndWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndWork seed request rich pc hp).1 =
      runAtWithTrace seed request rich pc hp := by
  unfold runAtWithTraceAndWork runAtWithTrace
  dsimp only
  rw [nativeAtWithTraceAndWork_erases]

theorem runAtWithTraceAndWork_le_native (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTraceAndWork seed request rich pc hp).2 ≤
      (BinaryPRGHeapRequestLifetime.runAtWithTraceAndWork seed
        request.logical.request rich pc hp).2 := by
  exact nativeAtWithTraceAndWork_le_native seed request rich pc hp

theorem runAt_erasure (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runAtWithTrace seed request rich pc hp).1 =
      (BinaryPRGHeapRequestLifetime.runAt seed request.logical.request rich pc hp).1 := by
  rw [BinaryPRGHeapRequestLifetime.runAt_selected]
  unfold runAtWithTrace
  rw [nativeAt_erasure]

def runWithTrace (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace :=
  let drawn := runAtWithTrace seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  (drawn.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2) [drawn.2])

def runWithTraceAndWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runAtWithTraceAndWork seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  ((drawn.1.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2) [drawn.1.2]),
    drawn.2)

def runWithTraceAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runAtWithTraceAndBuildWork seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  ((drawn.1.1,wrapList seed.cap.bits.length 16 (seed.cap.bits.length+2) [drawn.1.2]),
    drawn.2)

theorem runWithTraceAndBuildWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndBuildWork seed request rich).1 =
      (runWithTraceAndWork seed request rich).1 := by
  unfold runWithTraceAndBuildWork runWithTraceAndWork
  dsimp only
  rw [runAtWithTraceAndBuildWork_erases]

theorem runWithTraceAndBuildWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (runWithTraceAndBuildWork seed request rich).2 =
      (runWithTraceAndWork seed request rich).2+
        (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
          words.1 (if rich then words.1 else words.2)).2 :=
  runAtWithTraceAndBuildWork_charge seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)

theorem runWithTraceAndBuildWork_bound (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndBuildWork seed request rich).2 ≤
      (runWithTraceAndWork seed request rich).2+
        preparationAllowance request :=
  runAtWithTraceAndBuildWork_bound seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)

theorem runWithTraceAndWork_le_buildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndWork seed request rich).2 ≤
      (runWithTraceAndBuildWork seed request rich).2 :=
  runAtWithTraceAndWork_le_buildWork seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)

theorem runWithTraceAndWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndWork seed request rich).1 =
      runWithTrace seed request rich := by
  unfold runWithTraceAndWork runWithTrace
  dsimp only
  rw [runAtWithTraceAndWork_erases]

/-- Selected request work with a conservative allowance for the same two
physical numerical-store lookup routes used by its initializer. The extra
term reads only store and index-width lengths, not the stores' contents. -/
def runWithTraceAndLookupWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runWithTraceAndWork seed request rich
  (drawn.1,drawn.2+
    BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request)

theorem runWithTraceAndLookupWork_erases (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndLookupWork seed request rich).1 =
      runWithTrace seed request rich := by
  exact runWithTraceAndWork_erases seed request rich

theorem runWithTraceAndLookupWork_charge (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndLookupWork seed request rich).2 =
      (runWithTraceAndWork seed request rich).2+
        BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request := rfl

theorem runWithTraceAndLookupWork_covers_native_lookup
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndWork seed request rich).2+
      BinaryPhysicalNumericalReadbackLifetime.pairNativeLookupWork request ≤
        (runWithTraceAndLookupWork seed request rich).2 := by
  rw [runWithTraceAndLookupWork_charge]
  exact Nat.add_le_add_left
    (BinaryPhysicalNumericalReadbackLifetime.pairNativeLookupWork_le_allowance request) _

/-- Selected request work with a physical-store-derived preparation allowance.
The extra arithmetic reads tape lengths; the already selected initializer
still builds each tree exactly once. -/
def runWithTraceAndPreparationWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runWithTraceAndLookupWork seed request rich
  (drawn.1,drawn.2+preparationAllowance request)

/-- One-pass physical-build route with the returned-heap builder work carried
through the resource call, plus the conservative preparation allowance. -/
def runWithTraceAndPreparationAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runWithTraceAndBuildWork seed request rich
  (drawn.1,drawn.2+
    BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
    preparationAllowance request)

theorem runWithTraceAndPreparationAndBuildWork_erases
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationAndBuildWork seed request rich).1 =
      runWithTrace seed request rich := by
  unfold runWithTraceAndPreparationAndBuildWork
  dsimp only
  rw [runWithTraceAndBuildWork_erases,runWithTraceAndWork_erases]

theorem runWithTraceAndPreparationAndBuildWork_charge
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationAndBuildWork seed request rich).2 =
      (runWithTraceAndBuildWork seed request rich).2+
        BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
        preparationAllowance request := rfl

theorem runWithTraceAndPreparationAndBuildWork_bound
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationAndBuildWork seed request rich).2 ≤
      (runWithTraceAndPreparationWork seed request rich).2+
        preparationAllowance request := by
  have hBuild := runWithTraceAndBuildWork_bound seed request rich
  rw [runWithTraceAndPreparationAndBuildWork_charge]
  unfold runWithTraceAndPreparationWork runWithTraceAndLookupWork
  dsimp only
  omega

theorem runWithTraceAndPreparationWork_le_buildWork
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationWork seed request rich).2 ≤
      (runWithTraceAndPreparationAndBuildWork seed request rich).2 := by
  have hBase := runWithTraceAndWork_le_buildWork seed request rich
  rw [runWithTraceAndPreparationAndBuildWork_charge]
  unfold runWithTraceAndPreparationWork runWithTraceAndLookupWork
  dsimp only
  omega

theorem runWithTraceAndPreparationWork_erases
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationWork seed request rich).1 =
      runWithTrace seed request rich := by
  exact runWithTraceAndLookupWork_erases seed request rich

theorem runWithTraceAndPreparationWork_charge
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndPreparationWork seed request rich).2 =
      (runWithTraceAndLookupWork seed request rich).2+
        preparationAllowance request := rfl

theorem runWithTraceAndPreparationWork_covers_native_initial
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPRGHeapResourceSource.initialWithWork
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
          (runWithTraceAndPreparationWork seed request rich).2 := by
  rw [runWithTraceAndPreparationWork_charge]
  exact Nat.add_le_add_left
    (native_initial_work_le_preparationAllowance request rich) _

/-- The same selected work field also covers the two builds' allowance
computed from the heaps returned by physical readback. -/
theorem runWithTraceAndPreparationWork_covers_physical_builds
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 ≤
          (runWithTraceAndPreparationWork seed request rich).2 := by
  rw [runWithTraceAndPreparationWork_charge]
  exact Nat.add_le_add_left
    (BinaryPhysicalHeapInitialLifetime.request_readback_build_work_le_preparationBound
      request rich) _

theorem runWithTraceAndPreparationAndBuildWork_covers_native_initial
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPRGHeapResourceSource.initialWithWork
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
          (runWithTraceAndPreparationAndBuildWork seed request rich).2 := by
  exact (runWithTraceAndPreparationWork_covers_native_initial seed request rich).trans
    (runWithTraceAndPreparationWork_le_buildWork seed request rich)

theorem runWithTraceAndPreparationAndBuildWork_covers_physical_builds
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 ≤
          (runWithTraceAndPreparationAndBuildWork seed request rich).2 := by
  exact (runWithTraceAndPreparationWork_covers_physical_builds seed request rich).trans
    (runWithTraceAndPreparationWork_le_buildWork seed request rich)

/-- The selected one-pass charge retains the returned-heap builder allowance
and pays only for count, enumeration, and scan outside those builds. -/
def runWithTraceAndResidualAndBuildWork (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (BinaryPRGWordControllerResource.Result seed
      (BinaryPRGResourceWork.resourceInput request.logical.request rich).length × Trace) × ℕ :=
  let drawn := runWithTraceAndBuildWork seed request rich
  (drawn.1,drawn.2+
    BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
    preparationResidualAllowance request)

theorem runWithTraceAndResidualAndBuildWork_erases
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndResidualAndBuildWork seed request rich).1 =
      runWithTrace seed request rich := by
  unfold runWithTraceAndResidualAndBuildWork
  dsimp only
  rw [runWithTraceAndBuildWork_erases,runWithTraceAndWork_erases]

theorem runWithTraceAndResidualAndBuildWork_charge
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndResidualAndBuildWork seed request rich).2 =
      (runWithTraceAndBuildWork seed request rich).2+
        BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
        preparationResidualAllowance request := rfl

theorem runWithTraceAndResidualAndBuildWork_le_preparationWork
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (runWithTraceAndResidualAndBuildWork seed request rich).2 ≤
      (runWithTraceAndPreparationWork seed request rich).2 := by
  have hBuild := runWithTraceAndBuildWork_charge seed request rich
  have hCombined := readback_build_plus_residual_le_preparationAllowance request rich
  rw [runWithTraceAndResidualAndBuildWork_charge]
  unfold runWithTraceAndPreparationWork runWithTraceAndLookupWork
  dsimp only
  omega

theorem runWithTraceAndResidualAndBuildWork_covers_native_initial
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPRGHeapResourceSource.initialWithWork
        selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
          (runWithTraceAndResidualAndBuildWork seed request rich).2 := by
  have hNative := native_initial_work_le_readback_build_plus_residual request rich
  have hBuild := runWithTraceAndBuildWork_charge seed request rich
  rw [runWithTraceAndResidualAndBuildWork_charge,
    runWithTraceAndLookupWork_charge]
  omega

theorem runWithTraceAndResidualAndBuildWork_covers_physical_builds
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let readback := BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork request
    let words := readback.1.1.getD ([],[])
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        words.1 (if rich then words.1 else words.2)).2 ≤
          (runWithTraceAndResidualAndBuildWork seed request rich).2 := by
  have hBuild := runWithTraceAndBuildWork_charge seed request rich
  rw [runWithTraceAndResidualAndBuildWork_charge,
    runWithTraceAndLookupWork_charge]
  omega

theorem runWithTraceAndResidualAndBuildWork_covers_native_builder_allocated
    (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    let ruler := BinaryCarryCounter.count selected.length.data.toList []
    (runWithTraceAndLookupWork seed request rich).2+
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero ruler selected.length.data.toList).2.allocatedBits +
      (BinaryPRGHeapStoredTree.prepareRulerWithWork
        BinaryRationalOpcode.zero ruler selected.resource.data.toList).2.allocatedBits ≤
        (runWithTraceAndResidualAndBuildWork seed request rich).2 := by
  have hAllocated :=
    BinaryPhysicalHeapInitialLifetime.request_readback_build_work_covers_native_allocated
      request rich
  have hBuild := runWithTraceAndBuildWork_charge seed request rich
  rw [runWithTraceAndResidualAndBuildWork_charge,
    runWithTraceAndLookupWork_charge]
  omega

theorem runWithTraceAndWork_le_native (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTraceAndWork seed request rich).2 ≤
      (BinaryPRGHeapRequestLifetime.runWithTraceAndWork seed
        request.logical.request rich).2 := by
  exact runAtWithTraceAndWork_le_native seed request rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)

theorem uniform_runWithTraceAndWork_bound : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store)
      (request : Request n) (rich : Bool),
      (runWithTraceAndWork seed request rich).2 ≤
        C * (n + request.logical.request.source.originalInputWordWidth +
          seed.width + seed.cap.value + 1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryPRGHeapResourceRequest.uniform_request_work_bound
  refine ⟨C,d,?_⟩
  intro n seed request rich
  have hNative := runWithTraceAndWork_le_native seed request rich
  rw [BinaryPRGHeapRequestLifetime.runWithTraceAndWork_charge] at hNative
  exact hNative.trans (hBound seed request.logical.request rich)

theorem run_erasure (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) :
    (runWithTrace seed request rich).1 =
      (BinaryPRGHeapRequestLifetime.run seed request.logical.request rich).1 := by
  rw [BinaryPRGHeapRequestLifetime.run_selected]
  unfold runWithTrace
  rw [runAt_erasure]

theorem sourceAt_trace (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTrace seed request rich pc hp).2 =
      wrap 32 2
        [(BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTrace request rich).2,
          (BinaryPRGHeapLoopLifetime.runWithTrace seed
            (BinaryPRGHeapInitialLifetime.initialWithTrace
              (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
              (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
              (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
              (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).1.1
            (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
              (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
              (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
            (BinaryPRGHeapInitialLifetime.initialWithTrace
              (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
              (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
              (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
              (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).1.2
            pc hp).2] := by
  unfold sourceAtWithTrace sourceAtWithTraceAndWork
  dsimp only
  have hPrepared := BinaryPhysicalHeapInitialLifetime.initialFromRequest_erasure request rich
  change (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTraceAndWork request rich).1.1 = _
    at hPrepared
  rw [hPrepared]
  rfl

theorem sourceAt_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I L : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I)
    (hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1)
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.2
      pc hp).2 ≤ L) :
    usage (sourceAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+I+L+76 := by
  rw [sourceAt_trace]
  have hPhysical := BinaryPhysicalHeapInitialLifetime.initialFromParsed_usage
    frame parsed hParsed rich I hInitial
  change usage (BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTrace
    parsed.1.2 rich).2 ≤ 2000000200*(frame.length+3)^7+I+38 at hPhysical
  have hw := wrap_usage 32 2
    [(BinaryPhysicalHeapInitialLifetime.initialFromRequestWithTrace parsed.1.2 rich).2,
      (BinaryPRGHeapLoopLifetime.runWithTrace seed
        (BinaryPRGHeapInitialLifetime.initialWithTrace
          (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
          (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
          (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
          (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.1
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
          (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
          (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1)
        (BinaryPRGHeapInitialLifetime.initialWithTrace
          (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
          (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
          (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
          (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.2
        pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  omega

theorem sourceAt_prefix (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I L borrowed steps : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I)
    (hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1)
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.2
      pc hp).2 ≤ L) :
    retainedHeap borrowed (sourceAtWithTrace seed parsed.1.2 rich pc hp).2 steps ≤
        borrowed+(2000000200*(frame.length+3)^7+I+L+76) ∧
      framePeak ((sourceAtWithTrace seed parsed.1.2 rich pc hp).2.take steps) ≤
        2000000200*(frame.length+3)^7+I+L+76 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (sourceAt_usage frame parsed hParsed seed rich pc hp I L hInitial hLoop)
    borrowed steps

theorem accepted_sourceAt_input_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let request := parsed.1.2.logical.request
    let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      request.source.normalizedInput.latticeDenominator
    usage (sourceAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+
        BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1 W
          (binaryWordWidth parsed.1.1)+
        BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W
          request.source.normalizedInput.latticeDenominator
          seed.width seed.cap.value+76 := by
  let request := parsed.1.2.logical.request
  let selected := BinaryPRGResourceWork.resourceInput request rich
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    request.source.normalizedInput.latticeDenominator
  let D := request.source.normalizedInput.latticeDenominator
  obtain ⟨hl,hr,hb,hrb⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage
    selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request rich).2.2 W hW
    (by intro j; exact (hcWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega))
    (by intro j; exact (hrWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega))
  have hLoopOld := BinaryPRGHeapLifetimePolynomial.original_array_loop_usage
    seed selected.length selected.resource
    (BinaryPRGResourceWork.resource_canonical request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request rich).2.2
    W D hW request.source.normalizedInput.latticeDenominator_pos
    (by intro j; exact (hcWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega))
    (by intro j; exact (hrWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega))
    hl hb hr hrb pc hp
  have hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request rich).2.2).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
        (BinaryPRGResourceWork.resource_canonical request rich).2.1)
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        (BinaryPRGResourceWork.resource_canonical request rich).2.1
        (BinaryPRGResourceWork.resource_canonical request rich).2.2).1.2
      pc hp).2 ≤
        BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
          seed.width seed.cap.value := by
    rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
    exact hLoopOld
  exact sourceAt_usage frame parsed hParsed seed rich pc hp _ _ hInitial hLoop

theorem accepted_sourceAt_input_prefix (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (borrowed steps : ℕ) :
    let request := parsed.1.2.logical.request
    let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      request.source.normalizedInput.latticeDenominator
    let bound := 2000000200*(frame.length+3)^7+
      BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1 W (binaryWordWidth parsed.1.1)+
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W
        request.source.normalizedInput.latticeDenominator seed.width seed.cap.value+76
    retainedHeap borrowed (sourceAtWithTrace seed parsed.1.2 rich pc hp).2 steps ≤
        borrowed+bound ∧
      framePeak ((sourceAtWithTrace seed parsed.1.2 rich pc hp).2.take steps) ≤ bound :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_sourceAt_input_usage frame parsed hParsed seed rich pc hp)
    borrowed steps

theorem nativeAt_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I L H : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I)
    (hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1)
      (BinaryPRGHeapInitialLifetime.initialWithTrace
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).1.2
      pc hp).2 ≤ L)
    (hHeap : ∀ state : BinaryPRGHeapResourceLoop.Finished
      (capStore (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
      parsed.1.1
      (count (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length),
      (sourceAtWithTrace seed parsed.1.2 rich pc hp).1.2.1 = some state →
        state.heap.tape.length ≤ H) :
    usage (nativeAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+I+L+
        BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1 H
          (capStore (BinaryPRGResourceWork.resourceInput
            parsed.1.2.logical.request rich).length).width+120 := by
  let selected := BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich
  let drawn := sourceAtWithTrace seed parsed.1.2 rich pc hp
  have hSource := sourceAt_usage frame parsed hParsed seed rich pc hp I L
    hInitial hLoop
  unfold nativeAtWithTrace
  dsimp only
  cases hState : drawn.1.2.1 with
  | none =>
      have hw := wrap_usage 16 2 [drawn.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 16 2 [drawn.2]) ≤ _
      change usage drawn.2 ≤ _ at hSource
      omega
  | some state =>
      have ht := BinaryPRGHeapMaterializationLifetime.materializeWithTrace_usage
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1 (sourceAt_cap seed parsed.1.2 rich pc hp)
        state H (hHeap state hState)
      have hw := wrap_usage 24 2
        [drawn.2,(BinaryPRGHeapMaterializationLifetime.materializeWithTrace
          selected.length
          (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
          drawn.1.1 (sourceAt_cap seed parsed.1.2 rich pc hp) state).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [drawn.2,
        (BinaryPRGHeapMaterializationLifetime.materializeWithTrace
          selected.length
          (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
          drawn.1.1 (sourceAt_cap seed parsed.1.2 rich pc hp) state).2]) ≤ _
      change usage drawn.2 ≤ _ at hSource
      change usage (BinaryPRGHeapMaterializationLifetime.materializeWithTrace
        selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1 (sourceAt_cap seed parsed.1.2 rich pc hp) state).2 ≤
          BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1 H
            (capStore selected.length).width at ht
      have hEnvelope :
          BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1 H
              (capStore selected.length).width =
            BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1 H
              (capStore (BinaryPRGResourceWork.resourceInput
                parsed.1.2.logical.request rich).length).width := rfl
      rw [hEnvelope] at ht
      omega

theorem accepted_nativeAt_input_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let request := parsed.1.2.logical.request
    let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      request.source.normalizedInput.latticeDenominator
    usage (nativeAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+
        BinaryPRGHeapNativeLifetimeBound.envelope parsed.1.1 W
          request.source.normalizedInput.latticeDenominator
          seed.width seed.cap.value+100 := by
  let request := parsed.1.2.logical.request
  let selected := BinaryPRGResourceWork.resourceInput request rich
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    request.source.normalizedInput.latticeDenominator
  let D := request.source.normalizedInput.latticeDenominator
  let hC := (BinaryPRGResourceWork.resource_canonical request rich).2.1
  let hR := (BinaryPRGResourceWork.resource_canonical request rich).2.2
  obtain ⟨hl,hr,hb,hrb⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    intro j
    exact (hcWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    intro j
    exact (hrWidth j).trans (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
  have hInitial := BinaryPRGHeapInitialLifetimeBound.initialWithTrace_usage
    selected.length selected.resource hC hR W hW hCapacity hResource
  have hLoopOld := BinaryPRGHeapLifetimePolynomial.original_array_loop_usage
    seed selected.length selected.resource hC hR W D hW
    request.source.normalizedInput.latticeDenominator_pos
    hCapacity hResource hl hb hr hrb pc hp
  have hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length hC)
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        hC hR).1.2 pc hp).2 ≤
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
        seed.width seed.cap.value := by
    rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
    exact hLoopOld
  have hHeap : ∀ state : BinaryPRGHeapResourceLoop.Finished
      (capStore selected.length) parsed.1.1 (count selected.length),
      (sourceAtWithTrace seed parsed.1.2 rich pc hp).1.2.1 = some state →
        state.heap.tape.length ≤
          BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D := by
    intro state hSome
    apply BinaryPRGHeapNativeLifetimeBound.returned_heap seed
      selected.length selected.resource hC hR W D hW
      request.source.normalizedInput.latticeDenominator_pos
      hCapacity hResource hl hb hr hrb pc hp state
    rw [← sourceAt_erasure]
    exact hSome
  have hNative := nativeAt_usage frame parsed hParsed seed rich pc hp
    (BinaryPRGHeapInitialLifetimeBound.envelope parsed.1.1 W
      (binaryWordWidth parsed.1.1))
    (BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
      seed.width seed.cap.value)
    (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
    hInitial hLoop hHeap
  have hm := BinaryPRGHeapNativeLifetimeBound.materialization_depth_mono
    parsed.1.1 (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
    (BinaryPRGHeapResourceInputBounds.source_depth selected.length)
  change BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
      (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
      (capStore (BinaryPRGResourceWork.resourceInput
        parsed.1.2.logical.request rich).length).width ≤
    BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
      (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
      (binaryWordWidth parsed.1.1) at hm
  change usage (nativeAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
    2000000200*(frame.length+3)^7+
      BinaryPRGHeapNativeLifetimeBound.envelope parsed.1.1 W D
        seed.width seed.cap.value+100
  unfold BinaryPRGHeapNativeLifetimeBound.envelope
  omega

theorem accepted_runAt_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (runAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+
        BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
          seed.width seed.cap.value+100 := by
  have hNative := accepted_nativeAt_input_usage frame parsed hParsed seed rich pc hp
  have hw := wrap_usage 24 2 [(nativeAtWithTrace seed parsed.1.2 rich pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runAtWithTrace seed parsed.1.2 rich pc hp).2 ≤ _ at hw
  unfold BinaryPRGHeapRequestLifetime.envelope
  omega

theorem accepted_run_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runWithTrace seed parsed.1.2 rich).2 ≤
      2000000200*(frame.length+3)^7+
        BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
          seed.width seed.cap.value+2*seed.width+120 := by
  have hAt := accepted_runAt_usage frame parsed hParsed seed rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  have hw := wrapList_usage seed.cap.bits.length 16 (seed.cap.bits.length+2)
    [(runAtWithTrace seed parsed.1.2 rich
      (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,seed.cap.size] at hw
  unfold runWithTrace
  dsimp only
  simp only [seed.cap.size]
  omega

theorem accepted_run_prefix (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    let bound := 2000000200*(frame.length+3)^7+
      BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
        seed.width seed.cap.value+2*seed.width+120
    retainedHeap borrowed (runWithTrace seed parsed.1.2 rich).2 steps ≤
        borrowed+bound ∧
      framePeak ((runWithTrace seed parsed.1.2 rich).2.take steps) ≤ bound :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_run_usage frame parsed hParsed seed rich) borrowed steps

end Blotto.BinaryPhysicalHeapRequestLifetime

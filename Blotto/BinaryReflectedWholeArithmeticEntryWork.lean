import Blotto.BinaryReflectedPrimitiveArithmeticEntryWork

/-! The actual one-pass initializer and primitive resource entry sum join
native materialization, reflected preparation and complete post-resource draw.
Materialization/reference transport adds no raw/comparison entries. -/
namespace Blotto.BinaryReflectedWholeArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPRGHeapPackedStore (pack)
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {n : ℕ}

def initialArrays (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : Stored (capStore capacity).tree × Stored (resStore capacity resource).tree)
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) (builtTrace : Trace) : ℕ :=
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨built.1.ruler,built.1.size⟩
  have hCap : capWord=(capStore capacity).cap := by
    simp only [capWord,hBuilt,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let enumerated := BinaryHeapEnumerationWidthMeasured.allFromBits capWord
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) := hCap ▸ enumerated.1.1
  BinaryReflectedPrimitiveArithmeticEntryWork.scan built.1 (pack built.2) addresses

theorem initialArrays_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : Stored (capStore capacity).tree × Stored (resStore capacity resource).tree)
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) (builtTrace : Trace) :
    initialArrays capacity resource hC hR built hBuilt builtTrace ≤
      2*listCells (BinaryReflectedInitialFused.fromArrays capacity resource hC hR built hBuilt builtTrace).1.2 := by
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨built.1.ruler,built.1.size⟩
  have hCap : capWord=(capStore capacity).cap := by
    simp only [capWord,hBuilt,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let enumerated := BinaryHeapEnumerationWidthMeasured.allFromBits capWord
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) := hCap ▸ enumerated.1.1
  have hs := BinaryReflectedPrimitiveArithmeticEntryWork.scan_bound built.1 (pack built.2) addresses
  dsimp only [addresses,enumerated,capWord] at hs
  simp only [initialArrays,BinaryReflectedInitialFused.fromArrays,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def initial (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) : ℕ :=
  let built := BinaryReflectedInitialFused.arrays capacity resource
  have hBuilt : built.1.1=(BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1 :=
    congrArg Prod.fst (BinaryReflectedInitialFused.arrays_previous capacity resource)
  initialArrays capacity resource hC hR built.1.1 hBuilt built.1.2

theorem initial_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    initial capacity resource hC hR ≤ 2*listCells (BinaryReflectedInitialFused.initial capacity resource hC hR).1.2 := by
  exact initialArrays_bound capacity resource hC hR (BinaryReflectedInitialFused.arrays capacity resource).1.1
    (congrArg Prod.fst (BinaryReflectedInitialFused.arrays_previous capacity resource))
    (BinaryReflectedInitialFused.arrays capacity resource).1.2

def source (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let initialized := BinaryReflectedInitialFused.initial capacity resource hC hR
  initial capacity resource hC hR+BinaryReflectedPrimitiveArithmeticEntryWork.loop seed initialized.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) initialized.1.1.2.active initialized.1.1.2 pc hp

theorem source_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    source seed capacity resource hC hR pc hp ≤ 2*listCells (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.2 := by
  have hi := initial_bound capacity resource hC hR
  have hl := BinaryReflectedPrimitiveArithmeticEntryWork.run_bound seed
    (BinaryReflectedInitialFused.initial capacity resource hC hR).1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    (BinaryReflectedInitialFused.initial capacity resource hC hR).1.1.2 pc hp
  simp only [source,BinaryReflectedNativeFused.source,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem native_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    source seed capacity resource hC hR pc hp ≤ 2*listCells (BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).1.2 := by
  have hs := source_bound seed capacity resource hC hR pc hp
  simp only [BinaryReflectedNativeFused.native]
  split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def resourceDraw (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  source seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp

theorem resourceDraw_bound (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    resourceDraw seed prepared pc hp ≤ 2*listCells (BinaryReflectedResourceMeasured.draw seed prepared pc hp).1.2 := by
  have hn := native_bound seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp
  simp only [resourceDraw,BinaryReflectedResourceMeasured.draw,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def resource (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  BinaryReflectedPreparationArithmeticEntryWork.prepare input+
    resourceDraw seed (BinaryReflectedPreparationMeasured.prepare input hC).1.1 pc hp

theorem resource_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    resource seed input hC pc hp ≤ 2*listCells (BinaryReflectedResourceMeasured.run seed input hC pc hp).1.2 := by
  have hprep := BinaryReflectedPreparationArithmeticEntryWork.prepare_bound input hC
  have hd := resourceDraw_bound seed (BinaryReflectedPreparationMeasured.prepare input hC).1.1 pc hp
  simp only [resource,BinaryReflectedResourceMeasured.run_record,BinaryReflectedResourceMeasured.join,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def draw (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let reached := BinaryReflectedResourceMeasured.run seed input hC pc hp
  resource seed input hC pc hp+BinaryReflectedTerminalArithmeticEntryWork.afterResource seed input hC hAd
    reached.1.1.1 pc hp reached.1.1.2 (BinaryReflectedResourceMeasured.run_resource seed input hC pc hp) K outer scalar

theorem draw_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    draw seed input hC hAd K outer scalar pc hp ≤ 2*listCells (BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).1.2 := by
  have hr := resource_bound seed input hC pc hp
  have ha := BinaryReflectedTerminalArithmeticEntryWork.afterResource_bound seed input hC hAd
    (BinaryReflectedResourceMeasured.run seed input hC pc hp).1.1.1 pc hp
    (BinaryReflectedResourceMeasured.run seed input hC pc hp).1.1.2 (BinaryReflectedResourceMeasured.run_resource seed input hC pc hp) K outer scalar
  simp only [draw,BinaryReflectedDrawMeasured.run_record,BinaryReflectedDrawMeasured.fromReached_record,BinaryReflectedDrawMeasured.join,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem draw_input_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    draw seed input hC hAd K outer scalar pc hp ≤ 2*BinaryReflectedDrawMeasured.envelope s K seed.width seed.cap.value := by
  have he := draw_bound seed input hC hAd K outer scalar pc hp
  have hu := (BinaryReflectedDrawMeasured.run_bounds seed input source hC hR hCase hAd s hs hH K outer scalar pc hp).2
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hu
  omega

end Blotto.BinaryReflectedWholeArithmeticEntryWork

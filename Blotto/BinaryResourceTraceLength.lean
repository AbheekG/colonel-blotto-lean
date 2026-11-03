import Blotto.BinaryPhysicalHeapAllowanceRequest

/-! Event-count certificates for actual resource producers. These theorems
bound trace lists by the source work returned by the same execution. No count
observer is called by a producer. Native scalar/header/reference/allocator
prices and complete machine-model joins remain separate. -/
namespace Blotto.BinaryResourceTraceLength
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem under_length (depth : ℕ) (trace : Trace) : (under depth trace).length = trace.length := by
  simp only [under,List.length_map]

theorem combine_length (children : List Trace) :
    (combine children).length = (children.map List.length).sum := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp only [combine,List.length_append,under_length,List.map_cons,List.sum_cons,ih]

theorem wrap_length (slots frames : ℕ) (children : List Trace) :
    (wrap slots frames children).length = 2+(children.map List.length).sum := by
  simp only [wrap,List.length_append,combine_length,List.length_cons,List.length_nil]

theorem wrapList_length (cells slots frames : ℕ) (children : List Trace) :
    (wrapList cells slots frames children).length = 3+(children.map List.length).sum := by
  simp only [wrapList,List.length_append,wrap_length,List.length_cons,List.length_nil]
  omega

theorem scan_length (bits : List Bool) :
    (BooleanFreshSeedMeasured.scan bits).1.2.length ≤ 2*(bits.length+1) :=
  BooleanFreshSeedMeasured.scanAt_trace_length bits 0

theorem difference_length (first second : List Bool) :
    (BinarySignedMeasured.differenceTraced first second).1.2.length = 3 := rfl

theorem gcd_loop_length (ruler first second : List Bool) :
    (BinarySteinGCDMeasured.loop ruler first second).1.2.length ≤
      (BinarySteinGCDMeasured.loop ruler first second).2 := by
  induction ruler generalizing first second with
  | nil =>
      have h := scan_length first
      simp only [BinarySteinGCDMeasured.loop,List.length_append,under_length,List.length_cons,List.length_nil]
      omega
  | cons marker ruler ih =>
      have hFirst := scan_length first
      have hSecond := scan_length second
      unfold BinarySteinGCDMeasured.loop
      dsimp only
      split
      · split
        · cases first with
          | nil =>
              simp only [List.length_append,under_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
              omega
          | cons a first => cases second with
            | nil =>
                cases a <;> simp only [List.length_append,under_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢ <;> omega
            | cons b second =>
                cases a <;> cases b <;> dsimp only
                · have hl := ih first second
                  simp only [List.length_append,under_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
                  omega
                · have hl := ih first (true::second)
                  simp only [List.length_append,under_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
                  omega
                · have hl := ih (true::first) second
                  simp only [List.length_append,under_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
                  omega
                · split
                  · have hl := ih (true::first) (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail
                    simp only [List.length_append,under_length,difference_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
                    omega
                  · have hl := ih (BinarySignedMeasured.differenceTraced (true::first) (true::second)).1.1.bits.tail (true::second)
                    simp only [List.length_append,under_length,difference_length,List.length_cons,List.length_nil] at hFirst hSecond ⊢
                    omega
        · simp only [List.length_append,under_length,List.length_cons,List.length_nil]
          omega
      · simp only [List.length_append,under_length,List.length_cons,List.length_nil]
        omega

theorem append_trace_length (first second : List Bool) :
    (BinaryPRGOutputLifetime.appendWithTrace first second).2.length = 2*first.length+1 := by
  induction first with
  | nil => rfl
  | cons bit rest ih =>
      simp only [BinaryPRGOutputLifetime.appendWithTrace,List.length_append,under_length,
        List.length_cons,List.length_nil,ih]
      omega

theorem trim_length (bits : List Bool) : (BinaryCanonicalTrimMeasured.traced bits).1.2.length = 3 := rfl

theorem gcd_length (first second : List Bool) :
    (BinarySteinGCDMeasured.gcd first second).1.2.length ≤ 3*(BinarySteinGCDMeasured.gcd first second).2 := by
  have h := gcd_loop_length (BinaryPRGOutputLifetime.appendWithTrace first second).1 first second
  simp only [BinarySteinGCDMeasured.gcd,List.length_append,under_length,append_trace_length,
    trim_length,List.length_cons,List.length_nil]
  omega

theorem division_length (first second : List Bool) :
    (BinaryDivisionStorageMeasured.tracedMeasured first second).1.1.2.length = 3 := rfl

theorem raw_length (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryRationalRawMeasured.traced op first second).1.2.length = 3 := rfl

theorem normalize_length (word : SignedWord) :
    (BinaryQuadraticMeasured.normalizeMeasured word).1.1.2.length ≤
      3*(BinaryQuadraticMeasured.normalizeMeasured word).1.2 := by
  have hg := gcd_length word.numerator word.denominator
  have hs := scan_length (BinaryDivisionStorageMeasured.tracedMeasured word.numerator
    (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1).1.1.1.1
  -- The sign scan is charged by the original numerator width, so use the
  -- existing division length certificate rather than introducing a new width.
  have hn : (BinaryDivisionStorageMeasured.tracedMeasured word.numerator
      (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1).1.1.1.1.length = word.numerator.length := by
    rw [BinaryDivisionStorageMeasured.tracedMeasured_compat,BinaryDivisionStorageMeasured.traced_data,
      BinaryLongDivision.divideWithWork_refines]
    exact (BinaryLongDivision.divide_lengths word.numerator
      (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1).1
  rw [hn] at hs
  simp only [BinaryQuadraticMeasured.normalizeMeasured,List.length_append,under_length,
    division_length,List.length_cons,List.length_nil]
  omega

theorem normalize_work_lower (word : SignedWord) : 5 ≤ (BinaryQuadraticMeasured.normalizeMeasured word).1.2 := by
  simp only [BinaryQuadraticMeasured.normalizeMeasured]
  omega

theorem canonicalize_work_lower (word : SignedWord) : 5 ≤ (BinaryQuadraticMeasured.canonicalizeMeasured word).1.2 := by
  have h := normalize_work_lower word
  simp only [BinaryQuadraticMeasured.canonicalizeMeasured]
  omega

theorem canonicalize_length (word : SignedWord) :
    (BinaryQuadraticMeasured.canonicalizeMeasured word).1.1.2.length ≤
      5*(BinaryQuadraticMeasured.canonicalizeMeasured word).1.2 := by
  have h := normalize_length word
  have hl := normalize_work_lower word
  simp only [BinaryQuadraticMeasured.canonicalizeMeasured,List.length_append,under_length,
    trim_length,List.length_cons,List.length_nil]
  omega

theorem opcode_length (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryQuadraticMeasured.applyMeasured op first second).1.1.2.length ≤
      6*(BinaryQuadraticMeasured.applyMeasured op first second).1.2 := by
  have h := canonicalize_length (BinaryRationalRawMeasured.traced op first second).1.1
  have hl := canonicalize_work_lower (BinaryRationalRawMeasured.traced op first second).1.1
  simp only [BinaryQuadraticMeasured.applyMeasured,List.length_append,under_length,
    raw_length,List.length_cons,List.length_nil]
  omega

theorem reverse_trace_length (bits acc : List Bool) :
    (reverseWithTrace bits acc).2.length = 2*bits.length+1 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih =>
      simp only [reverseWithTrace,List.length_append,under_length,List.length_cons,List.length_nil,ih]
      omega

theorem register_scan_length {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth) (address : List Bool) :
    (BinaryQuadraticResourcePairLifetime.scanTreeWithTrace tree address).2.length = 2*(depth+1) := by
  induction tree generalizing address with
  | leaf word => rfl
  | branch left right hl hr => cases address with
    | nil =>
        simp only [BinaryQuadraticResourcePairLifetime.scanTreeWithTrace,List.length_append,under_length,
          List.length_cons,List.length_nil,hl]
        omega
    | cons bit rest => cases bit <;> simp only [BinaryQuadraticResourcePairLifetime.scanTreeWithTrace,
        Bool.false_eq_true,ite_false,ite_true,List.length_append,under_length,List.length_cons,List.length_nil,hl,hr] <;> omega

theorem register_lookup_length {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth)
    (address : FixedBinaryWord depth) :
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace tree address).2.length = 4*depth+5 := by
  simp only [BinaryQuadraticResourcePairLifetime.lookupWithTrace,List.length_append,under_length,
    List.length_cons,List.length_nil,reverse_trace_length,register_scan_length,address.size]
  omega

theorem register_write_scan_length {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth)
    (address : List Bool) (word : SignedWord) :
    (BinaryQuadraticResourcePairLifetime.writeScanWithTrace tree address word).2.length = 2*(depth+1) := by
  induction tree generalizing address with
  | leaf old => rfl
  | branch left right hl hr => cases address with
    | nil =>
        simp only [BinaryQuadraticResourcePairLifetime.writeScanWithTrace,List.length_append,under_length,
          List.length_cons,List.length_nil,hl]
        omega
    | cons bit rest => cases bit <;> simp only [BinaryQuadraticResourcePairLifetime.writeScanWithTrace,
        Bool.false_eq_true,ite_false,ite_true,List.length_append,under_length,List.length_cons,List.length_nil,hl,hr] <;> omega

theorem register_write_length {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth)
    (address : FixedBinaryWord depth) (word : SignedWord) :
    (BinaryQuadraticResourcePairLifetime.writeWithTrace tree address word).2.length = 4*depth+5 := by
  simp only [BinaryQuadraticResourcePairLifetime.writeWithTrace,List.length_append,under_length,
    List.length_cons,List.length_nil,reverse_trace_length,register_write_scan_length,address.size]
  omega

theorem advance_length {w : ℕ} (word : FixedBinaryWord w) :
    (BinaryHeapEnumerationMeasured.advance word).1.2.length ≤ 3*(w+1)+2 := by
  have h := BinaryWordCoinPrimitivesMeasured.incrementBitsAt_trace_length word.bits 0
  rw [word.size] at h
  simp only [BinaryHeapEnumerationMeasured.advance,BinaryWordCoinPrimitivesMeasured.incrementBits,
    List.length_append,under_length,List.length_cons,List.length_nil]
  omega

theorem register_execute_length (instruction : BinaryPRGWordControllerPairRegisters.Instruction)
    (registers : BinaryPRGWordControllerPairRegisters.Registers) :
    (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1.2.length ≤
      6*(BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.2 := by
  have ha := advance_length registers.cursor
  have hw := opcode_length instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1
  simp only [BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapPairRegistersMeasured.executeMeasured,List.length_append,under_length,
    register_lookup_length,register_write_length,List.length_cons,List.length_nil]
  omega

theorem register_run_length (program : List BinaryPRGWordControllerPairRegisters.Instruction)
    (registers : BinaryPRGWordControllerPairRegisters.Registers) :
    (BinaryHeapPairRegistersMeasured.runMeasured program registers).1.1.2.length ≤
      6*(BinaryHeapPairRegistersMeasured.runMeasured program registers).1.2 := by
  induction program generalizing registers with
  | nil => simp [BinaryHeapPairRegistersMeasured.runMeasured]
  | cons instruction rest ih =>
      have hn := register_execute_length instruction registers
      have hl := ih (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1.1
      simp only [BinaryHeapPairRegistersMeasured.runMeasured,List.length_append,under_length,
        List.length_cons,List.length_nil]
      omega

theorem register_build_length (fallback : SignedWord) (ruler : List Bool) (seed : List SignedWord) :
    (BinaryQuadraticResourcePairLifetime.buildWithTrace fallback ruler seed).2.length =
      2*BinaryPRGWordControllerWordStore.buildVisits fallback ruler seed := by
  induction ruler generalizing seed with
  | nil => cases seed <;> rfl
  | cons marker ruler ih =>
      simp only [BinaryQuadraticResourcePairLifetime.buildWithTrace,List.length_append,under_length,
        List.length_cons,List.length_nil,ih,BinaryPRGWordControllerWordStore.buildVisits,
        BinaryQuadraticResourcePairLifetime.buildWithTrace_erases]
      omega

theorem register_initial_length (source : BinaryRationalPairProgram.Source) :
    (BinaryHeapPairRegistersMeasured.initial source).1.2.length = 65 := by
  have hv := BinaryPRGWordControllerWordStore.buildVisits_exact BinaryRationalOpcode.zero
    [false,false,false,false] (BinaryPRGWordControllerPairRegisters.initialWords source)
  norm_num only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reducePow] at hv
  simp only [BinaryHeapPairRegistersMeasured.initial,BinaryQuadraticResourcePairLifetime.initialWithTrace,
    List.length_append,under_length,List.length_cons,List.length_nil,register_build_length,hv]
  rfl

theorem register_pair_length (source : BinaryRationalPairProgram.Source) :
    (BinaryHeapPairRegistersMeasured.pairMeasured source).1.1.2.length ≤
      6*(BinaryHeapPairRegistersMeasured.pairMeasured source).1.2 := by
  have hl := register_run_length BinaryPRGWordControllerPairRegisters.code
    (BinaryHeapPairRegistersMeasured.initial source).1.1
  have hi := register_initial_length source
  have hw : 218 ≤ (BinaryHeapPairRegistersMeasured.initial source).2 := by
    simp only [BinaryHeapPairRegistersMeasured.initial]
    omega
  simp only [BinaryHeapPairRegistersMeasured.pairMeasured,List.length_append,under_length,
    List.length_cons,List.length_nil]
  omega

theorem register_outputs_length (source : BinaryRationalPairProgram.Source) :
    (BinaryHeapPairRegistersMeasured.outputsMeasured source).1.1.2.length ≤
      6*(BinaryHeapPairRegistersMeasured.outputsMeasured source).1.2 := by
  have h := register_pair_length source
  simp only [BinaryHeapPairRegistersMeasured.outputsMeasured,List.length_append,under_length,
    register_lookup_length,List.length_cons,List.length_nil]
  omega

theorem packed_read_length {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth)
    (address : FixedBinaryWord depth) :
    (BinaryHeapPackedReadMeasured.read data address).1.2.length ≤
      2*((BinaryHeapPackedReadMeasured.read data address).2+2) :=
  BinaryHeapPackedReadMeasured.readAt_trace_work data address 0

theorem comparison_length (first second : SignedWord) :
    (BinaryRationalComparisonMeasured.traced first second).1.2.length = 3 := rfl

theorem write_sequence_length {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (BinaryHeapWriteMeasured.execute data changes).1.2.length ≤
      8*((BinaryHeapWriteMeasured.execute data changes).2.1.work+1) := by
  have h := BinaryHeapWriteMeasured.executePlanAt_budget data changes 0
  simp only [BinaryHeapWriteMeasured.execute,BinaryHeapWriteMeasured.executeAtMeasured,
    BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero]
  omega

open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word)}

theorem pair_source_length (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he).1.2.length ≤
      3*(BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he).2 := by
  have ha := packed_read_length (BinaryPRGHeapPackedStore.pack limits) first.word
  have hb := packed_read_length (BinaryPRGHeapPackedStore.pack limits) second.word
  have hc := packed_read_length state.packed first.word
  have hd := packed_read_length state.packed second.word
  simp only [BinaryHeapPairSourceMeasured.source,wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem pair_length (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (BinaryHeapPairSourceMeasured.pairMeasured (hC := hC) limits state first second tail he).1.1.2.length ≤
      6*(BinaryHeapPairSourceMeasured.pairMeasured (hC := hC) limits state first second tail he).1.2 := by
  have hi := pair_source_length (hC := hC) limits state first second tail he
  have ho := register_outputs_length (BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he).1.1
  simp only [BinaryHeapPairSourceMeasured.pairMeasured,wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem fractional_length (limits : Stored capacity.tree) (bids : BinaryPRGHeapPackedStore.Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (BinaryHeapScanMeasured.fractional limits bids address).1.2.length ≤
      3*(BinaryHeapScanMeasured.fractional limits bids address).2.2 := by
  have hb := packed_read_length bids address.word
  have hl := packed_read_length (BinaryPRGHeapPackedStore.pack limits) address.word
  simp only [BinaryHeapScanMeasured.fractional,wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    comparison_length]
  omega

theorem scan_addresses_length (limits : Stored capacity.tree) (bids : BinaryPRGHeapPackedStore.Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (BinaryHeapScanMeasured.scan limits bids addresses).1.2.length ≤
      3*(BinaryHeapScanMeasured.scan limits bids addresses).2.2 := by
  induction addresses with
  | nil => simp [BinaryHeapScanMeasured.scan,wrap_length]
  | cons address rest ih =>
      have ht := fractional_length limits bids address
      simp only [BinaryHeapScanMeasured.scan,wrapList_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega

theorem update_length (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (BinaryHeapUpdateMeasured.updateMeasured limits state first second tail chosen).1.1.2.length ≤
      8*(BinaryHeapUpdateMeasured.updateMeasured limits state first second tail chosen).1.2.1 := by
  let a := BinaryHeapPackedReadMeasured.read state.packed first.word
  let b := BinaryHeapPackedReadMeasured.read state.packed second.word
  let total := BinaryQuadraticMeasured.applyMeasured .add a.1.1 b.1.1
  let other := BinaryQuadraticMeasured.applyMeasured .sub total.1.1.1 chosen
  let next := BinaryHeapWriteMeasured.execute state.packed [(first.word,chosen),(second.word,other.1.1.1)]
  have ha := packed_read_length state.packed first.word
  have hb := packed_read_length state.packed second.word
  have ht := opcode_length .add a.1.1 b.1.1
  have ho := opcode_length .sub total.1.1.1 chosen
  have hw := write_sequence_length state.packed [(first.word,chosen),(second.word,other.1.1.1)]
  have hs := scan_addresses_length limits next.1.1 [first,second]
  simp only [BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapUpdateMeasured.updateMeasured_eq_reference,BinaryHeapUpdateMeasured.updateMeasuredReference,wrapList_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  dsimp only [a,b,total,other,next] at ht ho hw hs
  omega

theorem update_work_lower (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    12 ≤ (BinaryHeapUpdateMeasured.updateMeasured limits state first second tail chosen).1.2.1 := by
  simp only [BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapUpdateMeasured.updateMeasured_eq_reference,BinaryHeapUpdateMeasured.updateMeasuredReference]
  omega

theorem selection_length (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (BinaryHeapUpdateMeasured.selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.2.length ≤
      10*(BinaryHeapUpdateMeasured.selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.2.1 := by
  let chosen := if branch then outputs.upper else outputs.lower
  have h := update_length limits state first second tail chosen
  have hl := update_work_lower limits state first second tail chosen
  simp only [BinaryHeapUpdateMeasured.selectMeasured_eq_reference,BinaryHeapUpdateMeasured.selectMeasuredReference,wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  dsimp only [chosen] at h hl
  omega

theorem prepared_length (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he).data.trace.length ≤
      6*(BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he).data.work := by
  simpa only [BinaryHeapLoopPrimitiveMeasured.prepare] using pair_length (hC := hC) limits state first second tail he

theorem draw_length (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopPrimitiveMeasured.draw seed word pc hp).data.trace.length ≤
      2*(BinaryHeapLoopPrimitiveMeasured.draw seed word pc hp).data.work := by
  have h := BinaryWordCoinSourceMeasured.samplePlanAt_budget seed word pc hp 0
  simp only [BinaryHeapLoopPrimitiveMeasured.draw,BinaryWordCoinSourceMeasured.sampleTraceMeasured,
    BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero]
  omega

theorem selected_length (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (BinaryHeapLoopPrimitiveMeasured.select limits hC state first second tail he outputs hOutputs branch).data.trace.length ≤
      10*(BinaryHeapLoopPrimitiveMeasured.select limits hC state first second tail he outputs hOutputs branch).data.work := by
  simpa only [BinaryHeapLoopPrimitiveMeasured.select,BinaryHeapUpdateMeasured.selectMeasured] using
    selection_length (hC := hC) limits state first second tail he outputs hOutputs branch

set_option backward.isDefEq.respectTransparency true in
theorem resource_reference_length (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference seed limits hC fuel state pc hp).1.1.2.length ≤
      10*(BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference seed limits hC fuel state pc hp).1.2 := by
  induction fuel generalizing state pc with
  | nil => simp [BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference,wrap_length]
  | cons marker fuel ih =>
      unfold BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference
        BinaryHeapLoopPrimitiveMeasured.stepBody BinaryHeapLoopPrimitiveMeasured.afterCoin
      dsimp only
      split
      · rename_i first second tail he
        have hpw := prepared_length limits hC state first second tail he
        have hcw := draw_length seed
          (BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he).data.outputs.probability pc hp
        split
        · simp only [wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
          omega
        · rename_i branch hSome
          let prepared := BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he
          let coin := BinaryHeapLoopPrimitiveMeasured.draw seed prepared.data.outputs.probability pc hp
          let selected := BinaryHeapLoopPrimitiveMeasured.select limits hC state first second tail he
            prepared.data.outputs prepared.data.valid branch
          have hsw := selected_length limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded
          simp only [wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
          dsimp only [prepared,coin,selected] at hsw hl
          omega
      · simp [wrap_length]

theorem resource_length (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopPrimitiveMeasured.loop seed limits hC fuel state pc hp).1.2.length ≤
      10*(BinaryHeapLoopPrimitiveMeasured.loop seed limits hC fuel state pc hp).2 := by
  change (BinaryHeapLoopPrimitiveMeasured.loopMeasured seed limits hC fuel state pc hp).1.1.2.length ≤
    10*(BinaryHeapLoopPrimitiveMeasured.loopMeasured seed limits hC fuel state pc hp).1.2
  rw [BinaryHeapLoopPrimitiveMeasured.loopMeasured_eq_reference]
  exact resource_reference_length seed limits hC fuel state pc hp

theorem resource_run_length (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).1.2.length ≤
      10*(BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).2 :=
  resource_length seed limits hC state.active state pc hp

theorem resource_total (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,
      CanonicalWord (BinaryPRGWordControllerWordStore.lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).2+
      (BinaryHeapLoopPrimitiveMeasured.runMeasured seed limits hC state pc hp).2+
      (BinaryHeapLoopPrimitiveMeasured.runTraceMeasured seed limits hC state pc hp).2 ≤
        66*(BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).2+16*n+2 := by
  have h := BinaryHeapLoopPrimitiveMeasured.runTraceMeasured_total_dimension seed limits hC state pc hp
  have ht := resource_run_length seed limits hC state pc hp
  change (BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).2+
    (BinaryHeapLoopPrimitiveMeasured.runMeasured seed limits hC state pc hp).2+
    (BinaryHeapLoopPrimitiveMeasured.runTraceMeasured seed limits hC state pc hp).2 ≤
      16*(BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).2+
        5*(BinaryHeapLoopPrimitiveMeasured.run seed limits hC state pc hp).1.2.length+16*n+2 at h
  omega

theorem source_length (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).1.2.length ≤
      (BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+
        10*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+2 := by
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let prepared := BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich
  have hr := resource_run_length seed prepared.1.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1)
    prepared.1.1.1.2 pc hp
  simp only [BinaryHeapLoopPrimitiveMeasured.run] at hr
  simp only [BinaryPhysicalHeapAllowanceInitial.sourceAt,
    BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured_eq_reference,
    BinaryPhysicalHeapAllowanceInitial.sourceAtMeasuredReference,wrap_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  dsimp only [selected,prepared] at hr
  omega

theorem source_emission (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed request rich pc hp).2 ≤
      60*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
        5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20 := by
  have h := BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured_emission_dimension seed request rich pc hp
  have ht := source_length seed request rich pc hp
  omega

theorem source_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed request rich pc hp).2 ≤
        66*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
          5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20 := by
  have h := BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured_total_dimension seed request rich pc hp
  have ht := source_length seed request rich pc hp
  omega

theorem native_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.1+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.2 ≤
        66*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
          5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20 := by
  have h := BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured_total seed request rich pc hp
  have ht := source_length seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceRequest.nativeAt_source_work_le seed request rich pc hp
  omega

theorem source_emission_width (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    binaryWordWidth (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed request rich pc hp).2 ≤
      binaryWordWidth (60*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
        5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20) :=
  binaryWordWidth_mono (source_emission seed request rich pc hp)

end Blotto.BinaryResourceTraceLength

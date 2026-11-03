import Blotto.BinaryWordStoreLifetime
import Blotto.BinaryPRGWordControllerDataCoin

/-! Executed Boolean-PC coin lifetimes. Reached zero/equality/guard scans,
tree lookup/reversal, restoring coin step and fixed increment are concrete
producers; source padding supplies the actual stored-word coin. Exact data
erasure preserves outcomes and the complete Boolean PC, including exhaustion.
Every old reservation stays live; borrowed Store/seed/word payload is explicit.
-/
set_option autoImplicit false
namespace Blotto.BinaryWordCoinLifetime
open BinarySeedPreparationSpace BinarySeedLookupTree BinaryWordStoreLifetime
open BinaryRationalNormalization

def zeroWithTrace (bits : List Bool) : Bool×Trace :=
  let scanned := BinaryBooleanPrimitiveLifetime.scanWithTrace bits
  (!scanned.1,scanned.2)

@[simp] theorem zeroWithTrace_erases (bits : List Bool) :
    (zeroWithTrace bits).1=bits.all (fun b => !b) := by
  simp only [zeroWithTrace,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · change (!BinaryEuclideanGCD.nonzero rest)=rest.all (fun b => !b)
        exact ih
      · rfl

theorem zeroWithTrace_bounds (bits : List Bool) :
    listCells (zeroWithTrace bits).2+arraySlots (zeroWithTrace bits).2≤4*(bits.length+1) ∧
    framePeak (zeroWithTrace bits).2≤bits.length+1 :=
  BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds bits

def sameWithTrace : List Bool → List Bool → Bool×Trace
  | [],[] => (true,[.frames 1,.arrayAllocation 4])
  | a::rest,b::tail =>
      if a=b then
        let later := sameWithTrace rest tail
        (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)
      else (false,[.frames 1,.arrayAllocation 4])
  | _,_ => (false,[.frames 1,.arrayAllocation 4])

@[simp] theorem sameWithTrace_erases (first second : List Bool) :
    (sameWithTrace first second).1=FixedBinaryWord.sameScan first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail =>
        by_cases h : bit=other <;> simp [sameWithTrace,FixedBinaryWord.sameScan,ih,h]

theorem sameWithTrace_bounds (first second : List Bool) :
    listCells (sameWithTrace first second).2+arraySlots (sameWithTrace first second).2≤4*(first.length+1) ∧
    framePeak (sameWithTrace first second).2≤first.length+1 := by
  induction first generalizing second with
  | nil => cases second <;> simp [sameWithTrace,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      cases second with
      | nil => simp [sameWithTrace,listCells,arraySlots,framePeak]
      | cons other tail =>
          have h := ih tail
          have hf := framePeak_under 1 (sameWithTrace rest tail).2
          unfold sameWithTrace
          split
          · simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
              listCells_under,arraySlots_under,List.length_cons]
            exact ⟨by omega,by omega⟩
          · simp [listCells,arraySlots,framePeak]

def stepWithTrace {w : ℕ} (a b : FixedBinaryWord w) : (Bool×FixedBinaryWord w)×Trace :=
  let stepped := BinaryDivisionAllocation.stepWithAllocation false a.bits b.bits
  have hSize : stepped.1.2.length=w := by
    rw [BinaryDivisionAllocation.stepWithAllocation_state]
    exact (BinaryDivisionWord.step_length false a.bits b.bits (a.size.trans b.size.symm)).trans a.size
  ((stepped.1.1,⟨stepped.1.2,hSize⟩),[.frames (2*w+8),.arrayAllocation 8,
    .listAllocation (BinaryDivisionAllocation.stepStorage false a.bits b.bits)])

@[simp] theorem stepWithTrace_erases {w : ℕ} (a b : FixedBinaryWord w) :
    (stepWithTrace a b).1=a.coinStep b := by
  unfold stepWithTrace FixedBinaryWord.coinStep
  simp only [BinaryDivisionAllocation.stepWithAllocation_state]
  rfl

theorem stepWithTrace_bounds {w : ℕ} (a b : FixedBinaryWord w) :
    listCells (stepWithTrace a b).2+arraySlots (stepWithTrace a b).2≤50*(w+2)^2+8 ∧
    framePeak (stepWithTrace a b).2≤2*w+8 := by
  have hs := BinaryDivisionAllocation.stepStorage_bound false a.bits b.bits (a.size.trans b.size.symm)
  rw [b.size] at hs
  simp only [stepWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def earlyTrace {w : ℕ} (a : FixedBinaryWord w) : Trace :=
  [.frames 2,.arrayAllocation 16] ++ under 2 (zeroWithTrace a.bits).2
def equalTrace {w : ℕ} (a b : FixedBinaryWord w) : Trace :=
  earlyTrace a ++ under 2 (sameWithTrace a.bits b.bits).2
def guardTrace {w : ℕ} (store : Store) (a b : FixedBinaryWord w) (pc : FixedBinaryWord store.width) : Trace :=
  equalTrace a b ++ under 2 (ltWithTrace pc store.cap).2
def readTrace {w : ℕ} (store : Store) (a b : FixedBinaryWord w) (pc : FixedBinaryWord store.width) : Trace :=
  guardTrace store a b pc ++ under 2 (lookupWithTrace store pc).2 ++ under 2 (stepWithTrace a b).2 ++
    under 2 (incrementWithTrace pc).2

def localBound (w indexWidth : ℕ) : ℕ :=
  50*(w+2)^2+6*(indexWidth+1)^2+8*w+10*indexWidth+100
def localFrames (w indexWidth : ℕ) : ℕ := 2*w+2*indexWidth+12

theorem localTrace_bounds {w : ℕ} (store : Store) (a b : FixedBinaryWord w) (pc : FixedBinaryWord store.width) :
    (listCells (earlyTrace a)+arraySlots (earlyTrace a)≤localBound w store.width ∧
      framePeak (earlyTrace a)≤localFrames w store.width) ∧
    (listCells (equalTrace a b)+arraySlots (equalTrace a b)≤localBound w store.width ∧
      framePeak (equalTrace a b)≤localFrames w store.width) ∧
    (listCells (guardTrace store a b pc)+arraySlots (guardTrace store a b pc)≤localBound w store.width ∧
      framePeak (guardTrace store a b pc)≤localFrames w store.width) ∧
    (listCells (readTrace store a b pc)+arraySlots (readTrace store a b pc)≤localBound w store.width ∧
      framePeak (readTrace store a b pc)≤localFrames w store.width) := by
  have hz := zeroWithTrace_bounds a.bits
  have he := sameWithTrace_bounds a.bits b.bits
  rw [a.size] at hz he
  have hg := ltWithTrace_bounds pc store.cap
  have hl := lookupWithTrace_bounds store pc
  have hs := stepWithTrace_bounds a b
  have hi := incrementWithTrace_bounds pc
  have hzf := framePeak_under 2 (zeroWithTrace a.bits).2
  have hef := framePeak_under 2 (sameWithTrace a.bits b.bits).2
  have hgf := framePeak_under 2 (ltWithTrace pc store.cap).2
  have hlf := framePeak_under 2 (lookupWithTrace store pc).2
  have hsf := framePeak_under 2 (stepWithTrace a b).2
  have hif := framePeak_under 2 (incrementWithTrace pc).2
  unfold localBound localFrames
  simp only [earlyTrace,equalTrace,guardTrace,readTrace,listCells_append,arraySlots_append,framePeak_append,
    listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

def runWithTrace {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value≤store.cap.value) :
    (Option Bool×FixedBinaryWord store.width)×Trace :=
  let zero := zeroWithTrace a.bits
  let first := earlyTrace a
  if zero.1 then ((some false,pc),first) else
    let same := sameWithTrace a.bits b.bits
    let second := equalTrace a b
    if same.1 then ((some true,pc),second) else
      let guard := ltWithTrace pc store.cap
      let third := guardTrace store a b pc
      if hRead : guard.1=true then
        let read := lookupWithTrace store pc
        let next := stepWithTrace a b
        let advanced := incrementWithTrace pc
        have hpNext : advanced.1.1.value≤store.cap.value := by
          rw [incrementWithTrace_erases]
          exact BinaryWordIndexCoinController.advance_bound store pc
            (by simpa only [guard,ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
        let localTrace := readTrace store a b pc
        if read.1=next.1.1 then
          let later := runWithTrace store next.1.2 b advanced.1.1 hpNext
          (later.1,localTrace ++ under 1 later.2)
        else ((some (!read.1),advanced.1.1),localTrace)
      else ((none,pc),third)
termination_by store.cap.value-pc.value
decreasing_by
  have hr : pc.value<store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [guard,ltWithTrace_erases] using hRead)
  have hn := BinaryWordIndexCoinController.advance_value store pc
    (by simpa only [guard,ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
  change (BinaryIndexWord.increment pc).1.value=pc.value+1 at hn
  rw [incrementWithTrace_erases]
  omega

set_option maxHeartbeats 2000000 in
theorem runWithTrace_bounds {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value≤store.cap.value) :
    listCells (runWithTrace store a b pc hp).2+arraySlots (runWithTrace store a b pc hp).2≤
      (store.cap.value-pc.value+1)*localBound width store.width ∧
    framePeak (runWithTrace store a b pc hp).2≤store.cap.value-pc.value+localFrames width store.width := by
  have hLocal := localTrace_bounds store a b pc
  have hScale := Nat.mul_le_mul_right (localBound width store.width) (show 1≤store.cap.value-pc.value+1 from by omega)
  unfold runWithTrace
  dsimp only
  split
  · exact ⟨hLocal.1.1.trans (by simpa only [Nat.one_mul] using hScale),hLocal.1.2.trans (by omega)⟩
  · split
    · exact ⟨hLocal.2.1.1.trans (by simpa only [Nat.one_mul] using hScale),hLocal.2.1.2.trans (by omega)⟩
    · split
      · rename_i hRead
        have hn := BinaryWordIndexCoinController.advance_value store pc
          (by simpa only [ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
        change (BinaryIndexWord.increment pc).1.value=pc.value+1 at hn
        have hr : pc.value<store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
          (by simpa only [ltWithTrace_erases] using hRead)
        split
        · have hpNext : (incrementWithTrace pc).1.1.value≤store.cap.value := by
            rw [incrementWithTrace_erases]
            exact BinaryWordIndexCoinController.advance_bound store pc
              (by simpa only [ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
          have hLater := runWithTrace_bounds store (stepWithTrace a b).1.2 b (incrementWithTrace pc).1.1 hpNext
          have hLaterFrames := framePeak_under 1 (runWithTrace store (stepWithTrace a b).1.2 b (incrementWithTrace pc).1.1 hpNext).2
          have hDiff : store.cap.value-(incrementWithTrace pc).1.1.value+1=store.cap.value-pc.value := by
            rw [incrementWithTrace_erases,hn]
            omega
          rw [hDiff] at hLater
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells_under,arraySlots_under]
          exact ⟨by nlinarith only [hLocal.2.2.2.1,hLater.1],by omega⟩
        · exact ⟨hLocal.2.2.2.1.trans (by simpa only [Nat.one_mul] using hScale),hLocal.2.2.2.2.trans (by omega)⟩
      · exact ⟨hLocal.2.2.1.1.trans (by simpa only [Nat.one_mul] using hScale),hLocal.2.2.1.2.trans (by omega)⟩
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (ltWithTrace pc store.cap).1=true := by assumption
  have hr : pc.value<store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [ltWithTrace_erases] using hRead')
  have hn := BinaryWordIndexCoinController.advance_value store pc
    (by simpa only [ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead')
  change (BinaryIndexWord.increment pc).1.value=pc.value+1 at hn
  rw [incrementWithTrace_erases]
  omega

theorem runWithTrace_erases {width : ℕ} (store : Store) (a b : FixedBinaryWord width)
    (pc : FixedBinaryWord store.width) (hp : pc.value≤store.cap.value) :
    (runWithTrace store a b pc hp).1=BinaryPRGWordControllerDataCoin.run store a b pc hp := by
  conv_lhs => unfold runWithTrace
  conv_rhs => unfold BinaryPRGWordControllerDataCoin.run
  dsimp only
  simp only [zeroWithTrace_erases,sameWithTrace_erases,ltWithTrace_erases,lookupWithTrace_erases,
    stepWithTrace_erases,incrementWithTrace_erases,FixedBinaryWord.isZero,FixedBinaryWord.same]
  split_ifs with hz he hRead hd <;> simp_all only [ite_true,ite_false,dite_true,dite_false]
  all_goals first
    | rfl
    | exact runWithTrace_erases store (a.coinStep b).2 b (BinaryIndexWord.increment pc).1
        (BinaryWordIndexCoinController.advance_bound store pc (by assumption))
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : BinaryIndexWord.lt pc store.cap=true := by assumption
  have hr := (BinaryIndexWord.lt_value pc store.cap).mp hRead'
  have hn := BinaryWordIndexCoinController.advance_value store pc hRead'
  change (BinaryIndexWord.increment pc).1.value=pc.value+1 at hn
  omega

def padWithTrace (W : ℕ) (bits : List Bool) : List Bool×Trace :=
  let zeros := BinaryPRGOutputLifetime.replicateWithTrace (W-bits.length) false
  let copied := BinaryPRGOutputLifetime.appendWithTrace bits zeros.1
  (copied.1,[.frames 2,.arrayAllocation 8] ++ under 2 zeros.2 ++ under 2 copied.2)

@[simp] theorem padWithTrace_erases (W : ℕ) (bits : List Bool) :
    (padWithTrace W bits).1=BinarySignedMagnitude.pad W bits := by
  simp only [padWithTrace,BinaryPRGOutputLifetime.appendWithTrace_state,BinaryPRGOutputLifetime.replicateWithTrace_state,
    BinarySignedMagnitude.pad]

theorem padWithTrace_bounds (W : ℕ) (bits : List Bool) (h : bits.length≤W) :
    listCells (padWithTrace W bits).2+arraySlots (padWithTrace W bits).2≤W+8 ∧
    framePeak (padWithTrace W bits).2≤W+3 := by
  have hz := BinaryPRGOutputLifetime.replicateWithTrace_frames (W-bits.length) false
  have hc := BinaryPRGOutputLifetime.appendWithTrace_frames bits
    (BinaryPRGOutputLifetime.replicateWithTrace (W-bits.length) false).1
  have hzf := framePeak_under 2 (BinaryPRGOutputLifetime.replicateWithTrace (W-bits.length) false).2
  have hcf := framePeak_under 2 (BinaryPRGOutputLifetime.appendWithTrace bits
    (BinaryPRGOutputLifetime.replicateWithTrace (W-bits.length) false).1).2
  simp only [padWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under,BinaryPRGOutputLifetime.replicateWithTrace_cells,BinaryPRGOutputLifetime.appendWithTrace_cells,
    BinaryPRGOutputLifetime.replicateWithTrace_arrays,BinaryPRGOutputLifetime.appendWithTrace_arrays]
  exact ⟨by omega,by omega⟩

def sampleWithTrace (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) : (Option Bool×FixedBinaryWord store.width)×Trace :=
  let W := width word
  let a := padWithTrace W word.numerator
  let b := padWithTrace W word.denominator
  have ha : a.1.length=W := by rw [padWithTrace_erases]; exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.length=W := by rw [padWithTrace_erases]; exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  let later := runWithTrace store ⟨a.1,ha⟩ ⟨b.1,hb⟩ pc hp
  (later.1,[.frames (W+8),.arrayAllocation 16] ++ under 2 a.2 ++ under 2 b.2 ++ under 2 later.2)

@[simp] theorem sampleWithTrace_erases (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) :
    (sampleWithTrace store word pc hp).1=BinaryPRGWordControllerDataCoin.sample store word pc hp := by
  unfold sampleWithTrace BinaryPRGWordControllerDataCoin.sample BinaryStoredRationalCoin.fromStored
  simp only [runWithTrace_erases,padWithTrace_erases,width]

def sampleBound (W indexWidth remaining : ℕ) : ℕ :=
  2*W+32+(remaining+1)*localBound W indexWidth

theorem localBound_mono {a b c d : ℕ} (hW : a≤b) (hI : c≤d) : localBound a c≤localBound b d := by
  unfold localBound
  gcongr

theorem sampleWithTrace_bounds (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) (W : ℕ) (hW : width word≤W) :
    listCells (sampleWithTrace store word pc hp).2+arraySlots (sampleWithTrace store word pc hp).2≤
      sampleBound W store.width (store.cap.value-pc.value) ∧
    framePeak (sampleWithTrace store word pc hp).2≤store.cap.value-pc.value+2*W+2*store.width+24 := by
  let a := padWithTrace (width word) word.numerator
  let b := padWithTrace (width word) word.denominator
  have ha : a.1.length=width word := by
    dsimp only [a]; rw [padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length _ _ (Nat.le_max_left _ _)
  have hb : b.1.length=width word := by
    dsimp only [b]; rw [padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length _ _ (Nat.le_max_right _ _)
  have hA := padWithTrace_bounds (width word) word.numerator (Nat.le_max_left _ _)
  have hB := padWithTrace_bounds (width word) word.denominator (Nat.le_max_right _ _)
  have hRun := runWithTrace_bounds store (⟨a.1,ha⟩ : FixedBinaryWord (width word)) ⟨b.1,hb⟩ pc hp
  have hMono := Nat.mul_le_mul_left (store.cap.value-pc.value+1) (localBound_mono hW (le_refl store.width))
  have hAF := framePeak_under 2 a.2
  have hBF := framePeak_under 2 b.2
  have hRF := framePeak_under 2 (runWithTrace store (⟨a.1,ha⟩ : FixedBinaryWord (width word)) ⟨b.1,hb⟩ pc hp).2
  unfold sampleWithTrace sampleBound
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  dsimp only [a,b] at hRun hAF hBF hRF
  unfold localFrames at hRun
  exact ⟨by nlinarith only [hA.1,hB.1,hRun.1,hMono,hW],by omega⟩

theorem sampleWithTrace_position (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) :
    pc.value≤(sampleWithTrace store word pc hp).1.2.value ∧
    (sampleWithTrace store word pc hp).1.2.value≤store.cap.value := by
  rw [sampleWithTrace_erases]
  exact BinaryPRGWordControllerDataCoin.sample_position store word pc hp

theorem sample_all_prefix (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) (W : ℕ) (hW : width word≤W)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (storeCells store+pc.bits.length+BinaryRationalOpcodeAllocation.payload word+originalSeedCells+borrowedOtherCells)
      (sampleWithTrace store word pc hp).2 steps≤
      storeCells store+pc.bits.length+BinaryRationalOpcodeAllocation.payload word+originalSeedCells+borrowedOtherCells+
        sampleBound W store.width (store.cap.value-pc.value) :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (sampleWithTrace_bounds store word pc hp W hW).1

theorem sample_all_prefix_frames (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value≤store.cap.value) (W : ℕ) (hW : width word≤W) (steps : ℕ) :
    framePeak ((sampleWithTrace store word pc hp).2.take steps)≤store.cap.value-pc.value+2*W+2*store.width+24 :=
  (framePeak_take_le _ _).trans (sampleWithTrace_bounds store word pc hp W hW).2

end Blotto.BinaryWordCoinLifetime

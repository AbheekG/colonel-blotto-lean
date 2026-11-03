import Blotto.BinaryReflectedTerminalArithmeticEntryWork
import Blotto.BinaryReflectedNativeFused

/-! Entry accounting follows the selected reflected primitive register program,
actual packed reads/two writes/scan and actual fuel/coin/selection recursion.
It does not substitute the different main resource backend. -/
namespace Blotto.BinaryReflectedPrimitiveArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (quadratic_bound)
open BinaryPRGWordControllerPairRegisters
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency true

def registerExecute (instruction : Instruction) (registers : Registers) : ℕ :=
  BinaryArithmeticEntryWork.raw instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1

theorem registerExecute_bound (instruction : Instruction) (registers : Registers) :
    registerExecute instruction registers ≤ 2*listCells (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1.2 := by
  have h := quadratic_bound instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,registerExecute,BinaryHeapPairRegistersMeasured.executeMeasured,
    BinaryQuadraticMeasured.applyMeasured_compat,listCells_append,listCells_under,listCells]
  omega

def registerRun : List Instruction → Registers → ℕ
  | [],_ => 0
  | instruction::rest,registers =>
    let next := BinaryHeapPairRegistersMeasured.executeMeasured instruction registers
    registerExecute instruction registers+registerRun rest next.1.1.1

theorem registerRun_bound (program : List Instruction) (registers : Registers) :
    registerRun program registers ≤ 2*listCells (BinaryHeapPairRegistersMeasured.runMeasured program registers).1.1.2 := by
  induction program generalizing registers with
  | nil => simp only [registerRun,BinaryHeapPairRegistersMeasured.runMeasured,listCells]; omega
  | cons instruction rest ih =>
    have hn := registerExecute_bound instruction registers
    have hl := ih (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1.1
    simp only [registerRun,BinaryHeapPairRegistersMeasured.runMeasured,listCells_append,listCells_under,listCells]
    omega

def registerPair (source : BinaryRationalPairProgram.Source) : ℕ :=
  registerRun code (BinaryHeapPairRegistersMeasured.initial source).1.1

theorem registerPair_bound (source : BinaryRationalPairProgram.Source) :
    registerPair source ≤ 2*listCells (BinaryHeapPairRegistersMeasured.pairMeasured source).1.1.2 := by
  have h := registerRun_bound code (BinaryHeapPairRegistersMeasured.initial source).1.1
  simp only [registerPair,BinaryHeapPairRegistersMeasured.pairMeasured,listCells_append,listCells_under,listCells]
  omega

theorem registerOutputs_bound (source : BinaryRationalPairProgram.Source) :
    registerPair source ≤ 2*listCells (BinaryHeapPairRegistersMeasured.outputsMeasured source).1.1.2 := by
  have h := registerPair_bound source
  simp only [BinaryHeapPairRegistersMeasured.outputsMeasured,listCells_append,listCells_under,listCells]
  omega

theorem comparison_trace (a b : SignedWord) :
    BinaryArithmeticEntryWork.comparison a b ≤ 2*listCells (BinaryRationalComparisonMeasured.traced a b).1.2 := by
  simpa only [BinaryRationalComparisonMeasured.traced,listCells,Nat.add_zero] using
    BinaryArithmeticEntryWork.comparison_bound a b

variable {capacity : Store} {n : ℕ} {hCount : n=capacity.cap.value}

def fractional (limits : Stored capacity.tree) (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) : ℕ :=
  let bid := BinaryHeapPackedReadMeasured.read bids address.word
  let limit := BinaryHeapPackedReadMeasured.read (pack limits) address.word
  BinaryArithmeticEntryWork.comparison bid.1.1 BinaryRationalOpcode.zero+BinaryArithmeticEntryWork.comparison limit.1.1 bid.1.1

theorem fractional_bound (limits : Stored capacity.tree) (bids : Packed capacity.width) (address : Address capacity.width capacity.cap) :
    fractional limits bids address ≤ 2*listCells (BinaryHeapScanMeasured.fractional limits bids address).1.2 := by
  have hp := comparison_trace (BinaryHeapPackedReadMeasured.read bids address.word).1.1 BinaryRationalOpcode.zero
  have hb := comparison_trace (BinaryHeapPackedReadMeasured.read (pack limits) address.word).1.1
    (BinaryHeapPackedReadMeasured.read bids address.word).1.1
  simp only [fractional,BinaryHeapScanMeasured.fractional,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def scan (limits : Stored capacity.tree) (bids : Packed capacity.width) : List (Address capacity.width capacity.cap) → ℕ
  | [] => 0
  | address::rest => fractional limits bids address+scan limits bids rest

theorem scan_bound (limits : Stored capacity.tree) (bids : Packed capacity.width) (addresses : List (Address capacity.width capacity.cap)) :
    scan limits bids addresses ≤ 2*listCells (BinaryHeapScanMeasured.scan limits bids addresses).1.2 := by
  induction addresses with
  | nil => simp only [scan,BinaryHeapScanMeasured.scan,wrap,combine,listCells]; omega
  | cons address rest ih =>
    have h := fractional_bound limits bids address
    simp only [scan,BinaryHeapScanMeasured.scan,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
    omega

def update (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord) : ℕ :=
  let a := BinaryHeapPackedReadMeasured.read state.packed first.word
  let b := BinaryHeapPackedReadMeasured.read state.packed second.word
  let total := BinaryQuadraticMeasured.applyMeasured .add a.1.1 b.1.1
  let other := BinaryQuadraticMeasured.applyMeasured .sub total.1.1.1 chosen
  let written := BinaryHeapWriteMeasured.executeAtMeasured state.packed [(first.word,chosen),(second.word,other.1.1.1)] 0
  BinaryArithmeticEntryWork.raw .add a.1.1 b.1.1+BinaryArithmeticEntryWork.raw .sub total.1.1.1 chosen+
    scan limits written.1.1.1 [first,second]

theorem update_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord) :
    update limits state first second tail chosen ≤ 2*listCells (BinaryHeapUpdateMeasured.updateTraceMeasured limits state first second tail chosen).1.1.1.2 := by
  have ha := quadratic_bound .add (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
    (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1
  have hs := quadratic_bound .sub (BinaryQuadraticMeasured.applyMeasured .add
    (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1 (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1).1.1.1 chosen
  have hc := scan_bound limits
    (BinaryHeapWriteMeasured.executeAtMeasured state.packed [(first.word,chosen),(second.word,
      (BinaryQuadraticMeasured.applyMeasured .sub (BinaryQuadraticMeasured.applyMeasured .add
        (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
        (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1).1.1.1 chosen).1.1.1)] 0).1.1.1 [first,second]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,BinaryHeapUpdateMeasured.updateTraceMeasured,BinaryQuadraticMeasured.applyMeasured_compat,
    wrapList,wrap,combine,listCells_append,listCells_under,listCells] at hs hc ⊢
  omega

variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def prepared (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail) : ℕ :=
  registerPair (BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he).1.1

theorem prepared_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail) :
    prepared (hC := hC) limits state first second tail he ≤ 2*listCells (BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he).data.trace := by
  have h := registerOutputs_bound (BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he).1.1
  simp only [prepared,BinaryHeapLoopPrimitiveMeasured.prepare,BinaryHeapPairSourceMeasured.pairMeasured,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def selected (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs) (branch : Bool) : ℕ :=
  update limits state first second tail (if branch then outputs.upper else outputs.lower)

theorem selected_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs=(BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    selected limits state first second tail outputs branch ≤ 2*listCells
      (BinaryHeapLoopPrimitiveMeasured.select limits hC state first second tail he outputs hOutputs branch).data.trace := by
  have h := update_bound limits state first second tail (if branch then outputs.upper else outputs.lower)
  simp only [selected,BinaryHeapLoopPrimitiveMeasured.select,BinaryHeapUpdateMeasured.selectTraceMeasured,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def afterCoin (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) → pc.value ≤ seed.cap.value → ℕ)
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail)
    (pair : BinaryHeapLoopPrimitiveMeasured.Prepared canonical state first second tail he)
    (coin : BinaryHeapLoopPrimitiveMeasured.Draw seed) : ℕ :=
  prepared (hC := canonical) limits state first second tail he+
    match coin.data.outcome with
    | none => 0
    | some branch =>
      let choice := BinaryHeapLoopPrimitiveMeasured.select limits canonical state first second tail he pair.data.outputs pair.data.valid branch
      selected limits state first second tail pair.data.outputs branch+resume choice.data.value coin.data.cursor coin.data.bounded

def step (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) → pc.value ≤ seed.cap.value → ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  match he : state.active with
  | first::second::tail =>
    let pair := BinaryHeapLoopPrimitiveMeasured.prepare limits canonical state first second tail he
    let coin := BinaryHeapLoopPrimitiveMeasured.draw seed pair.data.outputs.probability pc hp
    afterCoin seed limits canonical resume state first second tail he pair coin
  | _ => 0

def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  match fuel with
  | [] => 0
  | _::rest => step seed limits canonical (fun state pc hp => loop seed limits canonical rest state pc hp) state pc hp
termination_by structural fuel

theorem loop_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loop seed limits canonical fuel state pc hp ≤ 2*listCells
      (BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference seed limits canonical fuel state pc hp).1.1.2 := by
  induction fuel generalizing state pc with
  | nil => simp only [loop,BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference,wrap,combine,listCells]; omega
  | cons marker rest ih =>
    rcases state with ⟨ruler,size,heap,root,valid,active,certified⟩
    cases active with
    | nil => simp only [loop,step,BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference,
        BinaryHeapLoopPrimitiveMeasured.stepBody,wrap,combine,listCells]; omega
    | cons first addresses => cases addresses with
      | nil => simp only [loop,step,BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference,
          BinaryHeapLoopPrimitiveMeasured.stepBody,wrap,combine,listCells]; omega
      | cons second tail =>
        let current : Finished capacity n hCount := ⟨ruler,size,heap,root,valid,first::second::tail,certified⟩
        let pair := BinaryHeapLoopPrimitiveMeasured.prepare limits canonical current first second tail rfl
        let coin := BinaryHeapLoopPrimitiveMeasured.draw seed pair.data.outputs.probability pc hp
        have hpairs := prepared_bound (hC := canonical) limits current first second tail rfl
        dsimp only [current] at hpairs
        simp only [loop,step,afterCoin,BinaryHeapLoopPrimitiveMeasured.loopMeasuredReference,
          BinaryHeapLoopPrimitiveMeasured.stepBody,BinaryHeapLoopPrimitiveMeasured.afterCoin]
        split
        · rename_i hNone
          simp only [hNone,wrap,combine,listCells_append,listCells_under,listCells]; omega
        · rename_i branch hSome
          let choice := BinaryHeapLoopPrimitiveMeasured.select limits canonical current first second tail rfl pair.data.outputs pair.data.valid branch
          have hs := selected_bound (hC := canonical) limits current first second tail rfl pair.data.outputs pair.data.valid branch
          have hl := ih choice.data.value coin.data.cursor coin.data.bounded
          dsimp only [pair,coin,choice,current] at hs hl
          simp only [hSome,wrap,combine,listCells_append,listCells_under,listCells] at hl ⊢
          omega

theorem run_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loop seed limits canonical state.active state pc hp ≤ 2*listCells (BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).1.2 := by
  change _ ≤ 2*listCells (BinaryHeapLoopPrimitiveMeasured.loopMeasured seed limits canonical state.active state pc hp).1.1.2
  rw [BinaryHeapLoopPrimitiveMeasured.loopMeasured_eq_reference]
  exact loop_bound seed limits canonical state.active state pc hp


end Blotto.BinaryReflectedPrimitiveArithmeticEntryWork

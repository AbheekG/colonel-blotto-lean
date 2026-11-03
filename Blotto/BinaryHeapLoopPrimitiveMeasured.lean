import Blotto.BinaryHeapLoopFusedMeasured

/-! The actual selected resource recursion returns its preceding full result,
trace and source charge together with reached opcode division, coin guard/step,
write-reversal and two-write-control charges. The selected recursion retains
absolute-depth plans and emits once at its requested outer entry. A separate
returned charge forwards reached coin emission and the final resource emission.
The preceding factor-six scope remains exact. New bounds explicitly retain
trace length; native scalar/header/reference/allocator pricing remains separate. -/
namespace Blotto.BinaryHeapLoopPrimitiveMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished Result)
open BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

structure Prepared
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) where
  data : BinaryHeapLoopFusedMeasured.Prepared hC state first second tail he
  extra : ℕ

@[irreducible] def prepare (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : Prepared hC state first second tail he :=
  let produced := BinaryHeapPairSourceMeasured.pairMeasured (hC := hC) limits state first second tail he
  ⟨⟨produced.1.1.1,produced.1.1.2,produced.1.2,by
    rw [BinaryHeapPairSourceMeasured.pairMeasured_compat]
    exact BinaryHeapPairSourceMeasured.pair_value (hC := hC) limits state first second tail he⟩,produced.2⟩

theorem prepare_compat (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (prepare limits hC state first second tail he).data =
      BinaryHeapLoopFusedMeasured.prepare limits hC state first second tail he := by
  simp only [prepare,BinaryHeapLoopFusedMeasured.prepare,BinaryHeapPairSourceMeasured.pairMeasured_compat]

theorem prepare_work_bound (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (prepare limits hC state first second tail he).extra ≤ 4*(prepare limits hC state first second tail he).data.work := by
  have h := BinaryHeapPairSourceMeasured.pairMeasured_division_work_bound (hC := hC) limits state first second tail he
  rw [← BinaryHeapPairSourceMeasured.pairMeasured_compat] at h
  simpa only [prepare] using h

structure Draw (seed : BinarySeedLookupTree.Store) where
  data : BinaryHeapLoopFusedMeasured.Draw seed
  extra : ℕ
  emission : ℕ

@[irreducible] def draw (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : Draw seed :=
  let measured := BinaryWordCoinSourceMeasured.sampleTraceMeasured seed word pc hp 0
  let produced := measured.1
  ⟨⟨produced.1.1.1.1,produced.1.1.1.2,produced.1.1.2,produced.1.2,by
    change (BinaryWordCoinSourceMeasured.sampleMeasured seed word pc hp).1.1.1.2.value ≤ seed.cap.value
    rw [BinaryWordCoinSourceMeasured.sampleMeasured_compat]
    exact (BinaryWordCoinSourceMeasured.sample_position seed word pc hp).2⟩,produced.2,measured.2⟩

theorem draw_compat (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed word pc hp).data = BinaryHeapLoopFusedMeasured.draw seed word pc hp := by
  simp only [draw,BinaryHeapLoopFusedMeasured.draw,
    BinaryWordCoinSourceMeasured.sample,BinaryWordCoinSourceMeasured.sampleMeasured]

theorem draw_work_bound (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed word pc hp).extra ≤ 4*(draw seed word pc hp).data.work := by
  have h := BinaryWordCoinSourceMeasured.sampleMeasured_work_bound seed word pc hp
  rw [← BinaryWordCoinSourceMeasured.sampleMeasured_compat] at h
  simpa only [draw,BinaryWordCoinSourceMeasured.sampleMeasured] using h

structure Selection (state : Finished capacity n hCount) where
  data : BinaryHeapLoopFusedMeasured.Selection state
  extra : ℕ
  writeEmission : ℕ

@[irreducible] def select (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Selection state :=
  let measured := BinaryHeapUpdateMeasured.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch
  let produced := measured.1
  ⟨⟨produced.1.1.1,produced.1.1.2,produced.1.2.1,by
    change (BinaryHeapUpdateMeasured.select (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.active.length < state.active.length
    exact BinaryHeapUpdateMeasured.select_progress (hC := hC) limits state first second tail he outputs hOutputs branch⟩,
    produced.2+produced.1.2.2+9,measured.2⟩

theorem select_compat (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).data =
      BinaryHeapLoopFusedMeasured.select limits hC state first second tail he outputs hOutputs branch := by
  simp only [select,BinaryHeapLoopFusedMeasured.select,BinaryHeapLoopFusedMeasured.selectMeasured,
    BinaryHeapUpdateMeasured.select,BinaryHeapUpdateMeasured.selectMeasured]

theorem select_work_bound (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).extra ≤
      5*(select limits hC state first second tail he outputs hOutputs branch).data.work := by
  have h := BinaryHeapUpdateMeasured.selectMeasured_extras_bound (hC := hC) limits state first second tail he outputs hOutputs branch
  rw [← BinaryHeapUpdateMeasured.selectMeasured_compat] at h
  simpa only [select,BinaryHeapUpdateMeasured.selectMeasured] using h

/-- Matching the returned coin as an explicit parameter avoids reducing its
concrete pair arithmetic while preprocessing the recursive equations. -/
def afterCoin (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ((Result seed capacity n hCount × Trace) × ℕ) × ℕ)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (prepared : Prepared hC state first second tail he)
    (coin : Draw seed) : ((Result seed capacity n hCount × Trace) × ℕ) × ℕ :=
  match coin.data.outcome with
  | none => ((((none,coin.data.cursor),wrap 24 2 [prepared.data.trace,coin.data.trace]),
      prepared.data.work+coin.data.work+4),prepared.extra+coin.extra)
  | some branch =>
      let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
      let later := resume selected.data.value coin.data.cursor coin.data.bounded
      (((later.1.1.1,wrap 32 2 [prepared.data.trace,coin.data.trace,selected.data.trace,later.1.1.2]),
        prepared.data.work+coin.data.work+selected.data.work+later.1.2+8),
        prepared.extra+coin.extra+selected.extra+later.2)

def stepBody (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ((Result seed capacity n hCount × Trace) × ℕ) × ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((Result seed capacity n hCount × Trace) × ℕ) × ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := prepare limits hC state first second tail he
      let coin := draw seed prepared.data.outputs.probability pc hp
      afterCoin seed limits hC resume state first second tail he prepared coin
  | _ => ((((some state,pc),wrap 16 2 []),2),0)

def loopMeasuredReference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((Result seed capacity n hCount × Trace) × ℕ) × ℕ :=
  match fuel with
  | [] => ((((some state,pc),wrap 16 2 []),2),0)
  | _::rest => stepBody seed limits hC
      (fun state pc hp => loopMeasuredReference seed limits hC rest state pc hp) state pc hp
termination_by structural fuel

def loopReference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (Result seed capacity n hCount × Trace) × ℕ := (loopMeasuredReference seed limits hC fuel state pc hp).1

theorem loopMeasuredReference_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (loopMeasuredReference seed limits hC fuel state pc hp).1 = loopReference seed limits hC fuel state pc hp := rfl

def Covered {α : Type} (result : (α × ℕ) × ℕ) : Prop := result.2 ≤ 5*result.1.2

set_option backward.isDefEq.respectTransparency true in
theorem loopMeasuredReference_covered (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Covered (loopMeasuredReference seed limits hC fuel state pc hp) := by
  induction fuel generalizing state pc with
  | nil => simp [loopMeasuredReference,Covered]
  | cons marker fuel ih =>
      unfold loopMeasuredReference stepBody afterCoin
      split
      · rename_i first second tail he
        dsimp only
        have hpw := prepare_work_bound limits hC state first second tail he
        have hcw := draw_work_bound seed (prepare limits hC state first second tail he).data.outputs.probability pc hp
        split
        · unfold Covered
          dsimp only
          omega
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hsw := select_work_bound limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded
          unfold Covered at hl ⊢
          with_reducible
            change prepared.extra+coin.extra+selected.extra+
              (loopMeasuredReference seed limits hC fuel selected.data.value coin.data.cursor coin.data.bounded).2 ≤
              5*(prepared.data.work+coin.data.work+selected.data.work+
                (loopMeasuredReference seed limits hC fuel selected.data.value coin.data.cursor coin.data.bounded).1.2+8)
          dsimp only [prepared,coin,selected] at hsw hl ⊢
          omega
      · simp [Covered]

theorem loopReference_eq_fused (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loopReference seed limits hC fuel state pc hp = BinaryHeapLoopFusedMeasured.loop seed limits hC fuel state pc hp := by
  induction fuel generalizing state pc with
  | nil => rfl
  | cons marker fuel ih =>
      conv_lhs => unfold loopReference loopMeasuredReference stepBody afterCoin
      conv_rhs => unfold BinaryHeapLoopFusedMeasured.loop
      dsimp only
      split
      · rename_i first second tail he
        symm
        split
        · rename_i otherFirst otherSecond otherTail hOther
          have hHeads := List.cons.inj (he.symm.trans hOther)
          have hRest := List.cons.inj hHeads.2
          have hFirst := hHeads.1
          have hSecond := hRest.1
          have hTail := hRest.2
          subst otherFirst
          subst otherSecond
          subst otherTail
          symm
          simp only [prepare_compat,draw_compat,select_compat,loopMeasuredReference_compat]
          split
          · rename_i hNone
            symm
            split
            · with_reducible rfl
            · rename_i other hOther
              with_reducible cases hNone.symm.trans hOther
          · rename_i branch hSome
            symm
            split
            · rename_i hNone
              with_reducible cases hSome.symm.trans hNone
            · rename_i otherBranch hOther
              have hBranch := by with_reducible exact Option.some.inj (hSome.symm.trans hOther)
              subst otherBranch
              symm
              simp only [ih]
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        symm
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · with_reducible rfl

theorem draw_emission_bound (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed word pc hp).emission ≤ 10*(draw seed word pc hp).data.work := by
  have h := BinaryWordCoinSourceMeasured.sampleTraceMeasured_emission seed word pc hp 0
  simpa only [draw] using h

-- Only the final public entry emits the resource plan. The additional returned
-- charge forwards the actual emissions already performed by reached coin draws.
def afterCoinPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (prepared : Prepared hC state first second tail he)
    (coin : Draw seed) (depth : ℕ) : (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ :=
  match coin.data.outcome with
  | none =>
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join (.shifted (depth+2) prepared.data.trace) (.shifted (depth+2) coin.data.trace))
      (((((none,coin.data.cursor),plan),prepared.data.work+coin.data.work+4),
        prepared.extra+coin.extra),coin.emission)
  | some branch =>
      let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
      let later := resume selected.data.value coin.data.cursor coin.data.bounded (depth+2)
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.shifted (depth+2) prepared.data.trace)
          (.join (.shifted (depth+2) coin.data.trace)
            (.join (.shifted (depth+2) selected.data.trace) later.1.1.1.2)))
      ((((later.1.1.1.1,plan),prepared.data.work+coin.data.work+selected.data.work+later.1.1.2+8),
        prepared.extra+coin.extra+selected.extra+later.1.2),coin.emission+later.2)

def stepPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := prepare limits hC state first second tail he
      let coin := draw seed prepared.data.outputs.probability pc hp
      afterCoinPlanAt seed limits hC resume state first second tail he prepared coin depth
  | _ => (((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0)

def loopPlanAtReference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ :=
  match fuel with
  | [] => (((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0)
  | _::rest => stepPlanAt seed limits hC
      (fun state pc hp depth => loopPlanAtReference seed limits hC rest state pc hp depth) state pc hp depth
termination_by structural fuel

theorem loopPlanAtReference_refines (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryWordCoinSourceMeasured.projected (loopPlanAtReference seed limits hC fuel state pc hp depth).1 =
      BinaryWordCoinSourceMeasured.offset depth (loopMeasuredReference seed limits hC fuel state pc hp) := by
  induction fuel generalizing state pc depth with
  | nil => rfl
  | cons marker fuel ih =>
      conv_lhs => unfold BinaryWordCoinSourceMeasured.projected loopPlanAtReference stepPlanAt afterCoinPlanAt
      conv_rhs => unfold BinaryWordCoinSourceMeasured.offset loopMeasuredReference stepBody afterCoin
      dsimp only
      split
      · rename_i first second tail he
        split
        · simp only [BinaryTracePlanMeasured.denote,wrap,combine,BinaryTraceDepth.under_append,
            BinaryTraceDepth.under_compose,List.append_nil,List.append_assoc]
          rfl
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hLater := ih selected.data.value coin.data.cursor coin.data.bounded (depth+2)
          have hData := congrArg (fun output => output.1.1.1) hLater
          have hTrace := congrArg (fun output => output.1.1.2) hLater
          have hWork := congrArg (fun output => output.1.2) hLater
          have hExtra := congrArg Prod.snd hLater
          dsimp only [BinaryWordCoinSourceMeasured.projected,BinaryWordCoinSourceMeasured.offset,
            prepared,coin,selected] at hData hTrace hWork hExtra
          simp only [BinaryTracePlanMeasured.denote,hData,hTrace,hWork,hExtra,wrap,combine,
            BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose,List.append_nil,List.append_assoc]
          rfl
      · rfl

theorem select_write_emission_bound (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : (select limits hC state first second tail he outputs hOutputs branch).writeEmission ≤
      32*(select limits hC state first second tail he outputs hOutputs branch).data.work := by
  have h := BinaryHeapUpdateMeasured.selectTraceMeasured_write_bound (hC := hC) limits state first second tail he outputs hOutputs branch
  simpa only [select,BinaryHeapUpdateMeasured.selectMeasured] using h

def afterCoinPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (prepared : Prepared hC state first second tail he)
    (coin : Draw seed) (depth : ℕ) : ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ :=
  match coin.data.outcome with
  | none =>
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join (.shifted (depth+2) prepared.data.trace) (.shifted (depth+2) coin.data.trace))
      ((((((none,coin.data.cursor),plan),prepared.data.work+coin.data.work+4),
        prepared.extra+coin.extra),coin.emission),0)
  | some branch =>
      let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
      let returned := resume selected.data.value coin.data.cursor coin.data.bounded (depth+2)
      let later := returned.1
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.shifted (depth+2) prepared.data.trace)
          (.join (.shifted (depth+2) coin.data.trace)
            (.join (.shifted (depth+2) selected.data.trace) later.1.1.1.2)))
      (((((later.1.1.1.1,plan),prepared.data.work+coin.data.work+selected.data.work+later.1.1.2+8),
        prepared.extra+coin.extra+selected.extra+later.1.2),coin.emission+later.2),selected.writeEmission+returned.2)

def stepPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := prepare limits hC state first second tail he
      let coin := draw seed prepared.data.outputs.probability pc hp
      afterCoinPlanWithWritesAt seed limits hC resume state first second tail he prepared coin depth
  | _ => ((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0)

def loopPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ :=
  match fuel with
  | [] => ((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0)
  | _::rest => stepPlanWithWritesAt seed limits hC
      (fun state pc hp depth => loopPlanWithWritesAt seed limits hC rest state pc hp depth) state pc hp depth
termination_by structural fuel

theorem loopPlanWithWritesAt_refines (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).1 =
      loopPlanAtReference seed limits hC fuel state pc hp depth := by
  induction fuel generalizing state pc depth with
  | nil => rfl
  | cons marker fuel ih =>
      unfold loopPlanWithWritesAt stepPlanWithWritesAt afterCoinPlanWithWritesAt
        loopPlanAtReference stepPlanAt afterCoinPlanAt
      dsimp only
      split
      · rename_i first second tail he
        split
        · rfl
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded (depth+2)
          dsimp only [prepared,coin,selected] at hl
          simp only [hl]
      · rfl

def loopPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ :=
  (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).1

theorem loopPlanAt_eq_reference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    loopPlanAt seed limits hC fuel state pc hp depth = loopPlanAtReference seed limits hC fuel state pc hp depth :=
  loopPlanWithWritesAt_refines seed limits hC fuel state pc hp depth

theorem loopPlanAt_refines (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryWordCoinSourceMeasured.projected (loopPlanAt seed limits hC fuel state pc hp depth).1 =
      BinaryWordCoinSourceMeasured.offset depth (loopMeasuredReference seed limits hC fuel state pc hp) := by
  rw [loopPlanAt_eq_reference]
  exact loopPlanAtReference_refines seed limits hC fuel state pc hp depth

def loopTraceMeasuredReference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (((Result seed capacity n hCount × Trace) × ℕ) × ℕ) × ℕ :=
  let planned := loopPlanAt seed limits hC fuel state pc hp depth
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  ((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2)


def loopTraceWithWrites (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    ((((Result seed capacity n hCount × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  let returned := loopPlanWithWritesAt seed limits hC fuel state pc hp depth
  let planned := returned.1
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.1.2 []
  (((((planned.1.1.1.1,emitted.1.1),planned.1.1.2),planned.1.2),planned.2+emitted.1.2+emitted.2),returned.2)

def loopTraceMeasured (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (((Result seed capacity n hCount × Trace) × ℕ) × ℕ) × ℕ :=
  (loopTraceWithWrites seed limits hC fuel state pc hp depth).1

theorem loopTraceMeasured_eq_reference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    loopTraceMeasured seed limits hC fuel state pc hp depth =
      loopTraceMeasuredReference seed limits hC fuel state pc hp depth := rfl


def loopMeasured (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((Result seed capacity n hCount × Trace) × ℕ) × ℕ :=
  (loopTraceMeasured seed limits hC fuel state pc hp 0).1

theorem loopMeasured_eq_reference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loopMeasured seed limits hC fuel state pc hp = loopMeasuredReference seed limits hC fuel state pc hp := by
  simpa only [loopMeasured,loopTraceMeasured_eq_reference,loopTraceMeasuredReference,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,BinaryWordCoinSourceMeasured.projected,
    BinaryWordCoinSourceMeasured.offset,BinaryTraceDepth.under_zero] using
      loopPlanAt_refines seed limits hC fuel state pc hp 0

def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (Result seed capacity n hCount × Trace) × ℕ := (loopMeasured seed limits hC fuel state pc hp).1

theorem loopMeasured_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (loopMeasured seed limits hC fuel state pc hp).1 = loop seed limits hC fuel state pc hp := rfl

theorem loopMeasured_covered (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Covered (loopMeasured seed limits hC fuel state pc hp) := by
  rw [loopMeasured_eq_reference]
  exact loopMeasuredReference_covered seed limits hC fuel state pc hp

theorem loop_eq_fused (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loop seed limits hC fuel state pc hp = BinaryHeapLoopFusedMeasured.loop seed limits hC fuel state pc hp := by
  rw [loop,loopMeasured_eq_reference]
  exact loopReference_eq_fused seed limits hC fuel state pc hp

def runPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : ((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ :=
  loopPlanWithWritesAt seed limits hC state.active state pc hp depth

def runTraceWithWrites (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((((Result seed capacity n hCount × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  loopTraceWithWrites seed limits hC state.active state pc hp 0

def runPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : (((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ :=
  loopPlanAt seed limits hC state.active state pc hp depth

def runTraceMeasured (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (((Result seed capacity n hCount × Trace) × ℕ) × ℕ) × ℕ :=
  loopTraceMeasured seed limits hC state.active state pc hp 0

def runMeasured (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((Result seed capacity n hCount × Trace) × ℕ) × ℕ :=
  (runTraceMeasured seed limits hC state pc hp).1

def run (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (Result seed capacity n hCount × Trace) × ℕ := (runMeasured seed limits hC state pc hp).1

theorem runMeasured_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runMeasured seed limits hC state pc hp).1 = run seed limits hC state pc hp := rfl

theorem run_eq_fused (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    run seed limits hC state pc hp = BinaryHeapLoopFusedMeasured.run seed limits hC state pc hp :=
  loop_eq_fused seed limits hC state.active state pc hp

theorem run_eq_reference (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    run seed limits hC state pc hp = BinaryPRGHeapLoopMeasuredWork.runWithTraceAndWork seed limits hC state pc hp := by
  rw [run_eq_fused,BinaryHeapLoopFusedMeasured.run_eq_reference]

theorem runMeasured_extras_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runMeasured seed limits hC state pc hp).2 ≤ 5*(run seed limits hC state pc hp).2 :=
  loopMeasured_covered seed limits hC state.active state pc hp

theorem run_with_extras_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed limits hC state pc hp).2+(runMeasured seed limits hC state pc hp).2 ≤
      6*(BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 := by
  have h := runMeasured_extras_bound seed limits hC state pc hp
  have hw : (run seed limits hC state pc hp).2 =
      (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 := by
    rw [run_eq_fused,BinaryHeapLoopFusedMeasured.run_work]
  rw [← hw]
  omega

theorem loopTraceMeasured_refines (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopTraceMeasured seed limits hC fuel state pc hp depth).1 =
      BinaryWordCoinSourceMeasured.offset depth (loopMeasuredReference seed limits hC fuel state pc hp) := by
  simpa only [loopTraceMeasured_eq_reference,loopTraceMeasuredReference,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,BinaryWordCoinSourceMeasured.projected] using
      loopPlanAt_refines seed limits hC fuel state pc hp depth

theorem runPlanAt_refines (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    BinaryWordCoinSourceMeasured.projected (runPlanAt seed limits hC state pc hp depth).1 =
      BinaryWordCoinSourceMeasured.offset depth (runMeasured seed limits hC state pc hp) := by
  change BinaryWordCoinSourceMeasured.projected (loopPlanAt seed limits hC state.active state pc hp depth).1 =
    BinaryWordCoinSourceMeasured.offset depth (loopMeasured seed limits hC state.active state pc hp)
  rw [loopMeasured_eq_reference]
  exact loopPlanAt_refines seed limits hC state.active state pc hp depth

theorem runPlanAt_data (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC state pc hp depth).1.1.1.1 = (runMeasured seed limits hC state pc hp).1.1.1 :=
  congrArg (fun output => output.1.1.1) (runPlanAt_refines seed limits hC state pc hp depth)

theorem runPlanAt_trace (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    BinaryTracePlanMeasured.denote (runPlanAt seed limits hC state pc hp depth).1.1.1.2 =
      under depth (runMeasured seed limits hC state pc hp).1.1.2 :=
  congrArg (fun output => output.1.1.2) (runPlanAt_refines seed limits hC state pc hp depth)

theorem runPlanAt_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC state pc hp depth).1.1.2 = (runMeasured seed limits hC state pc hp).1.2 :=
  congrArg (fun output => output.1.2) (runPlanAt_refines seed limits hC state pc hp depth)

theorem runPlanAt_extra (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC state pc hp depth).1.2 = (runMeasured seed limits hC state pc hp).2 := by
  have h := congrArg (fun output => output.2) (runPlanAt_refines seed limits hC state pc hp depth)
  exact h

theorem loopPlanAtReference_nodes (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.nodes (loopPlanAtReference seed limits hC fuel state pc hp depth).1.1.1.2 ≤ 8*fuel.length+1 := by
  induction fuel generalizing state pc depth with
  | nil => simp [loopPlanAtReference,BinaryTracePlanMeasured.nodes]
  | cons marker fuel ih =>
      unfold loopPlanAtReference stepPlanAt afterCoinPlanAt
      dsimp only
      split
      · rename_i first second tail he
        split
        · simp only [BinaryTracePlanMeasured.nodes,List.length_cons]; omega
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded (depth+2)
          simp only [BinaryTracePlanMeasured.nodes,List.length_cons]
          dsimp only [prepared,coin,selected] at hl
          omega
      · simp only [BinaryTracePlanMeasured.nodes,List.length_cons]; omega

theorem loopPlanAt_nodes (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.nodes (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2 ≤ 8*fuel.length+1 := by
  rw [loopPlanAt_eq_reference]
  exact loopPlanAtReference_nodes seed limits hC fuel state pc hp depth

theorem loopPlanAtReference_child_emission (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanAtReference seed limits hC fuel state pc hp depth).2 ≤
      10*(loopPlanAtReference seed limits hC fuel state pc hp depth).1.1.2 := by
  induction fuel generalizing state pc depth with
  | nil => simp [loopPlanAtReference]
  | cons marker fuel ih =>
      unfold loopPlanAtReference stepPlanAt afterCoinPlanAt
      dsimp only
      split
      · rename_i first second tail he
        have hc := draw_emission_bound seed (prepare limits hC state first second tail he).data.outputs.probability pc hp
        split
        · dsimp only; omega
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded (depth+2)
          dsimp only [prepared,coin,selected] at hl
          dsimp only
          omega
      · simp

theorem loopPlanAt_child_emission (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanAt seed limits hC fuel state pc hp depth).2 ≤
      10*(loopPlanAt seed limits hC fuel state pc hp depth).1.1.2 := by
  rw [loopPlanAt_eq_reference]
  exact loopPlanAtReference_child_emission seed limits hC fuel state pc hp depth

theorem loopTraceMeasured_emission (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopTraceMeasured seed limits hC fuel state pc hp depth).2 ≤
      10*(loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.2+
        5*(loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.1.2.length+16*fuel.length+2 := by
  have hn := loopPlanAt_nodes seed limits hC fuel state pc hp depth
  have hc := loopPlanAt_child_emission seed limits hC fuel state pc hp depth
  have hs := BinaryTracePlanMeasured.shiftCount_bound (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2
  simp only [loopTraceMeasured_eq_reference,loopTraceMeasuredReference]
  simp only [BinaryTracePlanMeasured.emitFull_erases,BinaryTracePlanMeasured.emit_work,
    BinaryTracePlanMeasured.emitFull_shifts,BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero]
  omega

theorem loopTraceMeasured_total (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.2+
      (loopTraceMeasured seed limits hC fuel state pc hp depth).1.2+
      (loopTraceMeasured seed limits hC fuel state pc hp depth).2 ≤
        16*(loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.2+
          5*(loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.1.2.length+16*fuel.length+2 := by
  have he := loopTraceMeasured_emission seed limits hC fuel state pc hp depth
  have hOld := loopMeasuredReference_covered seed limits hC fuel state pc hp
  have hx : (loopTraceMeasured seed limits hC fuel state pc hp depth).1.2 ≤
      5*(loopTraceMeasured seed limits hC fuel state pc hp depth).1.1.2 := by
    rw [loopTraceMeasured_refines]
    exact hOld
  omega

theorem loop_plan_references (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.planReferences (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2 ≤ 16*fuel.length+2 := by
  have h := BinaryTracePlanMeasured.planReferences_bound (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2
  have hn := loopPlanAt_nodes seed limits hC fuel state pc hp depth
  omega

theorem loop_emit_frames (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.emitFrames (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2 ≤
      BinaryTracePlanMeasured.payload (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2+8*fuel.length+2 := by
  have h := BinaryTracePlanMeasured.emitFrames_bound (loopPlanAt seed limits hC fuel state pc hp depth).1.1.1.2
  have hn := loopPlanAt_nodes seed limits hC fuel state pc hp depth
  omega

theorem runTraceMeasured_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runTraceMeasured seed limits hC state pc hp).1 = runMeasured seed limits hC state pc hp := rfl

theorem runPlanAt_nodes_dimension (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : BinaryTracePlanMeasured.nodes (runPlanAt seed limits hC state pc hp depth).1.1.1.2 ≤ 8*n+1 := by
  have h := loopPlanAt_nodes seed limits hC state.active state pc hp depth
  have hn := state.active_length_le
  exact h.trans (by omega)

theorem runTraceMeasured_total_dimension (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runTraceMeasured seed limits hC state pc hp).1.1.2+
      (runTraceMeasured seed limits hC state pc hp).1.2+(runTraceMeasured seed limits hC state pc hp).2 ≤
        16*(runTraceMeasured seed limits hC state pc hp).1.1.2+
          5*(runTraceMeasured seed limits hC state pc hp).1.1.1.2.length+16*n+2 := by
  have h := loopTraceMeasured_total seed limits hC state.active state pc hp 0
  have hn := state.active_length_le
  change (runTraceMeasured seed limits hC state pc hp).1.1.2+
    (runTraceMeasured seed limits hC state pc hp).1.2+(runTraceMeasured seed limits hC state pc hp).2 ≤
      16*(runTraceMeasured seed limits hC state pc hp).1.1.2+
        5*(runTraceMeasured seed limits hC state pc hp).1.1.1.2.length+16*state.active.length+2 at h
  omega

theorem loopPlanWithWritesAt_write_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).2 ≤
      32*(loopPlanWithWritesAt seed limits hC fuel state pc hp depth).1.1.1.2 := by
  induction fuel generalizing state pc depth with
  | nil => simp [loopPlanWithWritesAt]
  | cons marker fuel ih =>
      unfold loopPlanWithWritesAt stepPlanWithWritesAt afterCoinPlanWithWritesAt
      dsimp only
      split
      · rename_i first second tail he
        split
        · dsimp only; omega
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.data.outputs.probability pc hp
          let selected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hs := select_write_emission_bound limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
          have hl := ih selected.data.value coin.data.cursor coin.data.bounded (depth+2)
          dsimp only [prepared,coin,selected] at hs hl
          dsimp only
          omega
      · simp

theorem runPlanWithWritesAt_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (runPlanWithWritesAt seed limits hC state pc hp depth).1 = runPlanAt seed limits hC state pc hp depth := rfl

theorem loopTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopTraceWithWrites seed limits hC fuel state pc hp depth).1 =
      loopTraceMeasured seed limits hC fuel state pc hp depth := rfl

theorem runTraceWithWrites_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runTraceWithWrites seed limits hC state pc hp).1 = runTraceMeasured seed limits hC state pc hp := rfl

theorem runPlanWithWritesAt_write_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (runPlanWithWritesAt seed limits hC state pc hp depth).2 ≤
      32*(runPlanWithWritesAt seed limits hC state pc hp depth).1.1.1.2 :=
  loopPlanWithWritesAt_write_bound seed limits hC state.active state pc hp depth

theorem runTraceWithWrites_write_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runTraceWithWrites seed limits hC state pc hp).2 ≤ 32*(run seed limits hC state pc hp).2 :=
  loopPlanWithWritesAt_write_bound seed limits hC state.active state pc hp 0

end Blotto.BinaryHeapLoopPrimitiveMeasured

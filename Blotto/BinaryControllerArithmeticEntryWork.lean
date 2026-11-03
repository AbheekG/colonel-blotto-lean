import Blotto.BinarySelectionArithmeticEntryWork

/-! Proof-only entry charges follow concrete pair preparation, the actual coin
outcome and concrete selection's returned state/cursor. Structural fuel gives
an execution-wide retained-cell bound, without an abstract backend premise. -/
namespace Blotto.BinaryControllerArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryHeapLoopPrimitiveMeasured (draw)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency true
variable {capacity : Store} {n : ℕ} {hCount : n=capacity.cap.value}

def afterCoin (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ℕ)
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail)
    (coin : BinaryHeapLoopPrimitiveMeasured.Draw seed) (depth : ℕ) : ℕ :=
  let prepared := BinaryPackedLoopPlan.prepare limits hC state first second tail he
  BinarySelectionArithmeticEntryWork.prepared (hC := hC) limits state first second tail he+
    match coin.data.outcome with
    | none => 0
    | some branch =>
        let selected := BinaryWriteLoopBackend.select limits hC state first second tail he
          prepared.1.data.outputs prepared.1.data.valid branch
        BinarySelectionArithmeticEntryWork.selected limits state first second tail prepared.1.data.outputs branch+
          resume selected.1.1.data.value coin.data.cursor coin.data.bounded (depth+2)

def step (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) (depth : ℕ) : ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := BinaryPackedLoopPlan.prepare limits hC state first second tail he
      let coin := draw seed prepared.1.data.outputs.probability pc hp
      afterCoin seed limits hC resume state first second tail he coin depth
  | _ => 0

def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) : ℕ :=
  match fuel with
  | [] => 0
  | _::rest => step seed limits hC
      (fun state pc hp depth => loop seed limits hC rest state pc hp depth) state pc hp depth
termination_by structural fuel

theorem loop_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    loop seed limits hC fuel state pc hp depth ≤ 2*listCells (denote
      (BinarySelectPriceContinuation.loopPlanWithWritesAt seed limits hC (BinaryWriteLoopBackend.backend limits hC)
        fuel state pc hp depth).1.1.1.1.1.1.2) := by
  induction fuel generalizing state pc depth with
  | nil => simp only [loop,BinarySelectPriceContinuation.loopPlanWithWritesAt,denote,listCells]; omega
  | cons marker rest ih =>
      rcases state with ⟨ruler,size,heap,root,valid,active,certified⟩
      cases active with
      | nil => simp only [loop,step,BinarySelectPriceContinuation.loopPlanWithWritesAt,
          BinarySelectPriceContinuation.stepPlanWithWritesAt,denote,listCells]; omega
      | cons first addresses => cases addresses with
        | nil => simp only [loop,step,BinarySelectPriceContinuation.loopPlanWithWritesAt,
            BinarySelectPriceContinuation.stepPlanWithWritesAt,denote,listCells]; omega
        | cons second tail =>
            let current : Finished capacity n hCount := ⟨ruler,size,heap,root,valid,first::second::tail,certified⟩
            let prepared := BinaryPackedLoopPlan.prepare limits hC current first second tail rfl
            let coin := draw seed prepared.1.data.outputs.probability pc hp
            have hpairs := BinarySelectionArithmeticEntryWork.prepared_bound (hC := hC) limits current first second tail rfl
            dsimp only [current] at hpairs
            simp only [loop,step,afterCoin,BinarySelectPriceContinuation.loopPlanWithWritesAt,
              BinarySelectPriceContinuation.stepPlanWithWritesAt,BinarySelectPriceContinuation.afterCoinPlanWithWritesAt]
            split
            · rename_i hNone
              simp only [hNone,denote,listCells_append,listCells_under,listCells]
              omega
            · rename_i branch hSome
              let selected := BinaryWriteLoopBackend.select limits hC current first second tail rfl
                prepared.1.data.outputs prepared.1.data.valid branch
              have hs := BinarySelectionArithmeticEntryWork.selected_bound limits current first second tail rfl
                prepared.1.data.outputs prepared.1.data.valid branch
              have hl := ih selected.1.1.data.value coin.data.cursor coin.data.bounded (depth+2)
              dsimp only [selected,coin,prepared,current] at hs hl hpairs
              simp only [hSome,BinaryWriteLoopBackend.backend,denote,listCells_append,listCells_under,listCells] at hl ⊢
              omega

theorem loop_coin_failure (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (marker : Address capacity.width capacity.cap) (rest : List (Address capacity.width capacity.cap))
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active=first::second::tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ)
    (hNone : (draw seed (BinaryPackedLoopPlan.prepare limits hC state first second tail he).1.data.outputs.probability pc hp).data.outcome=none) :
    loop seed limits hC (marker::rest) state pc hp depth =
      BinarySelectionArithmeticEntryWork.prepared (hC := hC) limits state first second tail he := by
  rcases state with ⟨ruler,size,heap,root,valid,active,certified⟩
  change active=first::second::tail at he
  subst active
  unfold loop step afterCoin
  simp only [hNone,Nat.add_zero]

def run (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) : ℕ :=
  loop seed limits hC state.active state pc hp depth

theorem run_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    run seed limits hC state pc hp depth ≤
      2*listCells (denote (BinaryWriteLoopBackend.runPlanAt seed limits hC state pc hp depth).1.1.1.1.1.1.2) :=
  loop_bound seed limits hC state.active state pc hp depth

theorem run_with_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    let produced := BinaryWriteLoopBackend.runPlanAt seed limits hC state pc hp depth
    run seed limits hC state pc hp depth+produced.1.1.1.1.1.2+produced.1.1.1.1.2+
      produced.1.1.1.2+produced.1.1.2+produced.1.2+produced.2 ≤
      2*(listCells (denote produced.1.1.1.1.1.1.2)+produced.1.1.1.1.1.2+produced.1.1.1.1.2+
        produced.1.1.1.2+produced.1.1.2+produced.1.2+produced.2) := by
  have h := run_bound seed limits hC state pc hp depth
  dsimp only
  omega

end Blotto.BinaryControllerArithmeticEntryWork

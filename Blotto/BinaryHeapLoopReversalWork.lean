import Blotto.BinaryHeapLoopFusedMeasured

/-! A proof-side ledger sums the actual extra write-reversal work returned by
the selected fused updates and their fixed two-write sequence control charge.
The selected public result/source counter is exact
as before. Its old whole-loop charge dominates this extra ledger, so their sum
has a factor-two bound. This ledger is not called by the selected runner and
does not price native evaluation of observer fields or imported primitives. -/
namespace Blotto.BinaryHeapLoopReversalWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryHeapLoopFusedMeasured (prepare draw selectMeasured)
set_option autoImplicit false
set_option maxHeartbeats 500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def Covered (charges : ℕ × ℕ) : Prop := charges.1 ≤ charges.2

def ledger (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) :
    List (Address capacity.width capacity.cap) → (state : Finished capacity n hCount) →
      (pc : FixedBinaryWord seed.width) → pc.value ≤ seed.cap.value → ℕ × ℕ
  | [],_state,_pc,_hp => (0,2)
  | _::fuel,state,pc,hp =>
      match he : state.active with
      | first::second::tail =>
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.outputs.probability pc hp
          match coin.outcome with
          | none => (0,prepared.work+coin.work+4)
          | some branch =>
              let selected := selectMeasured limits hC state first second tail he prepared.outputs prepared.valid branch
              let later := ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded
              (selected.2+9+later.1,prepared.work+coin.work+selected.1.work+later.2+8)
      | _ => (0,2)
termination_by structural fuel _state _pc _hp => fuel

set_option backward.isDefEq.respectTransparency true in
theorem ledger_covered (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Covered (ledger seed limits hC fuel state pc hp) := by
  induction fuel generalizing state pc with
  | nil => simp [ledger,Covered]
  | cons marker fuel ih =>
      unfold ledger
      split
      · rename_i first second tail he
        dsimp only
        split
        · simp [Covered]
        · rename_i branch hSome
          let prepared := prepare limits hC state first second tail he
          let coin := draw seed prepared.outputs.probability pc hp
          let selected := selectMeasured limits hC state first second tail he prepared.outputs prepared.valid branch
          have hLocal := BinaryHeapLoopFusedMeasured.selectMeasured_write_overhead_le_work
            limits hC state first second tail he prepared.outputs prepared.valid branch
          with_reducible change selected.2+9 ≤ selected.1.work at hLocal
          have hLater := ih selected.1.value coin.cursor coin.bounded
          change (ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded).1 ≤
            (ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded).2 at hLater
          unfold Covered
          with_reducible
            change selected.2+9+(ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded).1 ≤
              prepared.work+coin.work+selected.1.work+
                (ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded).2+8
          exact (Nat.add_le_add hLocal hLater).trans (by omega)
      · simp [Covered]

set_option backward.isDefEq.respectTransparency true in
theorem ledger_source (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (ledger seed limits hC fuel state pc hp).2 = (BinaryHeapLoopFusedMeasured.loop seed limits hC fuel state pc hp).2 := by
  induction fuel generalizing state pc with
  | nil => rfl
  | cons marker fuel ih =>
      conv_lhs => unfold ledger
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
          simp only [BinaryHeapLoopFusedMeasured.select]
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
              let prepared := prepare limits hC state first second tail he
              let coin := draw seed prepared.outputs.probability pc hp
              let selected := selectMeasured limits hC state first second tail he prepared.outputs prepared.valid branch
              with_reducible
                change prepared.work+coin.work+selected.1.work+
                  (ledger seed limits hC fuel selected.1.value coin.cursor coin.bounded).2+8 =
                  prepared.work+coin.work+selected.1.work+
                    (BinaryHeapLoopFusedMeasured.loop seed limits hC fuel selected.1.value coin.cursor coin.bounded).2+8
              rw [ih]
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        symm
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · with_reducible rfl

def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  (ledger seed limits hC fuel state pc hp).1

theorem loop_le_source (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loop seed limits hC fuel state pc hp ≤ (BinaryHeapLoopFusedMeasured.loop seed limits hC fuel state pc hp).2 := by
  have h := ledger_covered seed limits hC fuel state pc hp
  change (ledger seed limits hC fuel state pc hp).1 ≤ (ledger seed limits hC fuel state pc hp).2 at h
  exact h.trans_eq (ledger_source seed limits hC fuel state pc hp)

def run (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  loop seed limits hC state.active state pc hp

theorem run_le_source (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    run seed limits hC state pc hp ≤ (BinaryHeapLoopFusedMeasured.run seed limits hC state pc hp).2 :=
  loop_le_source seed limits hC state.active state pc hp

theorem run_with_reversals_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryHeapLoopFusedMeasured.run seed limits hC state pc hp).2+run seed limits hC state pc hp ≤
      2*(BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 := by
  have h := run_le_source seed limits hC state pc hp
  rw [← BinaryHeapLoopFusedMeasured.run_work]
  omega

end Blotto.BinaryHeapLoopReversalWork

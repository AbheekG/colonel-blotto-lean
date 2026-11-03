import Blotto.BinaryPRGHeapLowerLifetime
import Blotto.BinaryPRGHeapResourceLoopBudget

/-! The deterministic physical lower loop returns its reached state, lifetime
trace and nonzero source-work charge together. The charge uses the same pair
and update source components as the random resource loop. It is not a complete
native-machine price for trace observation, addressing or reference transport.
The seed in the budget theorem is an erased proof witness only; execution has
no seed argument and never invokes a coin. -/
namespace Blotto.BinaryPRGHeapLowerMeasuredWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapPairLifetime BinaryPRGHeapLoopLifetime BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000
variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def run (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) : (Finished capacity n hCount × Trace) × ℕ :=
  match he : state.active with
  | first :: second :: tail =>
      let prepared := pairWithTrace (hC := hC) limits state first second tail he
      have hOutputs : prepared.1 =
          (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs :=
        (pairWithTrace_erasure limits state first second tail he).trans
          (BinaryPRGHeapResourceLoop.pairWithWork_value limits state first second tail he)
      let selected := selectWithTrace limits state first second tail he prepared.1 hOutputs false
      let later := run limits hC selected.1
      let pairCharge := (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
        limits state first second tail he).2
      let selectedCharge := (BinaryPRGHeapResourceLoop.selectWithWork limits state
        first second tail he prepared.1 hOutputs false).2
      ((later.1.1,wrap 32 2 [prepared.2,selected.2,later.1.2]),
        pairCharge + selectedCharge + later.2 + 8)
  | _ => ((state,wrap 16 2 []),2)
termination_by state.active.length
decreasing_by exact selectWithTrace_progress limits state first second tail he prepared.1 _ false

theorem run_erases (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) :
    (run limits hC state).1 = BinaryPRGHeapLowerLifetime.runWithTrace limits hC state := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount),s.active.length ≤ fuel →
      (run limits hC s).1 = BinaryPRGHeapLowerLifetime.runWithTrace limits hC s from
    h state.active.length state le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hSize
      conv_lhs => unfold run
      conv_rhs => unfold BinaryPRGHeapLowerLifetime.runWithTrace
      split
      · rename_i first second tail he
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
          dsimp only
          let prepared := pairWithTrace (hC := hC) limits s first second tail he
          have hOutputs : prepared.1 =
              (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).outputs :=
            (pairWithTrace_erasure limits s first second tail he).trans
              (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he)
          let selected := selectWithTrace limits s first second tail he prepared.1 hOutputs false
          have hProgress := selectWithTrace_progress limits s first second tail he prepared.1 hOutputs false
          have hLater := ih selected.1.active.length (hProgress.trans_le hSize) selected.1 le_rfl
          change ((run limits hC selected.1).1.1,
            wrap 32 2 [prepared.2,selected.2,(run limits hC selected.1).1.2]) = _
          rw [hLater]
        · rename_i hNoPair
          exact False.elim (hNoPair first second tail he)
      · rename_i hNoPair
        split
        · rename_i first second tail he
          exact False.elim (hNoPair first second tail he)
        · rfl

theorem run_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : BinaryPRGHeapResourceLoopBudget.ReachableStepBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state) :
    (run limits hC state).2 ≤ state.active.length * (2 * M) + 2 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount),Inv s → s.active.length ≤ fuel →
      (run limits hC s).2 ≤ fuel * (2 * M) + 2 from h state.active.length state hInv le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hs hSize
      conv_lhs => unfold run
      split
      · rename_i first second tail he
        dsimp only
        simp only [pairWithTrace_erasure,selectWithTrace_erasure]
        let prepared := BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits s first second tail he
        let selected := BinaryPRGHeapResourceLoop.selectWithWork limits s first second tail he prepared.1
          (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) false
        have hPair := budget.pairCoin s first second tail he seed.cap le_rfl hs
        have hSelected := budget.selected s first second tail he false hs
        have hClosed := budget.closed s first second tail he false hs
        have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits s
          first second tail he prepared.1
          (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he) false
        change prepared.2 + _ + 8 ≤ M at hPair
        change selected.2 ≤ M at hSelected
        change Inv selected.1 at hClosed
        change selected.1.active.length < s.active.length at hProgress
        have hLater := ih selected.1.active.length (hProgress.trans_le hSize) selected.1 hClosed le_rfl
        have hOne : selected.1.active.length + 1 ≤ fuel := by omega
        have hMul := Nat.mul_le_mul_right (2 * M) hOne
        rw [Nat.add_mul,one_mul] at hMul
        change prepared.2 + selected.2 + (run limits hC selected.1).2 + 8 ≤ _
        omega
      · omega

theorem run_inputCount_work (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : BinaryPRGHeapResourceLoopBudget.ReachableStepBudget seed limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state) :
    (run limits hC state).2 ≤ n * (2 * M) + 2 :=
  (run_work seed limits hC Inv M budget state hInv).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (2 * M) state.active_length_le) 2)

end Blotto.BinaryPRGHeapLowerMeasuredWork

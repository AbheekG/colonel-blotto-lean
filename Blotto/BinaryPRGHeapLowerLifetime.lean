import Blotto.BinaryPRGHeapLoopLifetimeBudget
import Blotto.BinaryGeneralResourceFallback

/-! The deterministic physical lower loop executes traced pair arithmetic and
selected tape updates without coin calls, including at probability one. Original
source initialization and materialization remain separate joins. -/
namespace Blotto.BinaryPRGHeapLowerLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage BinaryPRGHeapPairLifetime BinaryPRGHeapLoopLifetime
set_option maxHeartbeats 2000000
variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def runWithTrace (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) : Finished capacity n hCount × Trace :=
  match he : state.active with
  | first :: second :: tail =>
      let prepared := pairWithTrace (hC := hC) limits state first second tail he
      have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs :=
        (pairWithTrace_erasure limits state first second tail he).trans
          (BinaryPRGHeapResourceLoop.pairWithWork_value limits state first second tail he)
      let selected := selectWithTrace limits state first second tail he prepared.1 hOutputs false
      let later := runWithTrace limits hC selected.1
      (later.1,wrap 32 2 [prepared.2,selected.2,later.2])
  | _ => (state,wrap 16 2 [])
termination_by state.active.length
decreasing_by exact selectWithTrace_progress limits state first second tail he prepared.1 _ false

private theorem prepare_original_pair
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail) :
    BinaryGeneralResourceChoice.prepare (table capacity.cap capacity.tree n hCount)
      (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference =
      .ask (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).original.original := by
  have hOne := BinaryPRGHeapResourceLoop.prepare_pair (hC := hC) state.reference first second tail
    (state.certified.choose_spec.2.symm.trans he)
  have hTwo := BinaryPRGWordControllerBooleanResourceLoop.prepare_original capacity n hCount hC state.reference
  rw [hOne] at hTwo
  have hThree := BinaryPRGWordControllerGeneralChoice.prepare_original
    (table capacity.cap capacity.tree n hCount)
    (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference
  rw [← hTwo] at hThree
  exact hThree.symm

private theorem prepare_original_short
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (hShort : state.active = [] ∨ ∃ first,state.active = [first]) :
    BinaryGeneralResourceChoice.prepare (table capacity.cap capacity.tree n hCount)
      (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference =
      .done state.reference.reference := by
  have hOne : BinaryPRGWordControllerBooleanResourceLoop.prepare capacity n hCount hC state.reference = .done state.reference := by
    rcases hShort with hNil | ⟨first,hSingle⟩
    · exact BinaryPRGHeapResourceLoop.prepare_nil state.reference (state.certified.choose_spec.2.symm.trans hNil)
    · exact BinaryPRGHeapResourceLoop.prepare_singleton state.reference first (state.certified.choose_spec.2.symm.trans hSingle)
  have hTwo := BinaryPRGWordControllerBooleanResourceLoop.prepare_original capacity n hCount hC state.reference
  rw [hOne] at hTwo
  have hThree := BinaryPRGWordControllerGeneralChoice.prepare_original
    (table capacity.cap capacity.tree n hCount)
    (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference
  rw [← hTwo] at hThree
  exact hThree.symm

theorem runWithTrace_reference (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) :
    (runWithTrace limits hC state).1.reference.reference =
      BinaryGeneralResourceFallback.choose (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
        state.reference.reference := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount),s.active.length ≤ fuel →
      (runWithTrace limits hC s).1.reference.reference =
        BinaryGeneralResourceFallback.choose (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
          s.reference.reference from h state.active.length state le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hSize
      conv_lhs => unfold runWithTrace
      split
      · rename_i first second tail he
        let prepared := pairWithTrace (hC := hC) limits s first second tail he
        have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).outputs :=
          (pairWithTrace_erasure limits s first second tail he).trans
            (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he)
        let selected := selectWithTrace limits s first second tail he prepared.1 hOutputs false
        have hProgress : selected.1.active.length < s.active.length :=
          selectWithTrace_progress limits s first second tail he prepared.1 hOutputs false
        have hLater := ih selected.1.active.length (hProgress.trans_le hSize) selected.1 le_rfl
        change (runWithTrace limits hC selected.1).1.reference.reference = _
        rw [hLater]
        have hSelected : selected.1.reference.reference =
            (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).original.original.select false := by
          change (selectWithTrace limits s first second tail he prepared.1 hOutputs false).1.reference.reference = _
          rw [selectWithTrace_erasure,BinaryPRGHeapResourceLoop.selectWithWork_reference,
            BinaryPRGWordControllerBooleanResourceLoop.Choice.select_original,
            BinaryPRGWordControllerGeneralChoice.Choice.select_original]
        rw [hSelected]
        conv_rhs => unfold BinaryGeneralResourceFallback.choose
        conv_rhs => unfold BinaryGeneralResourceFallback.chooseWithPairs
        rw [prepare_original_pair hC s first second tail he]
        rfl
      · rename_i hNoPair
        have hShort : s.active = [] ∨ ∃ first,s.active = [first] := by
          cases hs : s.active with
          | nil => exact Or.inl rfl
          | cons first rest =>
              cases rest with
              | nil => exact Or.inr ⟨first,rfl⟩
              | cons second tail => exact False.elim (hNoPair first second tail hs)
        conv_rhs => unfold BinaryGeneralResourceFallback.choose
        conv_rhs => unfold BinaryGeneralResourceFallback.chooseWithPairs
        rw [prepare_original_short hC s hShort]

theorem runWithTrace_terminal (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) : (runWithTrace limits hC state).1.active.length ≤ 1 := by
  let result := (runWithTrace limits hC state).1
  have h := BinaryGeneralResourceFallback.choose_terminal
    (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference
  rw [← runWithTrace_reference limits hC state] at h
  change result.reference.reference.state.active.length ≤ 1 at h
  rw [BinaryPRGWordControllerBooleanResourceLoop.Certified.reference_state] at h
  simp only [BinaryPRGWordControllerBooleanResourceUpdate.State.reference,List.length_map] at h
  rw [result.certified.choose_spec.2]
  exact h

structure Budget (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) : Prop where
  pair : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail),Inv state →
    usage (pairWithTrace (hC := hC) limits state first second tail he).2 ≤ M
  selected : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs),Inv state →
    usage (selectWithTrace limits state first second tail he outputs hOutputs false).2 ≤ M
  closed : ∀ (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs),Inv state →
    Inv (selectWithTrace limits state first second tail he outputs hOutputs false).1

theorem budget_of_reachable (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ)
    (budget : BinaryPRGHeapLoopLifetimeBudget.ReachableBudget seed limits hC Inv M) : Budget limits hC Inv M := by
  refine ⟨?_,?_,?_⟩
  · intro state first second tail he hInv
    have h := budget.pairCoin state first second tail he seed.cap le_rfl hInv
    dsimp only at h
    omega
  · intro state first second tail he outputs hOutputs hInv
    exact budget.selected state first second tail he outputs hOutputs false hInv
  · intro state first second tail he outputs hOutputs hInv
    exact budget.closed state first second tail he outputs hOutputs false hInv

theorem runWithTrace_invariant (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) (budget : Budget limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state) : Inv (runWithTrace limits hC state).1 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount),Inv s → s.active.length ≤ fuel →
      Inv (runWithTrace limits hC s).1 from h state.active.length state hInv le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hs hSize
      conv_rhs => unfold runWithTrace
      split
      · rename_i first second tail he
        let prepared := pairWithTrace (hC := hC) limits s first second tail he
        have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).outputs :=
          (pairWithTrace_erasure limits s first second tail he).trans
            (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he)
        let selected := selectWithTrace limits s first second tail he prepared.1 hOutputs false
        have hProgress := selectWithTrace_progress limits s first second tail he prepared.1 hOutputs false
        exact ih selected.1.active.length (hProgress.trans_le hSize) selected.1
          (budget.closed s first second tail he prepared.1 hOutputs hs) le_rfl
      · exact hs

theorem runWithTrace_usage (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) (budget : Budget limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state) :
    usage (runWithTrace limits hC state).2 ≤ state.active.length*(2*M+64)+32 := by
  suffices h : ∀ (fuel : ℕ) (s : Finished capacity n hCount),Inv s → s.active.length ≤ fuel →
      usage (runWithTrace limits hC s).2 ≤ fuel*(2*M+64)+32 from h state.active.length state hInv le_rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hs hSize
      conv_lhs => unfold runWithTrace
      split
      · rename_i first second tail he
        let prepared := pairWithTrace (hC := hC) limits s first second tail he
        have hOutputs : prepared.1 = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) s first second tail he).outputs :=
          (pairWithTrace_erasure limits s first second tail he).trans
            (BinaryPRGHeapResourceLoop.pairWithWork_value limits s first second tail he)
        let selected := selectWithTrace limits s first second tail he prepared.1 hOutputs false
        have hPair := budget.pair s first second tail he hs
        have hSelected := budget.selected s first second tail he prepared.1 hOutputs hs
        have hClosed := budget.closed s first second tail he prepared.1 hOutputs hs
        have hProgress := selectWithTrace_progress limits s first second tail he prepared.1 hOutputs false
        change usage prepared.2 ≤ M at hPair
        change usage selected.2 ≤ M at hSelected
        change Inv selected.1 at hClosed
        change selected.1.active.length < s.active.length at hProgress
        have hLater := ih selected.1.active.length (hProgress.trans_le hSize) selected.1 hClosed le_rfl
        let later := runWithTrace limits hC selected.1
        change usage later.2 ≤ selected.1.active.length*(2*M+64)+32 at hLater
        have hw := wrap_usage 32 2 [prepared.2,selected.2,later.2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        have hOne : selected.1.active.length+1 ≤ fuel := by omega
        have hm := Nat.mul_le_mul_right (2*M+64) hOne
        rw [Nat.add_mul,one_mul] at hm
        change usage (wrap 32 2 [prepared.2,selected.2,later.2]) ≤ _
        omega
      · have hw := wrap_usage 16 2 []
        simp only [List.map_nil,List.sum_nil] at hw
        change usage (wrap 16 2 []) ≤ _
        omega

theorem all_prefix (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (Inv : Finished capacity n hCount → Prop) (M : ℕ) (budget : Budget limits hC Inv M)
    (state : Finished capacity n hCount) (hInv : Inv state) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace limits hC state).2 steps ≤ borrowed + n*(2*M+64)+32 ∧
    framePeak ((runWithTrace limits hC state).2.take steps) ≤ n*(2*M+64)+32 := by
  have h := (runWithTrace_usage limits hC Inv M budget state hInv).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (2*M+64) state.active_length_le) 32)
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ h borrowed steps

end Blotto.BinaryPRGHeapLowerLifetime

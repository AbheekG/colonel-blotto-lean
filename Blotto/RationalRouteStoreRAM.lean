import Blotto.TableStoreRAM

/-! The cached route table has a fixed-region RAM initialization/store
program. It refines the retained prepared table with at most 2n record writes.
Word-store/address primitive costs are explicit; native array ownership and
route codecs/complete peak-space composition remain separate. -/

namespace Blotto.RationalTerminalPacking

def routeStoreProgram {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    List (Fin n × GroupRoute i.groups.length) :=
  TableStoreRAM.fillProgram (none, (0 : ℚ)) ++ p.routeAssignments

def runRouteStore {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i)
    (state : TableStoreState n (GroupRoute i.groups.length) β) : TableStoreState n (GroupRoute i.groups.length) β :=
  TableStoreRAM.run p.routeStoreProgram state

theorem runRouteStore_refines {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i)
    (state : TableStoreState n (GroupRoute i.groups.length) β) : (p.runRouteStore state).cells = p.prepareOutput.table.read := by
  unfold runRouteStore routeStoreProgram
  rw [TableStoreRAM.run_append, TableStoreRAM.run_fillProgram]
  let a := FixedArrayTable.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)
  have hInitial : a.read = (fun _ => (none, (0 : ℚ))) := by funext j; exact FixedArrayTable.read_ofFn _ j
  have hp := TableStoreRAM.run_refines_patch p.routeAssignments a state.frame
  rw [hInitial] at hp
  exact congrArg (fun s : TableStoreState n (GroupRoute i.groups.length) β => s.cells) hp

theorem runRouteStore_frame {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i)
    (state : TableStoreState n (GroupRoute i.groups.length) β) : (p.runRouteStore state).frame = state.frame :=
  TableStoreRAM.run_frame p.routeStoreProgram state

theorem routeStoreProgram_length {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    p.routeStoreProgram.length = n + p.routeAssignments.length := by
  rw [routeStoreProgram, List.length_append, TableStoreRAM.fillProgram_length]

theorem routeStoreProgram_writes {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    TableStoreRAM.writeCount p.routeStoreProgram ≤ 2 * n := by
  rw [TableStoreRAM.writeCount_eq, p.routeStoreProgram_length]
  have h := p.routeAssignments_length_le
  omega

theorem routeStoreProgram_words {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) :
    ∀ e ∈ p.routeStoreProgram, routePayloadWordWidth e.2 ≤ routePayloadWidth n s := by
  intro e he
  rw [routeStoreProgram, List.mem_append] at he
  rcases he with he | he
  · rcases List.mem_ofFn.mp he with ⟨j, rfl⟩
    have hZero := rationalWordWidth_of_height ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs)
    change 1 + 0 + rationalWordWidth (0 : ℚ) ≤ 1 + binaryWordWidth (n + 4) + (1 + 2 * s)
    omega
  · exact p.assignmentPayloadWidth_bound D s h hD hB hWidth e he

def routeStoreWordWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (addressPrice : Fin n → ℕ) : ℕ := TableStoreRAM.writeWordWork routePayloadWordWidth addressPrice p.routeStoreProgram

theorem routeStoreWordWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (addressPrice : Fin n → ℕ) (A : ℕ) (hAddress : ∀ j, addressPrice j ≤ A) :
    p.routeStoreWordWork addressPrice ≤ 2 * n * (2 * routePayloadWidth n s + A) := by
  have hp := TableStoreRAM.writeWordWork_bound routePayloadWordWidth addressPrice p.routeStoreProgram
    (routePayloadWidth n s) A (p.routeStoreProgram_words D s h hD hB hs hWidth) hAddress
  have hCount : p.routeStoreProgram.length ≤ 2 * n := by
    rw [← TableStoreRAM.writeCount_eq]
    exact p.routeStoreProgram_writes
  exact hp.trans (Nat.mul_le_mul_right _ hCount)

theorem routeStorePrefix_words {n : ℕ} {i : RationalTerminalLotto n} {β : Type*} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (state : TableStoreState n (GroupRoute i.groups.length) β)
    (hState : ∀ j, routePayloadWordWidth (state.cells j) ≤ routePayloadWidth n s) (steps : ℕ) :
    ∀ j, routePayloadWordWidth ((TableStoreRAM.run (p.routeStoreProgram.take steps) state).cells j) ≤ routePayloadWidth n s :=
  TableStoreRAM.run_words_bound routePayloadWordWidth _ state _ hState
    (fun e he => p.routeStoreProgram_words D s h hD hB hs hWidth e (List.mem_of_mem_take he))

end Blotto.RationalTerminalPacking

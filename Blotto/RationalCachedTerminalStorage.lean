import Blotto.RationalGroupTableConstructionWork
import Blotto.RationalRouteArrayCopyWork

/-! Retained group/route table payloads have an explicit linear word bound.
The patch invariant follows actual writes. This measures these finished tables;
temporary buffers, other live objects and physical peak memory remain separate. -/

namespace Blotto.FixedArrayTable

theorem patch_words_bound {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α)
    (es : List (Fin n × α)) (W : ℕ) (h : ∀ j, words (a.read j) ≤ W)
    (hAssigned : ∀ e ∈ es, words e.2 ≤ W) : ∀ j, words ((a.patch es).read j) ≤ W := by
  induction es generalizing a with
  | nil => exact h
  | cons e rest ih =>
    rw [patch]
    exact ih (a.write e.1 e.2) (a.write_words_bound words W h e.1 e.2 (hAssigned e (by simp)))
      (fun e he => hAssigned e (List.mem_cons_of_mem _ he))

end Blotto.FixedArrayTable

namespace Blotto.RationalTerminalPacking

def cachedGroupPayloadWords {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : ℕ :=
  p.groups.payloadWordSum RationalTerminalLotto.groupEntryPayloadWordWidth

theorem cachedGroupEntryWords_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hWidth : binaryWordWidth D ≤ s)
    (g : Fin i.groups.length) :
    RationalTerminalLotto.groupEntryPayloadWordWidth (p.groups.read g) ≤ RationalTerminalLotto.groupEntryPayloadWidth n s := by
  have hLength : (i.groups.get g).length ≤ n := by
    simpa only [RationalTerminalLotto.partition, Fintype.card_fin] using (i.partition.nodup g).length_le_card
  have hLabels : ((i.groups.get g).map (fun j => binaryWordWidth (j.val + 1))).sum ≤ n * binaryWordWidth (n + 4) := by
    calc
      _ ≤ ((i.groups.get g).map (fun _ => binaryWordWidth (n + 4))).sum :=
        List.sum_le_sum (fun j _ => binaryWordWidth_mono (by omega : j.val + 1 ≤ n + 4))
      _ = (i.groups.get g).length * binaryWordWidth (n + 4) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hLength
  have hTotal := rationalWordWidth_of_height ((h.total_height hD hB g).mono hWidth)
  unfold RationalTerminalLotto.groupEntryPayloadWordWidth RationalTerminalLotto.groupEntryPayloadWidth
  rw [p.members_correct, p.total_correct]
  omega

theorem cachedGroupPayloadWords_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hWidth : binaryWordWidth D ≤ s) :
    p.cachedGroupPayloadWords ≤ 3 * RationalTerminalLotto.groupEntryPayloadWidth n s := by
  have hp := p.groups.payloadWordSum_bound RationalTerminalLotto.groupEntryPayloadWordWidth
    (RationalTerminalLotto.groupEntryPayloadWidth n s) (p.cachedGroupEntryWords_bound D s h hD hB hWidth)
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  exact hp.trans (Nat.mul_le_mul_right _ hCount)

def cachedRoutePayloadWords {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : ℕ :=
  p.prepareOutput.table.payloadWordSum routePayloadWordWidth

theorem cachedRoutePayloadWords_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) : p.cachedRoutePayloadWords ≤ n * routePayloadWidth n s := by
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)
  have hZero := rationalWordWidth_of_height ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs)
  have hInitial : ∀ j, routePayloadWordWidth (initial.read j) ≤ routePayloadWidth n s := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    change 1 + 0 + rationalWordWidth (0 : ℚ) ≤ 1 + binaryWordWidth (n + 4) + (1 + 2 * s)
    omega
  have hPatch := initial.patch_words_bound routePayloadWordWidth p.routeAssignments (routePayloadWidth n s) hInitial
    (p.assignmentPayloadWidth_bound D s h hD hB hWidth)
  exact (initial.patch p.routeAssignments).payloadWordSum_bound routePayloadWordWidth _ hPatch

def cachedTerminalPayloadWords {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : ℕ :=
  p.cachedGroupPayloadWords + p.cachedRoutePayloadWords

def cachedTerminalPayloadBound (n s : ℕ) : ℕ :=
  4 * n * binaryWordWidth (n + 4) + (n + 3) * (1 + 2 * s) + n + 3

theorem cachedTerminalPayloadWords_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) : p.cachedTerminalPayloadWords ≤ cachedTerminalPayloadBound n s := by
  have hp := Nat.add_le_add (p.cachedGroupPayloadWords_bound D s h hD hB hWidth)
    (p.cachedRoutePayloadWords_bound D s h hD hB hs hWidth)
  exact hp.trans_eq (by unfold RationalTerminalLotto.groupEntryPayloadWidth routePayloadWidth cachedTerminalPayloadBound; ring)

end Blotto.RationalTerminalPacking

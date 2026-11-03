import Blotto.WeightedArrayCopyWork
import Blotto.RationalRoutingMetadata

/-! Route-array payload copying retains the option tag, group label and
rational coefficient. Bounds hold for every intermediate actual patch table,
without array exclusivity. Physical pointers/allocator records stay separate. -/

namespace Blotto

def routePayloadWordWidth {m : ℕ} (route : GroupRoute m) : ℕ :=
  1 + (match route.1 with | none => 0 | some g => binaryWordWidth g.val) + rationalWordWidth route.2

namespace RationalTerminalPacking

def routePayloadWidth (n s : ℕ) : ℕ := 1 + binaryWordWidth (n + 4) + (1 + 2 * s)

theorem assignmentPayloadWidth_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hWidth : binaryWordWidth D ≤ s)
    (e : Fin n × GroupRoute i.groups.length) (he : e ∈ p.routeAssignments) :
    routePayloadWordWidth e.2 ≤ routePayloadWidth n s := by
  rcases (p.mem_routeAssignments e).mp he with ⟨g, _, hEq⟩
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hLabel := binaryWordWidth_mono (show g.val ≤ n + 4 by omega)
  have hRatio := rationalWordWidth_of_height ((i.partition.ratio_height_lattice D hD h.1
    (fun j => (i.length_le j).trans hB) (fun g => (i.partition_total_le g).trans hB) e.1 g).mono hWidth)
  change rationalWordWidth (i.length e.1 / i.partition.total g) ≤ 1 + 2 * s at hRatio
  rw [hEq]
  change 1 + binaryWordWidth g.val + rationalWordWidth (i.length e.1 / i.partition.total g) ≤ routePayloadWidth n s
  unfold routePayloadWidth
  omega

def routeArrayCopyWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : ℕ :=
  wordArrayCopyWork routePayloadWordWidth (List.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)) 0 +
    (FixedArrayTable.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)).patchCopyWork
      routePayloadWordWidth p.routeAssignments

def routeArrayCopyBound (n s : ℕ) : ℕ := (4 * n * n + 2 * n) * routePayloadWidth n s

theorem routeArrayCopyBound_mono_fields (s : ℕ) : Monotone (fun n => routeArrayCopyBound n s) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 4)
  unfold routeArrayCopyBound routePayloadWidth
  dsimp only
  gcongr

theorem routeArrayCopyWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) : p.routeArrayCopyWork ≤ routeArrayCopyBound n s := by
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)
  let W := routePayloadWidth n s
  have hZero := rationalWordWidth_of_height ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs)
  have hInitial : ∀ j, routePayloadWordWidth (initial.read j) ≤ W := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    change 1 + 0 + rationalWordWidth (0 : ℚ) ≤ 1 + binaryWordWidth (n + 4) + (1 + 2 * s)
    omega
  have hAssigned : ∀ e ∈ p.routeAssignments, routePayloadWordWidth e.2 ≤ W :=
    fun e he => p.assignmentPayloadWidth_bound D s h hD hB hWidth e he
  have hPatch := initial.patchCopyWork_bound routePayloadWordWidth p.routeAssignments W hInitial hAssigned
  have hPatchN := hPatch.trans (Nat.mul_le_mul_right _ p.routeAssignments_length_le)
  have hConstruct := wordArrayCopyWork_uniform_bound routePayloadWordWidth
    (List.ofFn (fun _ : Fin n => (none, (0 : ℚ)) : Fin n → GroupRoute i.groups.length)) W
    (fun q hq => by
      rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩
      simpa only [initial, FixedArrayTable.read_ofFn] using hInitial j)
  simp only [List.length_ofFn] at hConstruct
  change p.routeArrayCopyWork ≤ (4 * n * n + 2 * n) * W
  unfold routeArrayCopyWork
  exact (Nat.add_le_add hConstruct hPatchN).trans_eq (by ring)

end RationalTerminalPacking
end Blotto

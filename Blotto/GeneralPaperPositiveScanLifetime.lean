import Blotto.GeneralPaperEqualIntegerCallerCapacity

/-! Executed positive scan: loaded comparisons, child results and work records.
Reserving all recursive frames and returned suffixes covers descent/unwind.
This observer is erased and does not execute another probability pass. -/
namespace Blotto.GeneralPaperPositiveScanLifetime
open GeneralPaperPositiveLabelScan (scan positive)
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def labelProfile (A length r : ℕ) : ℕ := length * (1 + binaryWordWidth r + 2 * A) + 32 * A

theorem labels_bound {r : ℕ} (A : ℕ) (items : List (Fin r)) (L : ℕ) (hL : items.length ≤ L) :
    listFootprint A (fun j => natBits j.val) items ≤ labelProfile A L r := by
  have h := GeneralPaperEncodedScalarStorage.list_bound A (1 + binaryWordWidth r)
    (fun j : Fin r => natBits j.val) items (by
      intro j _
      exact Nat.add_le_add_left (binaryWordWidth_mono j.isLt.le) 1)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) _)

def localFoot {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ)
    (j : Fin r) (rest : List (Fin r)) : ℕ :=
  let current := positive model A (weights.read j)
  let child := scan model A weights rest
  let actual := scan model A weights (j :: rest)
  rationalWordWidth (weights.read j) + rationalWordWidth (0 : ℚ) + current.2 +
    fields A [j.val, current.2, child.2, actual.2] + 128 * A

theorem local_bound {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ)
    (j : Fin r) (rest : List (Fin r)) :
    localFoot weights model A j rest ≤ 256 * (scan model A weights (j :: rest)).2 := by
  let current := positive model A (weights.read j)
  let child := scan model A weights rest
  let F := (scan model A weights (j :: rest)).2
  have hF : F = current.2 + child.2 + 64 * (A + binaryWordWidth (j.val + 1) + 1) := rfl
  have hCurrent : rationalWordWidth (weights.read j) + rationalWordWidth (0 : ℚ) + 32 * A + 32 ≤ current.2 := by
    dsimp only [current, positive]
    omega
  have hIndex := Nat.add_le_add_left (binaryWordWidth_mono (Nat.le_succ j.val)) 1
  change natBits j.val ≤ 1 + binaryWordWidth (j.val + 1) at hIndex
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2)
    [j.val, current.2, child.2, F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · omega
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact GeneralPaperNaturalScalarLifetime.counter_word _)
  change fields A _ ≤ 4 * (F + 2 + A) + 32 * A at hFields
  change rationalWordWidth (weights.read j) + rationalWordWidth (0 : ℚ) + current.2 +
    fields A [j.val, current.2, child.2, F] + 128 * A ≤ 256 * F
  omega

def live {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ) : List (Fin r) → ℕ
  | [] => fields A [(scan model A weights []).2] + 64 * A
  | j :: rest => localFoot weights model A j rest +
      listFootprint A (fun i => natBits i.val) (scan model A weights (j :: rest)).1 + live weights model A rest

theorem bounded {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A F L : ℕ)
    (items : List (Fin r)) (hF : (scan model A weights items).2 ≤ F) (hL : items.length ≤ L) :
    live weights model A items ≤ (items.length + 1) * (256 * F + labelProfile A L r + 64 * A) := by
  induction items with
  | nil =>
    have hBase : 32 * A + 32 ≤ F := hF
    have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2) [32 * A + 32] (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega))
    simp only [List.length_singleton, one_mul] at hFields
    simp only [live, scan, List.length_nil, Nat.zero_add, one_mul]
    omega
  | cons j rest ih =>
    have hChild : (scan model A weights rest).2 ≤ F := by
      rw [scan] at hF
      dsimp only at hF
      omega
    have hLocal := (local_bound weights model A j rest).trans (Nat.mul_le_mul_left 256 hF)
    have hSelected : (scan model A weights (j :: rest)).1.length ≤ L := by
      rw [GeneralPaperPositiveLabelScan.data]
      exact (List.length_filter_le _ _).trans hL
    have hOutput := labels_bound A (scan model A weights (j :: rest)).1 L hSelected
    have hRest := ih hChild (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ rest.length) hL)
    simp only [live, List.length_cons]
    nlinarith only [hLocal, hOutput, hRest]

theorem height_bound {r s : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ)
    (items : List (Fin r)) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (weights.read j) s) (hL : items.length ≤ r) :
    live weights model A items ≤ (r + 1) *
      (256 * (r * GeneralPaperPositiveLabelScan.stepBound model A r s + 32 * A + 32) + labelProfile A r r + 64 * A) := by
  have hWork := (GeneralPaperPositiveLabelScan.work model A weights hs h items).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) _) _)
  exact (bounded weights model A _ r items hWork hL).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hL 1))

end Blotto.GeneralPaperPositiveScanLifetime

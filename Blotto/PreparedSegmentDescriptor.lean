import Blotto.FixedArrayTable
import Blotto.RationalSegmentLottery
import Blotto.BinaryWordWidthCore

/-! Eager finite descriptor storage evaluates every weight and endpoint once.
The resulting read closures retain tables rather than formula evaluators.
Logical rational-cell counts do not certify physical allocation or uniqueness. -/

namespace Blotto
open scoped BigOperators

theorem RationalSegmentLottery.eq_of_stored_fields {n k : ℕ} (a b : RationalSegmentLottery n k)
    (hw : a.weight = b.weight) (hP : a.P = b.P) (hQ : a.Q = b.Q) : a = b := by
  cases a
  cases b
  cases hw
  cases hP
  cases hQ
  rfl

structure PreparedSegmentDescriptor {n k : ℕ} (l : RationalSegmentLottery n k) where
  weights : FixedArrayTable k ℚ
  left : FixedArrayTable k (FixedArrayTable n ℚ)
  right : FixedArrayTable k (FixedArrayTable n ℚ)
  weight_correct : ∀ slot, weights.read slot = l.weight slot
  left_correct : ∀ slot j, (left.read slot).read j = l.P slot j
  right_correct : ∀ slot j, (right.read slot).read j = l.Q slot j

namespace PreparedSegmentDescriptor

def prepare {n k : ℕ} (l : RationalSegmentLottery n k) : PreparedSegmentDescriptor l where
  weights := FixedArrayTable.ofFn l.weight
  left := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (l.P slot))
  right := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (l.Q slot))
  weight_correct := FixedArrayTable.read_ofFn _
  left_correct := by intro slot j; rw [FixedArrayTable.read_ofFn, FixedArrayTable.read_ofFn]
  right_correct := by intro slot j; rw [FixedArrayTable.read_ofFn, FixedArrayTable.read_ofFn]

def lottery {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l) : RationalSegmentLottery n k where
  weight := p.weights.read
  P := fun slot => (p.left.read slot).read
  Q := fun slot => (p.right.read slot).read
  nonnegative := by intro slot; rw [p.weight_correct]; exact l.nonnegative slot
  mass := by simp only [p.weight_correct]; exact l.mass

theorem lottery_eq {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l) : p.lottery = l := by
  apply RationalSegmentLottery.eq_of_stored_fields
  · funext slot; exact p.weight_correct slot
  · funext slot j; exact p.left_correct slot j
  · funext slot j; exact p.right_correct slot j

def rationalCells {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l) : ℕ :=
  p.weights.data.size + (∑ slot, (p.left.read slot).data.size) + (∑ slot, (p.right.read slot).data.size)

theorem rationalCells_eq {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l) :
    p.rationalCells = k + 2 * k * n := by
  simp only [rationalCells, p.weights.size, FixedArrayTable.size, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

def payloadBitCost {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l) : ℕ :=
  (∑ slot, rationalWordWidth (p.weights.read slot)) +
    (∑ slot, ∑ j, rationalWordWidth ((p.left.read slot).read j)) +
    (∑ slot, ∑ j, rationalWordWidth ((p.right.read slot).read j))


end PreparedSegmentDescriptor
end Blotto

import Blotto.PlayerSpecificUnorderedThreeSourceCost

/-! Measured sequential segment choice. Each reached conditional
quotient and midpoint coin executes once; only rejection computes the
next remaining mass and recurses. Returns include the exact visit count. -/
namespace Blotto.PlayerSpecificSegmentSelectionExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {slots : ℕ} (root : Candidate) (weights : FixedArrayTable slots Data) (fallback : Fin slots)
    (H : ℕ) (items : List (Fin slots)) (remaining probability next : Data) (blocks : ℕ) (result : Fin slots×ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi],remaining,probability,next]++List.ofFn weights.read)
    ([slots,H,fallback.val,items.length,blocks,result.1.val,result.2,1]++items.map Fin.val)

def select {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) : List (Fin slots) → Data → List (Fin H → Bool) → (Fin slots×ℕ)×ℕ
  | [],remaining,blocks =>
      let result:=(fallback,0)
      (result,price model (frame root weights fallback H [] remaining [] [] blocks.length result))
  | slot::rest,remaining,blocks =>
      let probability:=PlayerSpecificFieldDivisionExecution.run model root.polynomial (weights.read slot) remaining
      let choice:=PlayerSpecificAlgebraicCoinExecution.run model root probability.1 H (blocks.headD (fun _ => false))
      if choice.1 then
        let result:=(slot,1)
        (result,probability.2+choice.2+price model (frame root weights fallback H (slot::rest) remaining probability.1 [] blocks.length result))
      else
        let next:=PlayerSpecificFieldCombination.run true root.polynomial remaining (weights.read slot)
        let tail:=select model root weights fallback H rest next.1 blocks.tail
        let result:=(tail.1.1,tail.1.2+1)
        (result,probability.2+choice.2+price model next.2+tail.2+
          price model (frame root weights fallback H (slot::rest) remaining probability.1 next.1 blocks.length result))

theorem value {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data) (blocks : List (Fin H → Bool)) :
    (select model root weights fallback H items remaining blocks).1=
      PlayerSpecificAlgebraicSegmentSample.select model root weights fallback H items remaining blocks := by
  induction items generalizing remaining blocks with
  | nil => rfl
  | cons slot rest ih =>
    simp only [select,PlayerSpecificFieldDivisionExecution.value,PlayerSpecificAlgebraicCoinExecution.value,
      PlayerSpecificAlgebraicSegmentSample.select]
    split
    · rfl
    · simp only [PlayerSpecificFieldCombination.value,ite_true,ih]

theorem visits {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data) (blocks : List (Fin H → Bool)) :
    (select model root weights fallback H items remaining blocks).1.2 ≤ items.length := by
  rw [value]
  exact PlayerSpecificAlgebraicSegmentSample.select_visits model root weights fallback H items remaining blocks

end Blotto.PlayerSpecificSegmentSelectionExecution

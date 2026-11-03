import Blotto.GeneralPaperIntervalUpdate

/-! Source operation profile of the actual contiguous-range traversal,
including shared-table queries, rounded products, addition and child calls.
This is not a primitive bit-price or complete working-space theorem.
-/
namespace Blotto.GeneralPaperIntervalUpdateWork
open GeneralPaperIntervalCache GeneralPaperIntervalUpdate GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 2500000

def nodeWork (prepared : Prepared) : ℕ :=
  2*prepared.format.columns*(12*(prepared.format.fractionalBits+1)+82)+
    8*prepared.format.fractionalBits+36*(prepared.format.fractionalBits+1)+352

theorem join_work (lambda k leftOffset rightOffset : ℕ)
    (leftMass rightMass : GeneralPaperDyadicFloat.Number) :
    (GeneralPaperCachedMassJoin.recompute (prepare lambda k) leftOffset leftMass rightOffset rightMass).work+48≤nodeWork (prepare lambda k) := by
  have hl := query_work lambda k leftOffset
  have hr := query_work lambda k rightOffset
  have hj := GeneralPaperCachedMassJoin.recompute_work (prepare lambda k) leftOffset rightOffset leftMass rightMass
  unfold nodeWork
  nlinarith

theorem run_work (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ) :
    (run (prepare lambda k) lo hi amount height node start span).work≤
      (run (prepare lambda k) lo hi amount height node start span).visits*nodeWork (prepare lambda k) := by
  have hK : 16≤nodeWork (prepare lambda k) := by unfold nodeWork; omega
  induction height generalizing start span with
  | zero => rw [run.eq_def]; split <;> (try split) <;> dsimp only <;> omega
  | succ height ih =>
    rw [run.eq_def]
    split
    · dsimp only; omega
    · split
      · dsimp only; omega
      · cases node with
        | uniform h level =>
          have hl := ih (.uniform height 0) start (span/2)
          have hr := ih (.uniform height 0) (start+span/2) (span/2)
          have hj := join_work lambda k
            (offset (run (prepare lambda k) lo hi amount height (.uniform height 0) start (span/2)).node)
            (offset (run (prepare lambda k) lo hi amount height (.uniform height 0) (start+span/2) (span/2)).node)
            (mass (prepare lambda k) (run (prepare lambda k) lo hi amount height (.uniform height 0) start (span/2)).node)
            (mass (prepare lambda k) (run (prepare lambda k) lo hi amount height (.uniform height 0) (start+span/2) (span/2)).node)
          dsimp only
          nlinarith
        | branch level cached left right =>
          have hl := ih left start (span/2)
          have hr := ih right (start+span/2) (span/2)
          have hj := join_work lambda k
            (offset (run (prepare lambda k) lo hi amount height left start (span/2)).node)
            (offset (run (prepare lambda k) lo hi amount height right (start+span/2) (span/2)).node)
            (mass (prepare lambda k) (run (prepare lambda k) lo hi amount height left start (span/2)).node)
            (mass (prepare lambda k) (run (prepare lambda k) lo hi amount height right (start+span/2) (span/2)).node)
          dsimp only
          nlinarith

theorem run_work_linear (lambda k : ℕ) (lo hi : ℚ) (amount height : ℕ) (node : Node height) (start span : ℚ)
    (hSpan : 0<span) : (run (prepare lambda k) lo hi amount height node start span).work≤
      (1+4*height)*nodeWork (prepare lambda k) := by
  have he := run_work lambda k lo hi amount height node start span
  have hv := visits_linear (prepare lambda k) lo hi amount height node start span hSpan
  exact he.trans (Nat.mul_le_mul_right (nodeWork (prepare lambda k)) hv)

end Blotto.GeneralPaperIntervalUpdateWork

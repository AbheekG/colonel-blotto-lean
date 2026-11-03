import Blotto.GeneralPaperCircleSweepBitBounds

/-! The priced cursor has the same geometric invariants as the actual
arithmetic sweep. These proofs bound reached operands and total advances;
they are erased and are not assumptions supplied to the native draw. -/
namespace Blotto.GeneralPaperCircleSweepBitInvariant
open GeneralPaperCircleSweepBits
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem state (price : ℕ → ℕ) (A R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ)) (a next : ℕ) (ha : a<2*R) (hn : next=(a+1)*(2*W))
    (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W)
    (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1))
    (hLower : ∀ arc∈arcs,a*(2*W)<2*(t+arc.1)+1) :
    let x := (run price A R W t arcs a next).1
    x.bin<2*R ∧ x.next=(x.bin+1)*(2*W) ∧ x.advances<2*R := by
  dsimp only
  rw [data]
  dsimp only [observe]
  have hBin := (GeneralPaperCircleCursorSweep.correct R W t hR hW ht arcs a next ha hn hRanges hOrder hLower).2
  have hNext := GeneralPaperCircleCursorSweep.next_invariant R W t arcs a next hn
  have hAdv := GeneralPaperCircleCursorSweep.bin_eq R W t arcs a next
  exact ⟨hBin,hNext,by omega⟩

theorem advanced (price : ℕ → ℕ) (A R W t offset : ℕ) (hR : 0<R) (hW : 0<W)
    (a next : ℕ) (hu : t+offset<2*(R*W)) (hn : next=(a+1)*(2*W))
    (hLower : a*(2*W)<2*(t+offset)+1) :
    let x := (GeneralPaperCircleBinAdvancePrice.run price A (2*W) (2*(t+offset)+1) (2*R) a next).1
    x.bin<2*R ∧ x.next=(x.bin+1)*(2*W) ∧ x.bin*(2*W)<2*(t+offset)+1 ∧ x.advances≤2*R := by
  dsimp only
  rw [GeneralPaperCircleBinAdvancePrice.data]
  exact ⟨(GeneralPaperCircleOddGeometry.cursor_bin R W (t+offset) a next hR hW hu hn hLower).2,
    GeneralPaperCircleBinAdvance.next_invariant _ _ _ _ _ hn,
    GeneralPaperCircleBinAdvance.lower _ _ _ _ _ hn hLower,
    GeneralPaperCircleBinAdvance.advances_le _ _ _ _ _⟩

end Blotto.GeneralPaperCircleSweepBitInvariant

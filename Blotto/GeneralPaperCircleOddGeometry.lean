import Blotto.GeneralPaperCircleBinAdvancePrice

/-! Odd endpoint coordinates avoid every even quantile boundary. The
arithmetic cursor returns the unrolled leftmost bin, and the same bin
remains below 2R over the whole translated circle. -/
namespace Blotto.GeneralPaperCircleOddGeometry
open GeneralPaperCircleBinAdvance
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem not_boundary (u W b : ℕ) : 2*u+1≠b*(2*W) := by
  intro h
  have he : 2*u+1=2*(b*W) := h.trans (by ring)
  omega

theorem gap_quotient (W u a : ℕ) (_hW : 0<W) (hLower : a*(2*W)<2*u+1)
    (hUpper : 2*u+1<(a+1)*(2*W)) : a=u/W := by
  have hl : a*W≤u := by nlinarith only [hLower]
  have hu : u<(a+1)*W := by nlinarith only [hUpper]
  exact (Nat.div_eq_of_lt_le hl hu).symm

theorem cursor_bin (R W u a next : ℕ) (_hR : 0<R) (hW : 0<W) (hu : u<2*(R*W))
    (hNext : next=(a+1)*(2*W)) (hLower : a*(2*W)<2*u+1) :
    (run (2*W) (2*u+1) (2*R) a next).bin=u/W ∧ (run (2*W) (2*u+1) (2*R) a next).bin<2*R := by
  have hCap : 2*u+1≤next+(2*R)*(2*W) := by nlinarith only [hu,Nat.zero_le next]
  have hg := gap (2*W) (2*u+1) (2*R) a next hNext hLower hCap (not_boundary u W)
  have hq := gap_quotient W u _ hW hg.1 hg.2
  refine ⟨hq,?_⟩
  rw [hq]
  apply (Nat.div_lt_iff_lt_mul hW).mpr
  nlinarith only [hu]

end Blotto.GeneralPaperCircleOddGeometry

import Blotto.PlayerSpecificSegmentInterpolationFrameCost

/-! Interpolation widths derive from original endpoint/scalar heights
and finite dimensions. These bounds are not executing parameters. -/
namespace Blotto.PlayerSpecificSegmentInterpolationSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (T : ℕ) : ℕ := 2*T+3
def scalarHeight (T : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.step (base T)
def height (N slots T : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (base T)+N+slots+10
def coefficient : ℕ := 4*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3+26

theorem base_lower (T : ℕ) : T≤base T ∧ 1≤base T := by dsimp [base]; omega

theorem lower (N slots T : ℕ) : base T≤height N slots T ∧ scalarHeight T≤height N slots T ∧
    N≤height N slots T ∧ slots≤height N slots T ∧ 1≤height N slots T := by
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 3 (base T)
  have hscalar:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono (base T) (by decide : 1≤3)
  change PlayerSpecificAlgebraicHeightEnvelope.step (base T)≤PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (base T) at hscalar
  dsimp [height,scalarHeight]
  omega

theorem linear (N slots T : ℕ) : height N slots T+16≤coefficient*(T+N+slots+1) := by
  let A:=(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3
  let V:=PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (base T)
  have hv : V+1≤A*(base T+1) := PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 3 (base T)
  have hb : base T+1≤4*(T+1) := by dsimp [base]; omega
  have hV : V+1≤4*A*(T+1) := hv.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left A hb)
  change V+N+slots+10+16≤(4*A+26)*(T+N+slots+1)
  nlinarith only [hV,Nat.zero_le (A*N),Nat.zero_le (A*slots),Nat.zero_le T,Nat.zero_le N,Nat.zero_le slots]

theorem transfer (C B N slots T U : ℕ) (hU : U+16≤B*(T+N+slots+1)) :
    C*(N+1)*(U+16)^3≤(C*B^3)*(N+1)*(T+N+slots+1)^3 := by
  exact (Nat.mul_le_mul_left (C*(N+1)) (Nat.pow_le_pow_left hU 3)).trans_eq (by ring)

end Blotto.PlayerSpecificSegmentInterpolationSizes

import Blotto.GeneralPaperEqualFirstBitDispatch

/-! Short rational fields for the actual c=256 rounded source. Midpoint
precision stays k+5; source-size comparisons alone may use old k+1 bounds. -/
namespace Blotto.GeneralPaperEqualFirstHeights
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualPreparedCache (Prepared)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem lottery_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1) :
    (lottery (rounded bits model W k values v hv) small).HeightAt
      (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) := by
  let D := (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
  have hD : 0 < D := (GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv).1
  have h := GeneralPaperEqualNativeSampler.unit_spec_height (rounded bits model W k values v hv) small D hD
    (lattice bits model W k values v hv)
  have hm : 2*binaryWordWidth D+1 ≤ GeneralPaperEqualNativeSampler.fieldHeight n (k+1) := by
    have hw := denominator_word bits model W k values v hv
    unfold GeneralPaperEqualNativeSampler.fieldHeight
    dsimp only [D] at *
    omega
  exact (h.mono hm).lottery (by unfold GeneralPaperEqualNativeSampler.fieldHeight; omega)
    (terminal (rounded bits model W k values v hv) small).groups_count

theorem route_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : Prepared (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small)) (j : Fin n) :
    RationalHeight (p.routes.table.read j).2 (binaryWordWidth n+k+10) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
  have hD : 0 < D := (GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv).1
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) := fun j =>
    (lattice bits model W k values v hv j).int_mul 2
  exact (p.routes.coefficient_height_lattice D hD hL small i.partition_total_le j).mono
    (denominator_word bits model W k values v hv)

theorem categorical_denominator {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : Prepared (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small)) :
    binaryWordWidth p.D ≤ 3670016*(binaryWordWidth n+k+11)+1 := by
  have h := GeneralPaperEqualPreparedCache.denominator_word p (lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (GeneralPaperEqualNativeSampler.segmentHeight n (k+1))
    (GeneralPaperEqualNativeCache.compact_count (rounded bits model W k values v hv) small).2
  have hs := GeneralPaperEqualNativeCache.segment_height_bound n (k+1)
  nlinarith only [h, hc, hs]

theorem rejection_range {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded bits model W k values v hv).weight j ≤ 1)
    (p : Prepared (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small)) :
    p.rangeBits ≤ 3670016*(binaryWordWidth n+k+11)+1 := by
  have h := GeneralPaperEqualPreparedCache.rangeBits_bound p (lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (GeneralPaperEqualNativeSampler.segmentHeight n (k+1))
    (GeneralPaperEqualNativeCache.compact_count (rounded bits model W k values v hv) small).2
  have hs := GeneralPaperEqualNativeCache.segment_height_bound n (k+1)
  nlinarith only [h, hc, hs]

theorem midpoint_count (k : ℕ) : 2^(k+5) = 32*2^k := by
  rw [pow_add]
  norm_num
  ring

end Blotto.GeneralPaperEqualFirstHeights

import Blotto.GeneralPaperEqualRationalCopy

/-! Copy every retained rational/integer prepared-cache field at the target
width. Scalar controls and the sole original budget are copied explicitly.
No rounding, grouping, formula, denominator or midpoint power is rebuilt. -/
namespace Blotto.GeneralPaperEqualPreparedCopy
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (compact count)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) :=
  let routes := GeneralPaperEqualRationalCopy.routes S A source.routes
  let segments := GeneralPaperEqualRationalCopy.segments S A source.segments
  let counts := GeneralPaperScalarTableCopy.run S A natBits source.counts
  let denominator := GeneralPaperReferenceCopy.scalar S A natBits source.D
  let width := GeneralPaperReferenceCopy.scalar S A natBits source.rangeBits
  let bits := GeneralPaperReferenceCopy.scalar S A natBits source.midpointBits
  let midpoint := GeneralPaperReferenceCopy.scalar S A natBits source.midpointCount
  let budget := GeneralPaperReferenceCopy.scalar S A rationalWordWidth source.budget
  let actual : GeneralPaperEqualPreparedCache.Prepared G l :=
    ⟨routes.1,segments.1,denominator.1,(by
      change source.D = _
      rw [GeneralPaperEqualRationalCopy.segments_data]
      exact source.D_correct),counts.1,(by
      intro i
      rw [GeneralPaperScalarTableCopy.data,GeneralPaperEqualRationalCopy.segments_data]
      exact source.counts_correct i),width.1,source.rangeBits_correct,bits.1,midpoint.1,source.midpointCount_correct,budget.1⟩
  (actual,routes.2 + segments.2 + counts.2 + denominator.2 + width.2 + bits.2 + midpoint.2 + budget.2 + 128 * (S + A + 1))

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) : (run S A source).1 = source :=
  GeneralPaperEqualCompactedCache.unique _ _ rfl rfl

def price (S A n m r s c d P b : ℕ) : ℕ :=
  GeneralPaperEqualRationalCopy.routesPrice S A n m c +
    GeneralPaperEqualRationalCopy.segmentsPrice S A m r (1 + 2 * s) +
    GeneralPaperScalarTableCopy.price S A r (r * (1 + d)) + 4 * P + b + 288 * (S + A + 1)

theorem work {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (hl : (compact l).HeightAt s) (hc : ∀ j,RationalHeight (source.routes.table.read j).2 c)
    (hd : ∀ i,binaryWordWidth (source.counts.read i) ≤ d)
    (hp : ∀ x ∈ [source.D,source.rangeBits,source.midpointBits,source.midpointCount],natBits x ≤ P) :
    (run S A source).2 ≤ price S A n m (count l) s c d P (rationalWordWidth source.budget) := by
  have hRoutes := GeneralPaperEqualRationalCopy.routes_work S A source.routes hc
  have hSegments := GeneralPaperEqualRationalCopy.segments_work S A source.segments
    (fun i => by rw [source.segments.weight_correct]; exact rationalWordWidth_of_height (hl.1 i))
    (fun i j => by rw [source.segments.left_correct]; exact rationalWordWidth_of_height (hl.2 i j).1)
    (fun i j => by rw [source.segments.right_correct]; exact rationalWordWidth_of_height (hl.2 i j).2)
  have hCounts := GeneralPaperScalarTableCopy.bounded_work S A (1 + d) natBits source.counts
    (fun i => Nat.add_le_add_left (hd i) 1)
  have hD := hp source.D (by simp)
  have hR := hp source.rangeBits (by simp)
  have hK := hp source.midpointBits (by simp)
  have hN := hp source.midpointCount (by simp)
  dsimp only [run,price,GeneralPaperReferenceCopy.scalar]
  omega

theorem charged {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) :
    preparedFoot A (run S A source).1 ≤ 64 * (run S A source).2 := by
  have hr := GeneralPaperEqualRationalCopy.routes_charged S A source.routes
  have hs := GeneralPaperEqualRationalCopy.segments_charged S A source.segments
  have hc := GeneralPaperScalarTableCopy.charged S A natBits source.counts
  dsimp only [run,preparedFoot,GeneralPaperReferenceCopy.scalar]
  unfold fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  nlinarith

end Blotto.GeneralPaperEqualPreparedCopy

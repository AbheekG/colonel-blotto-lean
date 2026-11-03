import Blotto.GeneralPaperEqualDispatchContract

/-! Uniqueness of the retained bit data. Erased correctness fields fix the
Boolean cache and the prepared sampler once precision/budget are fixed.
This transfers native resource theorems to actual selected grouped returns. -/
namespace Blotto.GeneralPaperEqualBitCanonical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem word_unique {w : ℕ} (a b : FixedBinaryWord w) (h : a.value = b.value) : a = b := by
  have he := BinaryBorrowWord.littleValue_injective a.bits b.bits (a.size.trans b.size.symm) h
  rcases a with ⟨bitsA,sizeA⟩
  rcases b with ⟨bitsB,sizeB⟩
  dsimp only at he
  subst bitsB
  rfl

theorem boolean_unique {n m r : ℕ} {G : RationalProportionalGroups n m}
    {l : RationalSegmentLottery m r} {p : GeneralPaperEqualPreparedCache.Prepared G l}
    (a b : GeneralPaperEqualBooleanCache.Cache p) : a = b := by
  have hDen := word_unique a.denominator b.denominator
    (a.denominator_value.trans b.denominator_value.symm)
  have hRows := a.rows_correct.trans b.rows_correct.symm
  have hA : a.ruler = List.replicate p.rangeBits () := List.eq_replicate_iff.mpr
    ⟨a.ruler_length, fun _ _ => Subsingleton.elim _ _⟩
  have hB : b.ruler = List.replicate p.rangeBits () := List.eq_replicate_iff.mpr
    ⟨b.ruler_length, fun _ _ => Subsingleton.elim _ _⟩
  have hRuler := hA.trans hB.symm
  cases a
  cases b
  cases hDen
  cases hRows
  cases hRuler
  rfl

theorem sampler_canonical {n m r : ℕ} {G : RationalProportionalGroups n m}
    {l : RationalSegmentLottery m r} (a : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (k : ℕ) (budget : ℚ) (hk : a.exponent = k) (hB : a.prepared.budget = budget) :
    a = GeneralPaperEqualStoredBitSampler.prepare
      (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget) k rfl := by
  have hMid : a.prepared.midpointBits = k + 5 := a.exponent_correct.trans (congrArg (fun k => k + 5) hk)
  have hPrepared := GeneralPaperEqualCompactedCache.unique a.prepared
    (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget) hMid hB
  cases a with
  | mk p c exponent hExp address hAddress =>
    dsimp only at hk hPrepared
    cases hk
    cases hPrepared
    have hCache := boolean_unique c (GeneralPaperEqualBooleanCache.prepare _)
    cases hCache
    cases hAddress
    rfl

theorem pure_coordinates {n : ℕ} (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (h : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) (j : Fin n) :
    row.allocation j = if j = chosen then budget else 0 := by
  have hj := congrFun h j
  change (row.allocation j : ℝ) = _ at hj
  by_cases he : j = chosen
  · simp only [PureBoundaryEquilibria.vertex, he, ite_true] at hj ⊢
    exact_mod_cast hj
  · simp only [PureBoundaryEquilibria.vertex, he, ite_false] at hj ⊢
    exact_mod_cast hj

end Blotto.GeneralPaperEqualBitCanonical

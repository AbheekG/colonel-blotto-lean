import Blotto.GeneralPaperEqualRealContract

/-! The smaller real cache owns exactly routes, segment tables, midpoint
controls and budget. Its retained bit description is bounded by the checked
full sampler description; no bit-only payload is added by this analysis. -/
namespace Blotto.GeneralPaperEqualRealDescription
open GeneralPaperEqualRealCache (Cache project)
open GeneralPaperEqualRetainedStorage (routeFoot segmentFoot)
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperEncodedScalarStorage (fields)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def footprint {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (W : ℕ) (p : Cache G l) : ℕ :=
  arrayFootprint W (routeFoot W) p.routes.table + segmentFoot W p.segments +
    fields W [p.midpointBits, p.midpointCount] + rationalWordWidth p.budget + 64 * W

theorem projection_bound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (W : ℕ) (s : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    footprint W (project s.prepared) ≤ GeneralPaperEqualRetainedStorage.footprint W s := by
  simp only [footprint, project, GeneralPaperEqualRetainedStorage.footprint,
    GeneralPaperEqualRetainedStorage.preparedFoot, fields, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

theorem prepared {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded false model 1 k values v hv).weight j ≤ 1)
    (budget : ℚ) :
    let p := (GeneralPaperEqualRealPreparation.run model k values v hv small budget).1
    let b := rationalWordWidth budget
    let R := GeneralPaperEqualDescriptionRates.reference n k b
    footprint R p ≤ GeneralPaperEqualDescriptionRates.paperBound n k b ∧ footprint R p < 2 ^ R := by
  dsimp only
  rw [GeneralPaperEqualRealPreparation.data]
  have h := projection_bound (GeneralPaperEqualDescriptionRates.reference n k (rationalWordWidth budget))
    (GeneralPaperEqualStoredBitSampler.native false model 1 k values v hv small budget)
  have hd := GeneralPaperEqualDescriptionRates.native_paper_description false model 1 k values v hv small budget
  exact ⟨h.trans hd.1, h.trans_lt hd.2⟩

theorem accuracy {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded false model 1
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let p := (GeneralPaperEqualRealPreparationRates.run model eps values v hv small budget).1
    let R := GeneralPaperEqualDescriptionRates.reference n k (rationalWordWidth budget)
    footprint R p ≤ GeneralPaperEqualDescriptionRates.paperBound n (binaryWordWidth ⌈eps⁻¹⌉₊) (rationalWordWidth budget) ∧
      footprint R p < 2 ^ R := by
  have h := prepared model (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
  have ha := GeneralPaperDyadicAccuracy.prepare_work eps
  have he := GeneralPaperDyadicAccuracy.prepare_work_exact eps
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by omega
  exact ⟨h.1.trans (GeneralPaperEqualDescriptionRates.paperBound_mono n hk le_rfl), h.2⟩

end Blotto.GeneralPaperEqualRealDescription

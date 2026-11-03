import Blotto.GeneralPaperMeasuredUnequalStoragePhases

/-! Actual counter lengths are already covered by the initializer and
native frames. This avoids calibrating addresses from numerical time. -/
namespace Blotto.GeneralPaperMeasuredUnequalCounterCapacity
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperEncodedScalarStorage (fields natBits)
open GeneralPaperMeasuredUnequalStorageFrame (initial child)
open GeneralPaperMeasuredUnequalStoragePhases (word word_eq)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem bits_mono (a b : ℕ) (h : a ≤ b) : natBits a ≤ natBits b :=
  Nat.add_le_add_left (binaryWordWidth_mono h) 1

theorem bits_add (a b : ℕ) : natBits (a + b) ≤ natBits a + natBits b := by
  have h := GeneralPaperReferenceScaling.word_add a b
  unfold natBits
  omega

theorem member_fields (W z : ℕ) (xs : List ℕ) (hz : z ∈ xs) : natBits z ≤ fields W xs := by
  have hm : natBits z ∈ xs.map natBits := List.mem_map.mpr ⟨z, hz, rfl⟩
  have hs := List.single_le_sum (fun a (_ : a ∈ xs.map natBits) => Nat.zero_le a) (natBits z) hm
  unfold fields
  omega

def initProfile (model : RationalCostModel) (W K : ℕ) (p : Problem) : ℕ :=
  GeneralPaperMixedInitializerPhases.profile model W K
    (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p))

theorem initial_field (model : RationalCostModel) (K : ℕ) (p : Problem) (hW : 1 ≤ word model K p)
    (z : ℕ) (hz : z ∈ GeneralPaperMixedInitializerControls.values model 1 K
      (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p))) :
    natBits z ≤ initProfile model (word model K p) K p := by
  have h := GeneralPaperMixedInitializerPhases.all_phases model (word model K p) 1 K hW
    (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) .returned
  have hf := member_fields (word model K p) z _ hz
  dsimp only [GeneralPaperMixedInitializerPhases.window, GeneralPaperMixedInitializerControls.controls] at h
  unfold initProfile
  omega

theorem initial_return_field (model : RationalCostModel) (K : ℕ) (p : Problem) (hW : 1 ≤ word model K p)
    (z : ℕ) (hz : z ∈ [(initial model K p).1.1.exponent, (initial model K p).1.2, (initial model K p).2]) :
    natBits z ≤ initProfile model (word model K p) K p := by
  have h := GeneralPaperMixedInitializerPhases.all_phases model (word model K p) 1 K hW
    (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) .returned
  have hf := member_fields (word model K p) z _ hz
  have hr := GeneralPaperMixedInitializerPhases.original_return_fields model (word model K p) 1 K
    (GeneralPaperMeasuredReferenceGrowth.original p)
  dsimp only [GeneralPaperMixedInitializerPhases.window, GeneralPaperMixedInitializerPhases.component] at h
  change fields (word model K p) [(initial model K p).1.1.exponent, (initial model K p).1.2,
    (initial model K p).2] + 64 * word model K p + 2 * word model K p = _ at hr
  unfold initProfile
  omega

theorem full_work_bits {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    natBits (GeneralPaperClosedStrategyDriver.bit model (cal.word p) (cal.word p) (cal.word p)
      p.words p.values p.selector p.correct p.budget p.budget_valid).2 ≤
        GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p := by
  let W := cal.word p
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
  let cS := GeneralPaperNativeSourceTimeRates.initialCursor o.reduced.m k o.Qv
  let cD : GeneralPaperClosedParsedStorage.DescriptionCursor model W k p.values p.selector p.correct :=
    ⟨0, Nat.zero_le _, 0, Nat.zero_le _, 0, Nat.zero_le _, 0, 0, none⟩
  let raw := GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid
  have hf := member_fields W (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector
    p.correct p.budget p.budget_valid).2 (GeneralPaperClosedStrategyConstructionStorage.controls W raw.1 raw.2) (by
      simp only [GeneralPaperClosedStrategyConstructionStorage.controls, GeneralPaperClosedStrategyDriver.bit]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  have h := (GeneralPaperNativeReferenceEnlargement.bit_contract hg p W (cal.above p) cS cD).1
  have hc : fields W (GeneralPaperClosedStrategyConstructionStorage.controls W raw.1 raw.2) ≤
      GeneralPaperClosedStrategyConstructionStorage.window W raw.1 raw.2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct
          p.budget p.budget_valid cS cD) := by unfold GeneralPaperClosedStrategyConstructionStorage.window; omega
  exact (hf.trans hc).trans h

theorem child_work_bits {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    natBits (child model K p).2 ≤ GeneralPaperNativeResourceReferenceGrowth.reserve model C d (cal.word p) p := by
  have h := GeneralPaperClosedParsedPreparation.work_le model (word model K p) (word model K p)
    (word model K p) (initial model K p).1.1 p.values p.selector p.correct p.budget p.budget_valid
  change (child model K p).2 ≤ (GeneralPaperClosedStrategyDriver.bit model (word model K p) (word model K p)
    (word model K p) p.words p.values p.selector p.correct p.budget p.budget_valid).2 at h
  rw [word_eq cal K hWord p] at h
  exact (bits_mono _ _ h).trans (full_work_bits hg cal p)

end Blotto.GeneralPaperMeasuredUnequalCounterCapacity

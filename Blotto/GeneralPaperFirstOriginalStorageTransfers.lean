import Blotto.GeneralPaperFirstOriginalStorageContract

/-! Fixed-factor transfer of complete equal/native retained data to the
common original-input space and description powers. -/
namespace Blotto.GeneralPaperFirstOriginalStorageTransfers
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters GeneralPaperOriginalHeadlineTransfers
open GeneralPaperFirstOriginalStorageContract
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

theorem equal_resources (model : RationalCostModel) (K Ct dt Cs ds Cd dd S s D e : ℕ)
    (p : Input) (hN : p.n ≠ 1) (hB : p.budget = 1)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed
      (GeneralPaperFirstStoredPipeline.width model 1 K (equalInput model p)))
    (h : GeneralPaperFirstEqualFullContract.Resources model K Ct dt Cs ds Cd dd p output)
    (hS : Cs ≤ S) (hs : ds ≤ s) (hD : Cd ≤ D) (he : dd ≤ e) :
    Contract model K S s D e p (.equal _ output) := by
  have hSpace : 0 ≤ spaceScale p := (Nat.cast_nonneg (inputSize p)).trans (space_ge_input p)
  have hDesc : 0 ≤ descriptionScale p := (Nat.cast_nonneg (inputSize p)).trans (description_ge_input p)
  refine .equal hN hB output ?_ ?_
  · obtain ⟨keys, hSupport, hBound⟩ := h.description
    exact ⟨keys, hSupport, raise p (descriptionScale p) hDesc _ Cd D dd e hD he
      (equal_scaled_bound model p _ (description_ge_input p) _ Cd dd hBound)⟩
  · intro phase
    obtain ⟨keys, hSupport, hBound, hCapacity⟩ := h.space phase
    exact ⟨keys, hSupport, raise p (spaceScale p) hSpace _ Cs S ds s hS hs
      (equal_scaled_bound model p _ (space_ge_input p) _ Cs ds hBound), hCapacity⟩

theorem native_description (model : RationalCostModel) (K Ad D e : ℕ)
    (p : Input) (hStrict : p.budget < 1) (output : GeneralPaperClosedStrategyDriver.Prepared p.n)
    (h : GeneralPaperMeasuredUnequalDispatchHeadlines.DescriptionBound model
      (GeneralPaperMeasuredReferenceGrowth.word model K (unequalInput p hStrict)) Ad (unequalInput p hStrict) output)
    (hD : Ad * 16 ≤ D) (he : 2 ≤ e) :
    NativeDescription (GeneralPaperMeasuredReferenceGrowth.word model K (unequalInput p hStrict))
      (unequalInput p hStrict) output ((D : ℚ) * descriptionScale p * (logarithm p : ℚ) ^ e) := by
  have hDesc : 0 ≤ descriptionScale p := (Nat.cast_nonneg (inputSize p)).trans (description_ge_input p)
  obtain ⟨sampler, hSampler, hFoot, hPrepared⟩ := h
  refine ⟨sampler, hSampler, ?_, ?_⟩
  · have ht := native_description_bound p hStrict _ Ad 2 hFoot
    norm_num only [show (2 : ℕ) ^ 2 = 4 by decide] at ht
    have hd : Ad * 4 * 4 ≤ D := by omega
    exact raise p _ hDesc _ (Ad * 4 * 4) D 2 e hd he ht
  · have ht := native_description_bound p hStrict _ Ad 2 hPrepared
    norm_num only [show (2 : ℕ) ^ 2 = 4 by decide] at ht
    have hd : Ad * 4 * 4 ≤ D := by omega
    exact raise p _ hDesc _ (Ad * 4 * 4) D 2 e hd he ht

theorem one_resources (model : RationalCostModel) (K S s D e : ℕ) (p : Input) (hN : p.n = 1)
    (hS : 32768 ≤ S) (hD : 1024 ≤ D) : Contract model K S s D e p (GeneralPaperAllBranchBitDispatch.one p hN).1 := by
  have hSpace : 0 ≤ spaceScale p := (Nat.cast_nonneg (inputSize p)).trans (space_ge_input p)
  have hDesc : 0 ≤ descriptionScale p := (Nat.cast_nonneg (inputSize p)).trans (description_ge_input p)
  exact .oneField hN
    (raise p _ hDesc _ 1024 D 0 e hD (Nat.zero_le _) (GeneralPaperOneFieldOriginalStorage.description_headline p))
    (fun phase => raise p _ hSpace _ 32768 S 0 s hS (Nat.zero_le _)
      (GeneralPaperOneFieldOriginalStorage.space_headline model K p hN phase))

end Blotto.GeneralPaperFirstOriginalStorageTransfers

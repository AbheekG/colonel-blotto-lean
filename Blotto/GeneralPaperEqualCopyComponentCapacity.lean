import Blotto.GeneralPaperEqualNativeCopyLifetimeRates

/-! One coefficient simultaneously covers all previously joined preparation
phases, native grouped-copy windows and pure scalar-row copy windows. The
new selected-copy wrapper/parent join is still a separate obligation. -/
namespace Blotto.GeneralPaperEqualCopyComponentCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

noncomputable def profile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPreparationResources.profile model W K p +
    GeneralPaperEqualNativeCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget) +
    GeneralPaperEqualPureCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget)

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hOld := GeneralPaperEqualSelectedPreparationCapacity.profile_rate model hFast K
  have hGrouped := GeneralPaperEqualNativeCopyLifetimeRates.profile_rate model K
  have hPure := GeneralPaperEqualPureCopyRates.profile_rate model K
  dsimp only [profile]
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),binaryWordWidth (profile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Co,ho⟩ := GeneralPaperEqualSelectedPreparationCapacity.uniform_word_growth model hFast
  obtain ⟨Cg,hg⟩ := GeneralPaperEqualNativeCopyLifetimeRates.uniform_word_growth model
  obtain ⟨Cp,hp⟩ := GeneralPaperEqualPureCopyRates.uniform_word_growth model
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model,1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hOld : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedPreparationResources.profile model a.reference a.coefficient a.input) L :=
    ⟨Co,fun a => ho a.input a.reference a.coefficient⟩
  have hGrouped : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualNativeCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cg,fun a => hg a.input a.reference a.coefficient⟩
  have hPure : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualPureCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cp,fun a => hp a.input a.reference a.coefficient⟩
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      profile model a.reference a.coefficient a.input) L := by
    dsimp only [profile]
    fun_prop
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ p : Input model,profile model (word K p) K p < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (profile model) logarithm logarithm_positive
    (uniform_word_growth model hFast)

end Blotto.GeneralPaperEqualCopyComponentCapacity

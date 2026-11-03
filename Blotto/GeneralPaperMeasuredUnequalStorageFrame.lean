import Blotto.GeneralPaperEnlargedReferenceSpace

/-! Actual outer unequal-preparation fields and retained initializer/input
owners. Numerical work counters are charged by their encoded lengths. -/
namespace Blotto.GeneralPaperMeasuredUnequalStorageFrame
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperUniformResourceGrowth
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperEncodedScalarStorage (fields natBits)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def initial (model : RationalCostModel) (K : ℕ) (p : Problem) :=
  GeneralPaperOriginalMeasuredReference.prepare model 1 K (GeneralPaperMeasuredReferenceGrowth.original p)

def child (model : RationalCostModel) (K : ℕ) (p : Problem) :=
  let i := initial model K p
  GeneralPaperClosedParsedPreparation.run model i.1.2 i.1.2 i.1.2 i.1.1
    p.values p.selector p.correct p.budget p.budget_valid

def values (model : RationalCostModel) (K : ℕ) (p : Problem) : List ℕ :=
  let i := initial model K p
  let c := child model K p
  let branch := GeneralPaperAllBranchBitDispatch.branchPrice model (GeneralPaperMeasuredReferenceGrowth.original p)
  [p.n, 1, K, i.1.1.exponent, i.1.2, i.2, c.2, i.2 + c.2,
    64 * (1 + i.1.2 + 1), i.2 + c.2 + 64 * (1 + i.1.2 + 1), branch,
    i.2 + c.2 + 64 * (1 + i.1.2 + 1) + branch]

noncomputable def cap (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (K : ℕ) (p : Problem) : ℕ :=
  p.n + K + exponent p + cal.word p + GeneralPaperMeasuredUnequalDispatchHeadlines.price model C d cal K p + 1

noncomputable def controlProfile (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d)
    (K : ℕ) (p : Problem) : ℕ := 12 * (natBits (cap model C d cal K p) + cal.word p) + 416 * cal.word p

theorem values_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    ∀ z ∈ values model K p, z ≤ cap model C d cal K p := by
  have hWork := Nat.add_le_add_right (GeneralPaperMeasuredUnequalTime.work_bound hg cal K hWord p)
    (GeneralPaperAllBranchBitDispatch.branchPrice model (GeneralPaperMeasuredReferenceGrowth.original p))
  change (initial model K p).2 + (child model K p).2 + 64 * (1 + (initial model K p).1.2 + 1) +
    GeneralPaperAllBranchBitDispatch.branchPrice model (GeneralPaperMeasuredReferenceGrowth.original p) ≤
      GeneralPaperMeasuredUnequalDispatchHeadlines.price model C d cal K p at hWork
  have hk : (initial model K p).1.1.exponent = exponent p := rfl
  have hw : (initial model K p).1.2 = cal.word p :=
    (GeneralPaperOriginalMeasuredReference.word model 1 K _).trans (congrFun hWord p).symm
  intro z hz
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold cap
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem controls_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    fields (cal.word p) (values model K p) + 384 * cal.word p ≤ controlProfile model C d cal K p := by
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap (cal.word p) (cap model C d cal K p)
    (values model K p) (values_bound hg cal K hWord p)
  change fields (cal.word p) _ ≤ 12 * (natBits (cap model C d cal K p) + cal.word p) + 32 * cal.word p at hf
  unfold controlProfile
  omega

def frame (model : RationalCostModel) (K : ℕ) (p : Problem) : ℕ :=
  let W := (initial model K p).1.2
  let ep := GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)
  GeneralPaperEqualInputInitializerLifetime.inputOwner model W ep +
    GeneralPaperMixedInitializerControls.returnedOwner model W 1 K ep + fields W (values model K p) + 384 * W

noncomputable def frameProfile (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d)
    (K : ℕ) (p : Problem) : ℕ :=
  GeneralPaperMixedInitializerPhases.profile model (cal.word p) K
    (GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)) +
      controlProfile model C d cal K p

theorem frame_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    frame model K p ≤ frameProfile model C d cal K p := by
  let ep := GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)
  have hi := GeneralPaperMixedInitializerPhases.all_phases model (cal.word p) 1 K (cal.positive p) ep .returned
  have hc := controls_bound hg cal K hWord p
  have hw : (initial model K p).1.2 = cal.word p :=
    (GeneralPaperOriginalMeasuredReference.word model 1 K _).trans (congrFun hWord p).symm
  dsimp only [GeneralPaperMixedInitializerPhases.window, GeneralPaperMixedInitializerPhases.component] at hi
  dsimp only [frame, frameProfile]
  rw [hw]
  dsimp only [ep] at hi
  omega

theorem time_rate_small (model : RationalCostModel) :
    Small (GeneralPaperNativeSourceTimeRates.rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hLedger := ledger_small model
  have hFields := fields_small model
  have hPow := dyadic_small model
  unfold GeneralPaperNativeSourceTimeRates.rate GeneralPaperSourceRateAlgebra.monomial
    GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.accuracy
  simp only [source_count, source_exponent, pow_zero, Nat.mul_one]
  fun_prop

theorem control_profile_polylog {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K) :
    Polylog (controlProfile model C d cal K) (logarithm model) := by
  have hL := logarithm_positive model
  have hPrice := bound_small hL (GeneralPaperMeasuredUnequalDispatchHeadlines.price_rate hg cal K hK)
    (time_rate_small model)
  have hn := count_small model
  have hk := exponent_small model
  have hW := small_of_tight cal.tight hL
  have hCap : Small (cap model C d cal K) (logarithm model) := by unfold cap; fun_prop
  have hBits := polylog_bits _ _ hL hCap
  have hWord := polylog_of_tight cal.tight
  unfold controlProfile
  fun_prop

end Blotto.GeneralPaperMeasuredUnequalStorageFrame

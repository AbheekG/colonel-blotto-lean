import Blotto.GeneralPaperEqualInputHeadline

/-! The unrestricted measured initializer feeds its actual outputs into
one bit dispatch. Equality transport erases; it does not rerun accuracy,
rounding, construction, or an analysis profile. -/
namespace Blotto.GeneralPaperEqualInputPipeline
open GeneralPaperEqualInputDomain
open GeneralPaperEqualBitBranch (Prepared outputLaw)
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def transport {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k')
    (a : Prepared (rounded true model W k values v hv) k budget) :
    Prepared (rounded true model W' k' values v hv) k' budget := by
  subst W'
  subst k'
  exact a

theorem transport_source {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    transport model W k W' k' values v hv budget hW hk
      (GeneralPaperEqualBitDispatch.run model W W k values v hv budget).1 =
        (GeneralPaperEqualBitDispatch.run model W' W' k' values v hv budget).1 := by
  subst W'
  subst k'
  rfl

theorem price_congr {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    (GeneralPaperEqualBitDispatch.run model W W k values v hv budget).2 =
      (GeneralPaperEqualBitDispatch.run model W' W' k' values v hv budget).2 := by
  subst W'
  subst k'
  rfl

def run (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    Prepared (rounded true model (word K p) p.k p.values p.selector p.correct) p.k p.budget × ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let actual := GeneralPaperEqualBitDispatch.run model initial.1.2 initial.1.2 initial.1.1 p.values p.selector p.correct p.budget
  let branch := transport model initial.1.2 initial.1.1 (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p) actual.1
  (branch, initial.2 + actual.2)

theorem data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1 = (GeneralPaperEqualBitDispatch.run model (word K p) (word K p) p.k p.values p.selector p.correct p.budget).1 :=
  transport_source model _ _ _ _ p.values p.selector p.correct p.budget _ _

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).2 = (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 +
      GeneralPaperEqualInputRates.sourceWork model K p := by
  have h := price_congr model
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.1
    (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p)
  exact congrArg (fun x => (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 + x) h

theorem calibrated_work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (run model (word K p) K p).2 = GeneralPaperEqualInputRates.totalWork model K p := work model _ K p

theorem epsilon_of_exponent {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1) (hk : k = (GeneralPaperDyadicAccuracy.prepare eps).exponent)
    (budget : ℚ) (hB : 0 < budget) :
    let branch := (GeneralPaperEqualBitDispatch.run model W A k values v hv budget).1
    Supported (budget : ℝ) (outputLaw model branch) ∧
      regret v.values (budget : ℝ) (outputLaw model branch) (outputLaw model branch) ≤ (eps : ℝ) := by
  subst k
  exact GeneralPaperEqualBitDispatch.epsilon model W A values v hv eps hp hOne budget hB

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hB : 0 < p.budget) :
    let branch := (run model A K p).1
    Supported (p.budget : ℝ) (outputLaw model branch) ∧
      regret p.selector.values (p.budget : ℝ) (outputLaw model branch) (outputLaw model branch) ≤
        (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  dsimp only
  rw [data]
  exact epsilon_of_exponent model _ _ p.k p.values p.selector p.correct
    (GeneralPaperEqualInputHeadline.epsilon p) (GeneralPaperEqualInputHeadline.epsilon_positive p) hOne
    (GeneralPaperEqualInputHeadline.exponent_exact p) p.budget hB

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ, ∀ p : Input model,
      (run model (word K p) K p).2 ≤ C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d := by
  obtain ⟨C, d, h⟩ := GeneralPaperEqualInputHeadline.bit_time model hFast K
  refine ⟨C, d, fun p => ?_⟩
  rw [calibrated_work]
  exact h p

end Blotto.GeneralPaperEqualInputPipeline

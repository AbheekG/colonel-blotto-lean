import Blotto.GeneralPaperEqualFirstSpaceGrowth

/-! The optional grouped reserve is bounded on the unrestricted original
input domain. Its sizes are erased observations of the actual branch,
with no supplied small-field or capacity certificate. -/
namespace Blotto.GeneralPaperEqualFirstGroupedGrowth
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualFirstSelectedSpace (SmallBranch groupedProfile)
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

noncomputable def sizes (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ × ℕ × ℕ := by
  classical
  exact if small : SmallBranch model W p then
    ((terminal (rounded true model W p.k p.values p.selector p.correct) small).groups.length,
      GeneralPaperPositiveSegmentCompaction.count (lottery (rounded true model W p.k p.values p.selector p.correct) small),
      (GeneralPaperEqualFirstNativeCache.prepare true model W p.k p.values p.selector p.correct small p.budget).rangeBits)
    else (0,0,0)

theorem sizes_bounds (model : RationalCostModel) (W : ℕ) (p : Input model) :
    (sizes model W p).1 ≤ 3 ∧ (sizes model W p).2.1 ≤ 7 ∧
      (sizes model W p).2.2 ≤ 3670016*(binaryWordWidth p.n+p.k+11)+1 := by
  classical
  by_cases small : SmallBranch model W p
  · simp only [sizes,dite_eq_left small]
    exact ⟨GeneralPaperEqualFirstNativeCache.group_count _ small,
      (GeneralPaperEqualFirstNativeCache.compact_count _ small).2,
      GeneralPaperEqualFirstNativeCache.rangeBits true model W p.k p.values p.selector p.correct small p.budget⟩
  · simp only [sizes,dite_eq_right small]
    exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩

theorem grouped_le (model : RationalCostModel) (W : ℕ) (p : Input model) :
    groupedProfile model W p ≤ GeneralPaperEqualFirstPreparationSpace.profile model W W p.k
      (sizes model W p).1 (sizes model W p).2.1 (sizes model W p).2.2 p.values p.budget := by
  classical
  by_cases small : SmallBranch model W p
  · simp only [groupedProfile,sizes,dite_eq_left small,le_refl]
  · simp only [groupedProfile,sizes,dite_eq_right small]
    exact Nat.zero_le _

theorem denominator_small (model : RationalCostModel) {α : Type*} (input : α → Input model)
    (W L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hn : Small (fun x => (input x).n) L)
    (hk : Tight (fun x => (input x).k) L) :
    Small (fun x => GeneralPaperEqualFirstNativeFacts.roundDen true model (W x) (input x).k (input x).values) L := by
  have hCap : Tight (fun x => binaryWordWidth (input x).n+(input x).k+10) L := by fun_prop
  obtain ⟨C,hC⟩ := hCap
  exact ⟨C,fun x => (GeneralPaperEqualFirstNativeFacts.roundDen_word true model (W x) (input x).k
    (input x).values (input x).selector (input x).correct).trans (hC x)⟩

theorem sizes_polylog (model : RationalCostModel) {α : Type*} (input : α → Input model)
    (W L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hn : Small (fun x => (input x).n) L)
    (hk : Tight (fun x => (input x).k) L) :
    Polylog (fun x => (sizes model (W x) (input x)).1) L ∧
    Polylog (fun x => (sizes model (W x) (input x)).2.1) L ∧
    Polylog (fun x => (sizes model (W x) (input x)).2.2) L := by
  have hCap : Polylog (fun x => 3670016*(binaryWordWidth (input x).n+(input x).k+11)+1) L := by
    have hkPoly := polylog_of_tight hk
    fun_prop
  exact ⟨dominated (polylog_constant 3 L) (fun x => (sizes_bounds model (W x) (input x)).1),
    dominated (polylog_constant 7 L) (fun x => (sizes_bounds model (W x) (input x)).2.1),
    dominated hCap (fun x => (sizes_bounds model (W x) (input x)).2.2)⟩

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => groupedProfile model (word K p) p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := GeneralPaperEqualInputDomain.ledger_positive
  have hn := GeneralPaperEqualInputDomain.count_small model
  have hk := GeneralPaperEqualInputDomain.exponent_tight model
  have hSizes := sizes_polylog model id (word K) logarithm hL hn hk
  have hNumeric := GeneralPaperEqualFirstSpaceGrowth.profile_bound model hFast (word K)
    (fun p : Input model => p.k) (fun p => p.n)
    (fun p => (sizes model (word K p) p).1) (fun p => (sizes model (word K p) p).2.1)
    (fun p => (sizes model (word K p) p).2.2) ledger logarithm (fun p => p.values) (fun p => p.budget)
    hL hk hn (GeneralPaperEqualInputRates.value_small model) (GeneralPaperEqualInputRates.original_budget_small model)
    (denominator_small model id (word K) logarithm hL hn hk)
    (GeneralPaperEqualInputDomain.word_tight K model) hr hSizes.1 hSizes.2.1 hSizes.2.2
    (GeneralPaperEqualInputRates.count_bound model) (GeneralPaperEqualInputRates.value_bound model)
    (GeneralPaperEqualInputRates.budget_bound model)
  exact dominated hNumeric (fun p => grouped_le model (word K p) p)

theorem profile_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    {α : Type*} (input : α → Input model) (W L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hW : Small W L) (hn : Small (fun x => (input x).n) L) (hk : Tight (fun x => (input x).k) L)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (input x).values) L)
    (hb : Small (fun x => rationalWordWidth (input x).budget) L) :
    Small (fun x => groupedProfile model (W x) (input x)) L := by
  have hSizes := sizes_polylog model input W L hL hn hk
  have hNumeric := GeneralPaperEqualFirstSpaceGrowth.profile_small model hFast W
    (fun x => (input x).k) (fun x => (input x).n)
    (fun x => (sizes model (W x) (input x)).1) (fun x => (sizes model (W x) (input x)).2.1)
    (fun x => (sizes model (W x) (input x)).2.2) L
    (fun x => (input x).values) (fun x => (input x).budget) hL hk hn hS hb
    (denominator_small model input W L hL hn hk) hW
    (small_of_polylog hL hSizes.1) (small_of_polylog hL hSizes.2.1) (small_of_polylog hL hSizes.2.2)
  exact small_mono hNumeric (fun x => grouped_le model (W x) (input x))

end Blotto.GeneralPaperEqualFirstGroupedGrowth

import Blotto.GeneralPaperEqualFirstDrawRepresentation

/-! Both corrected selected branches and their actual compact mixed-width
draw closure. The existing local reference and one-bit outer header suffice
for the corrected source. No address, data or midpoint precision changes. -/
namespace Blotto.GeneralPaperEqualFirstSelectedDescription
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualSelectedSampler
open GeneralPaperEqualSelectedDescription (footprint branchFootprint base_positive)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem branch_bound {n : ℕ} (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (p : GeneralPaperEqualBitBranch.Prepared (rounded true model Wv k values v hv) k budget) :
    GeneralPaperEqualSelectedBranchOwner.footprint W p ≤
      GeneralPaperEqualSelectedBranchOwner.profile W n (k+1) (rationalWordWidth budget) := by
  cases p with
  | dominant chosen heavy row correct =>
    exact (GeneralPaperEqualSelectedBranchOwner.pure_bound W budget chosen row correct).trans (Nat.le_add_left _ _)
  | grouped small sampler hK hB =>
    exact (GeneralPaperEqualFirstDescription.profile_bound model Wv W k values v hv small budget sampler hK hB).trans
      (Nat.le_add_right _ _)

theorem profile_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (rounded true model W k values v hv) k budget) :
    footprint a ≤ 2*GeneralPaperEqualDrawAddressCapacity.profile (baseReference a.branch) n (k+1) (rationalWordWidth budget) := by
  have hBase := base_positive a.branch
  have hHead := GeneralPaperEqualSelectedDescription.header_bound (baseReference a.branch) n (k+1) (rationalWordWidth budget) hBase
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      dsimp only at hBase hHead ⊢
      have hp := GeneralPaperEqualSelectedDescription.pure_bound _ (k+1) budget chosen row correct hBase
      dsimp only [footprint,branchFootprint]
      rw [hAddress]
      omega
    | grouped small sampler hK hB =>
      dsimp only at hBase hHead ⊢
      have hp := GeneralPaperEqualFirstDrawRepresentation.profile_bound model W k values v hv small budget sampler hK hB
      dsimp only [footprint,branchFootprint]
      rw [hAddress]
      dsimp only [baseReference] at *
      omega

theorem capacity {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (rounded true model W k values v hv) k budget) : footprint a < 2^a.address := by
  have h := profile_bound model W k values v hv budget a
  have hc := GeneralPaperEqualFirstDrawCapacity.capacity n (GeneralPaperEqualSelectedDescription.groups a.branch) k
    (rationalWordWidth budget) (GeneralPaperEqualSelectedDescription.groups_bound a.branch)
    (GeneralPaperEqualNativeDrawRepresentation.budget_width budget)
  rw [← GeneralPaperEqualSelectedDescription.base_formula] at hc
  have hm := Nat.mul_lt_mul_of_pos_left hc (by decide : 0 < (2 : ℕ))
  rw [a.address_correct,pow_succ]
  nlinarith only [h,hm]

theorem paper_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (rounded true model W k values v hv) k budget) :
    footprint a ≤ 2*GeneralPaperEqualDescriptionRates.paperBound n (k+1) (rationalWordWidth budget) := by
  have h := profile_bound model W k values v hv budget a
  have hd := GeneralPaperEqualDrawDescription.profile_bound (baseReference a.branch) n (k+1) (rationalWordWidth budget)
  have hStep := GeneralPaperEqualFirstBitWork.address_step n (GeneralPaperEqualSelectedDescription.groups a.branch) k (rationalWordWidth budget)
  have hRef : GeneralPaperEqualDescriptionRates.bound (baseReference a.branch) n (k+1) (rationalWordWidth budget) ≤
      GeneralPaperEqualDescriptionRates.bound
        (GeneralPaperEqualBitDrawRates.address n (GeneralPaperEqualSelectedDescription.groups a.branch) (k+1) (rationalWordWidth budget))
        n (k+1) (rationalWordWidth budget) := by
    rw [GeneralPaperEqualSelectedDescription.base_formula]
    unfold GeneralPaperEqualDescriptionRates.bound
    gcongr
  have hDraw := GeneralPaperEqualDrawDescription.bound_at_draw n (GeneralPaperEqualSelectedDescription.groups a.branch)
    (k+1) (rationalWordWidth budget) (GeneralPaperEqualSelectedDescription.groups_bound a.branch)
  exact h.trans (Nat.mul_le_mul_left 2 ((hd.trans hRef).trans hDraw))

def closureProfile (model : RationalCostModel) (W n k b : ℕ) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.profile W n (k+1) b+
    GeneralPaperEqualSelectedClosureLifetime.controlProfile model W n k b+
    GeneralPaperEqualSelectedClosureLifetime.componentProfile model W n k b+
    2*GeneralPaperEqualDescriptionRates.paperBound n (k+1) b

theorem closure_phases {n : ℕ} (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (p : GeneralPaperEqualBitBranch.Prepared (rounded true model Wv k values v hv) k budget)
    (phase : GeneralPaperEqualSelectedClosureLifetime.Phase) :
    GeneralPaperEqualSelectedClosureLifetime.window model W k budget p phase ≤ closureProfile model W n k (rationalWordWidth budget) := by
  have ho := branch_bound model Wv W k values v hv budget p
  have hc := GeneralPaperEqualSelectedClosureLifetime.controls_bound model W k budget p
  have hs := GeneralPaperEqualSelectedClosureLifetime.component_bound model W k budget p phase
  have hr := paper_bound model Wv k values v hv budget (close model W k budget p).1
  dsimp only [GeneralPaperEqualSelectedClosureLifetime.window,closureProfile]
  omega

end Blotto.GeneralPaperEqualFirstSelectedDescription

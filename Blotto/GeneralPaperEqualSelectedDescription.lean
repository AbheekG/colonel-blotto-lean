import Blotto.GeneralPaperEqualSelectedDraw

/-! Complete mixed-width ownership of the returned local closure: the
grouped cache keeps its already stored reference width; the outer reference
has one extra bit. The pure row owns its budget once and its chosen label.
These numerical bounds do not assert an allocation schedule. -/
namespace Blotto.GeneralPaperEqualSelectedDescription
open GeneralPaperEqualSelectedSampler GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def groups {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : GeneralPaperEqualBitBranch.Prepared v k budget → ℕ
  | .dominant _ _ _ _ => 0
  | .grouped small _ _ _ => (GeneralPaperEqualFiniteKernel.terminal v small).groups.length

theorem groups_bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : GeneralPaperEqualBitBranch.Prepared v k budget) : groups p ≤ 3 := by
  cases p with
  | dominant chosen heavy row correct => exact Nat.zero_le _
  | grouped small sampler hK hB => exact GeneralPaperEqualNativeCache.group_count v small

theorem base_formula {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    baseReference p = GeneralPaperEqualBitDrawRates.address n (groups p) k (rationalWordWidth budget) := by
  cases p with
  | dominant chosen heavy row correct => rfl
  | grouped small sampler hK hB =>
    dsimp only [baseReference, groups]
    rw [sampler.address_correct, hK, hB]

theorem base_positive {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : GeneralPaperEqualBitBranch.Prepared v k budget) : 1 ≤ baseReference p := by
  rw [base_formula]
  exact binaryWordWidth_pos _

def branchFootprint {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (W : ℕ) :
    GeneralPaperEqualBitBranch.Prepared v k budget → ℕ
  | .dominant chosen _ row _ => arrayFootprint W rationalWordWidth (⟨row.data,row.size⟩ : FixedArrayTable n ℚ) +
      natBits chosen.val + 32 * W
  | .grouped _ sampler _ _ => GeneralPaperEqualRetainedStorage.footprint sampler.address sampler

def header (W : ℕ) : ℕ := fields W [W] + 64 * W
def footprint {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) : ℕ :=
  branchFootprint a.address a.branch + header a.address

theorem header_bound (A n k b : ℕ) (hA : 1 ≤ A) :
    header (A + 1) ≤ GeneralPaperEqualDrawAddressCapacity.profile A n k b := by
  have h := GeneralPaperNaturalScalarLifetime.counter_word (A + 1)
  have he : header (A + 1) = natBits (A + 1) + 97 * (A + 1) := by
    simp only [header,fields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    ring
  rw [he,GeneralPaperEqualDrawAddressCapacity.profile_eq]
  omega

theorem pure_bound {n : ℕ} (A k : ℕ) (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (h : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) (hA : 1 ≤ A) :
    arrayFootprint (A + 1) rationalWordWidth (⟨row.data,row.size⟩ : FixedArrayTable n ℚ) + natBits chosen.val + 32 * (A + 1) ≤
      GeneralPaperEqualDrawAddressCapacity.profile A n k (rationalWordWidth budget) := by
  have hp : (∑ j : Fin n, rationalWordWidth (row.allocation j)) ≤ 3 * n + rationalWordWidth budget := by
    simp_rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen row h]
    exact GeneralPaperEqualBitVertex.payload budget chosen
  have ha : arrayFootprint (A + 1) rationalWordWidth (⟨row.data,row.size⟩ : FixedArrayTable n ℚ) ≤
      64 * (A + 1) + n * (A + 1) + 3 * n + rationalWordWidth budget := by
    change 64 * (A + 1) + (∑ j : Fin n, (A + 1 + rationalWordWidth (row.allocation j))) ≤ _
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    nlinarith only [hp]
  have hi := GeneralPaperNaturalScalarLifetime.counter_word chosen.val
  have hn := Nat.mul_le_mul_left n hA
  have hc := chosen.isLt
  have hNQ := Nat.zero_le (n * GeneralPaperEqualNativeRetainedStorage.short n k)
  have hAQ := Nat.zero_le (A * GeneralPaperEqualNativeRetainedStorage.short n k)
  rw [GeneralPaperEqualDrawAddressCapacity.profile_eq]
  nlinarith only [ha,hi,hn,hc,hA,hNQ,hAQ]

theorem profile_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    footprint a ≤ 2 * GeneralPaperEqualDrawAddressCapacity.profile (baseReference a.branch) n k (rationalWordWidth budget) := by
  have hBase := base_positive a.branch
  have hHead := header_bound (baseReference a.branch) n k (rationalWordWidth budget) hBase
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      dsimp only at hBase hHead ⊢
      have hp := pure_bound _ k budget chosen row correct hBase
      dsimp only [footprint,branchFootprint]
      rw [hAddress]
      omega
    | grouped small sampler hK hB =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
      subst sampler
      dsimp only at hBase hHead ⊢
      have hp := GeneralPaperEqualNativeDrawRepresentation.native_bound true model W k values v hv small budget
      dsimp only [GeneralPaperEqualStoredBitSampler.native, GeneralPaperEqualNativeCache.prepare] at hp
      dsimp only [footprint,branchFootprint]
      rw [hAddress]
      dsimp only [baseReference] at *
      omega

theorem capacity {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    footprint a < 2 ^ a.address := by
  have h := profile_bound model W k values v hv budget a
  have hc := GeneralPaperEqualDrawAddressCapacity.capacity n (groups a.branch) k (rationalWordWidth budget)
    (groups_bound a.branch) (GeneralPaperEqualNativeDrawRepresentation.budget_width budget)
  rw [← base_formula] at hc
  have hm := Nat.mul_lt_mul_of_pos_left hc (by decide : 0 < 2)
  rw [a.address_correct,pow_succ]
  nlinarith only [h,hm]

theorem paper_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    footprint a ≤ 2 * GeneralPaperEqualDescriptionRates.paperBound n k (rationalWordWidth budget) := by
  have h := profile_bound model W k values v hv budget a
  have hd := (GeneralPaperEqualDrawDescription.profile_bound (baseReference a.branch) n k (rationalWordWidth budget)).trans
    (by simpa only [base_formula] using GeneralPaperEqualDrawDescription.bound_at_draw n (groups a.branch) k (rationalWordWidth budget) (groups_bound a.branch))
  exact h.trans (Nat.mul_le_mul_left 2 hd)

end Blotto.GeneralPaperEqualSelectedDescription

import Blotto.ImplicitLeafProposalInterface
import Blotto.ImplicitLeafSamplingSchedule

/-! The actual resource-driven sparse rounded history constructs a proposal
leaf with derived partition/positivity certificates. Its all-budget target and
scheduled seed cap follow the concrete block sampler, not an enumerated label
categorical. Decoder correctness and internal-node caps remain separate. -/

namespace Blotto.ImplicitLeafCounts
open scoped Classical

def roundedProposalLeaf {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) : ProposalLeaf where
  cap := caps field
  blocks := resourceBlockHistory caps decode selected opponent eta theta past field
  partition := resourceBlockHistory_partition caps decode selected opponent eta theta past field
  positive := resourceBlockHistory_positive caps decode selected opponent eta theta heta htheta past field
  decode := decode field
  monotone := hm field

theorem roundedProposalLeaf_mass {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (code : Fin (caps field + 1)) :
    (roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).family.mass code =
      SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected
        (resourceLoss caps decode selected opponent) eta theta past field code :=
  resourceBlockHistory_refines caps decode hm selected opponent eta theta past field code

theorem roundedProposalLeaf_resource {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (code : Fin (caps field + 1)) :
    (roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).family.resource code =
      decode field code.val := rfl

theorem roundedProposalLeaf_scheduled_close {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (budget epsilon : ℚ) (he : 0 < epsilon) :
    ((roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).actualKernel budget
      (leafPrecision epsilon) (leafPrecision epsilon)).Close
      ((roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).idealKernel budget) (epsilon : ℝ) := by
  intro test hTest
  exact ((roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).actualKernel_close
    budget _ _ test hTest).trans (leafPrecision_error epsilon he)

theorem roundedProposalLeaf_horizon_cap {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (epsilon : ℚ) (he : 0 < epsilon)
    (T : ℕ) (hT : past.length ≤ T) :
    (roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past field).bitBudget
      (leafPrecision epsilon) (leafPrecision epsilon) ≤
        6 * T + (6 + binaryWordWidth (16 * epsilon).den) * (3 + offsetWidth (caps field)) :=
  resourceBlockHistory_horizon_word_cap caps decode selected opponent eta theta epsilon he past field T hT

end Blotto.ImplicitLeafCounts

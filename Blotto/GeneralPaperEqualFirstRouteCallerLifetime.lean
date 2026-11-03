import Blotto.GeneralPaperEqualFirstPackingCallerLifetime

/-! Actual native routes consume the measured packing and materialized
length returns. Their caller and completed route payload have derived bounds;
all partial-table and scalar conditions follow native rounded lattice data. -/
namespace Blotto.GeneralPaperEqualFirstRouteCallerLifetime
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal)
open GeneralPaperEqualFirstPackingCallerLifetime (packing lengths length_correct)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def routes {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) :=
  GeneralPaperEqualRouteConstruction.prepare (packing model W A exponent values v hv small).1 model A
    (lengths model W A exponent values).1 (length_correct model W A exponent values v hv small)

theorem work_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W exponent values v hv).weight j ≤ 1) (_budget : ℚ) :
    (routes model W A exponent values v hv small).2 ≤
      GeneralPaperEqualFirstPrefixRates.routeBound model A n exponent :=
  GeneralPaperEqualFirstPrefixRates.routes model W A exponent values v hv small
    (packing model W A exponent values v hv small).1 (lengths model W A exponent values).1
    (length_correct model W A exponent values v hv small)

def borrowed {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstPackingCallerLifetime.window model W A exponent values v hv small budget

def returnedPayload {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) : ℕ :=
  GeneralPaperEqualRouteOwner.footprint A (routes model W A exponent values v hv small).1

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) :
    returnedPayload model W A exponent values v hv small ≤ GeneralPaperEqualRouteOwner.profile A n 3 (binaryWordWidth n + exponent + 10) :=
  GeneralPaperEqualFirstSourceOwnership.routes true model W A exponent values v hv small (routes model W A exponent values v hv small).1

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperRouteConstructionLifetime.Phase n (terminal (rounded true model W exponent values v hv) small).groups.length) : ℕ :=
  GeneralPaperRouteConstructionLifetime.window (packing model W A exponent values v hv small).1 model A
    (lengths model W A exponent values).1 (borrowed model W A exponent values v hv small budget)
    (returnedPayload model W A exponent values v hv small) phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperRouteConstructionLifetime.profile A n m
    (GeneralPaperEqualFirstPrefixRates.routeBound model A n exponent)
    (binaryWordWidth n + exponent + 10)
    (GeneralPaperEqualFirstPackingCallerLifetime.profile model W A exponent values budget)
    (GeneralPaperEqualRouteOwner.profile A n 3 (binaryWordWidth n + exponent + 10))

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperRouteConstructionLifetime.Phase n (terminal (rounded true model W exponent values v hv) small).groups.length) :
    window model W A exponent values v hv small budget phase ≤
      profile model W A exponent (terminal (rounded true model W exponent values v hv) small).groups.length values budget := by
  have hWork := work_bound model W A exponent values v hv small budget
  change (GeneralPaperEqualRouteConstruction.run (packing model W A exponent values v hv small).1 model A (lengths model W A exponent values).1).2 ≤ _ at hWork
  have hFields := GeneralPaperEqualFirstSourceOwnership.fields_height true model W exponent values v hv small
    (packing model W A exponent values v hv small).1 (lengths model W A exponent values).1 (length_correct model W A exponent values v hv small)
  have hKernel := GeneralPaperRouteConstructionLifetime.all_phases (packing model W A exponent values v hv small).1 model A _
    (lengths model W A exponent values).1 (by omega : 2 ≤ binaryWordWidth n + exponent + 10) hFields.1 hFields.2 hWork
    (borrowed model W A exponent values v hv small budget) (returnedPayload model W A exponent values v hv small) phase
  exact hKernel.trans (GeneralPaperRouteConstructionLifetime.owner_mono A n _ _ _ _ _ _ _
    (GeneralPaperEqualFirstPackingCallerLifetime.actual model W A exponent values v hv small budget)
    (returned_bound model W A exponent values v hv small))

end Blotto.GeneralPaperEqualFirstRouteCallerLifetime

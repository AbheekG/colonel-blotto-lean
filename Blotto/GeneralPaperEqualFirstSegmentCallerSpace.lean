import Blotto.GeneralPaperEqualFirstSourceSpace

/-! Segment generation consumes the actual corrected route/packing returns.
The previous source owners, static segment code and prefix price/control
records remain live; all bounds concern erased observers of the same source. -/
namespace Blotto.GeneralPaperEqualFirstSegmentCallerSpace
open GeneralPaperEqualFirstNativeFacts (rounded roundDen fieldHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualFirstPackingCallerLifetime (packing lengths length_correct)
open GeneralPaperEqualFirstRouteCallerLifetime (routes)
open GeneralPaperEqualFirstInitialPrefixLifetime (raw)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def sourcePriceCap {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  GeneralPaperEqualFirstPrefixRates.prefixBound model W A k values+
    GeneralPaperEqualFirstPrefixRates.packingBound model A n k+
    GeneralPaperEqualFirstPrefixRates.routeBound model A n k

theorem source_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (raw model W k values).2+(lengths model W A k values).2+
      (packing model W A k values v hv small).2+(routes model W A k values v hv small).2 ≤
        sourcePriceCap model W A k values := by
  have h0 := GeneralPaperEqualFirstPrefixRates.prefix_work model W A k values v hv
  have h1 := GeneralPaperEqualFirstPackingCallerLifetime.work_bound model W A k values v hv small budget
  have h2 := GeneralPaperEqualFirstRouteCallerLifetime.work_bound model W A k values v hv small budget
  exact Nat.add_le_add (Nat.add_le_add h0 h1) h2

def borrowed {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstRouteCallerLifetime.window model W A k values v hv small budget .returned+
    GeneralPaperEqualStaticCodeOwner.footprint A+
    GeneralPaperEqualSegmentCallerOwners.controlFoot A W n (roundDen true model W k values) k
      (raw model W k values).2 (lengths model W A k values).2
      (packing model W A k values v hv small).2 (routes model W A k values v hv small).2

def ownerProfile {n : ℕ} (model : RationalCostModel) (W A k m : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstSourceSpace.profile model W A k m values budget+
    GeneralPaperEqualStaticCodeOwner.profile A+
    GeneralPaperEqualSegmentCallerOwners.controlProfile A W n (roundDen true model W k values) k
      (sourcePriceCap model W A k values)

theorem owner_bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    borrowed model W A k values v hv small budget ≤
      ownerProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length values budget := by
  have h0 := GeneralPaperEqualFirstSourceSpace.all_phases model W A k values v hv small budget (.inr (some .returned))
  have h1 := GeneralPaperEqualStaticCodeOwner.bounded A
  have h2 := GeneralPaperEqualSegmentCallerOwners.controls_bound A W n (roundDen true model W k values) k
    (raw model W k values).2 (lengths model W A k values).2
    (packing model W A k values v hv small).2 (routes model W A k values v hv small).2
    (sourcePriceCap model W A k values) (source_work model W A k values v hv small budget)
  exact Nat.add_le_add (Nat.add_le_add h0 h1) h2

def full {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :=
  GeneralPaperEqualNativeSegmentPreparation.prepared (rounded true model W k values v hv) small
    (packing model W A k values v hv small).1 model A

theorem full_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :
    (full model W A k values v hv small).2 ≤ GeneralPaperEqualFirstPrefixRates.segmentBound model A n k :=
  GeneralPaperEqualFirstPrefixRates.segments model W A k values v hv small (packing model W A k values v hv small).1

theorem fields_height {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :
    ((packing model W A k values v hv small).1.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)).FieldsHeight
      (fieldHeight n k) := by
  have h := GeneralPaperEqualFirstNativeFacts.native_spec_height true model W k values v hv small
  unfold GeneralPaperEqualFiniteKernel.spec at h
  rw [RationalTerminalPacking.uniformSpec_eq] at h ⊢
  exact h

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (terminal (rounded true model W k values v hv) small).groups.length) : ℕ :=
  GeneralPaperNativeSegmentFactoryLifetime.window
    ((packing model W A k values v hv small).1.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small))
    (packing model W A k values v hv small).1.groups.data.size (terminal _ small).groups_count model A
    (borrowed model W A k values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A k m : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperNativeSegmentFactoryLifetime.profile model A (fieldHeight n k) (ownerProfile model W A k m values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (terminal (rounded true model W k values v hv) small).groups.length) :
    window model W A k values v hv small budget phase ≤
      profile model W A k (terminal (rounded true model W k values v hv) small).groups.length values budget := by
  let p := (packing model W A k values v hv small).1
  have h := GeneralPaperNativeSegmentFactoryLifetime.bounded
    (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size p.groups.size
    (terminal _ small).groups_count model A (fieldHeight n k)
    (borrowed model W A k values v hv small budget) (by unfold fieldHeight; omega)
    (fields_height model W A k values v hv small) phase
  exact h.trans (GeneralPaperEqualSegmentCallerLifetime.factory_borrowed_mono model A _ _ _
    (owner_bound model W A k values v hv small budget))

end Blotto.GeneralPaperEqualFirstSegmentCallerSpace

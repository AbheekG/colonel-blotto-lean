import Blotto.GeneralPaperEqualDispatchLocalRates
import Blotto.GeneralPaperEqualInputContract

/-! Simultaneous initializer, once-built prefix, heavy scan, dominant row,
grouped native phases and dispatch parent lifetimes. The grouped reserve is
an erased conditional analysis, never a branch premise of the input or a
runtime memory census. All previously retained owners remain reserved. -/
namespace Blotto.GeneralPaperEqualDispatchLifetime
open GeneralPaperEqualInputDomain GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def SmallBranch (model : RationalCostModel) (p : Input model) : Prop :=
  ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1

noncomputable def groupedProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ := by
  classical
  exact if h : SmallBranch model p then
    GeneralPaperEqualFullInitializationResources.profile model W K (grouped p h) else 0

def sourceWork (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualBitDispatch.run model W W p.k p.values p.selector p.correct p.budget).2

def parentCap (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  p.n + p.k + W + K + word K p +
    GeneralPaperEqualInputInitialization.initializationPrice model W K p +
    GeneralPaperEqualBitDispatch.bound model W W p.k p.values p.budget + 128 * W + 128

def parentWindow (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  fields W [p.n,p.k,W,K,word K p,
    (GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
    sourceWork model W p,
    (GeneralPaperEqualInputInitialization.prepareReference model W K p).2 + sourceWork model W p] + 192 * W

def parentProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  8 * (natBits (parentCap model W K p) + W) + 224 * W

theorem parent_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    parentWindow model W K p ≤ parentProfile model W K p := by
  have hi := GeneralPaperEqualInputInitialization.initialization_work model W K p
  have hs : sourceWork model W p ≤ GeneralPaperEqualBitDispatch.bound model W W p.k p.values p.budget :=
    GeneralPaperEqualBitDispatch.work model W W p.k p.values p.selector p.correct p.budget
  have hf := fields_bound W (natBits (parentCap model W K p))
    [p.n,p.k,W,K,word K p,
      (GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
      sourceWork model W p,
      (GeneralPaperEqualInputInitialization.prepareReference model W K p).2 + sourceWork model W p] (by
        intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap; omega)
  change fields W _ ≤ 8 * (natBits (parentCap model W K p) + W) + 32 * W at hf
  dsimp only [parentWindow, parentProfile]
  omega

def lengths (model : RationalCostModel) (W : ℕ) (p : Input model) : FixedArrayTable p.n ℚ :=
  let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 p.k p.values).1
  (GeneralPaperEqualLengthArray.run model W raw.1 raw.2).1

noncomputable def profile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.profile model W K p +
    GeneralPaperEqualDispatchLocalRates.profile model W p + groupedProfile model W K p + parentProfile model W K p

inductive Phase (model : RationalCostModel) (W : ℕ) (p : Input model) where
  | initialization (phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n)
  | initialPrefix (phase : GeneralPaperEqualInitialPrefixLifetime.Phase p.n)
  | scan (cursor : ℕ) (h : cursor ≤ p.n)
  | vertex (chosen : Fin p.n) (cursor : ℕ) (h : cursor ≤ p.n)
  | groupedNative (small : SmallBranch model p)
      (phase : GeneralPaperEqualCommonReference.Phase model W (grouped p small))
  | returned

noncomputable def window (model : RationalCostModel) (W K : ℕ) (p : Input model) : Phase model W p → ℕ
  | .initialization phase => GeneralPaperEqualInputInitializerLifetime.window model W K p phase + parentWindow model W K p
  | .initialPrefix phase => GeneralPaperEqualInputInitializerLifetime.returnedOwner model W K p +
      GeneralPaperEqualInitialPrefixLifetime.window model W W p.k p.values p.budget phase + parentWindow model W K p
  | .scan cursor _ => GeneralPaperEqualInputInitializerLifetime.returnedOwner model W K p +
      GeneralPaperEqualInitialPrefixLifetime.window model W W p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) cursor + parentWindow model W K p
  | .vertex chosen cursor h => GeneralPaperEqualInputInitializerLifetime.returnedOwner model W K p +
      GeneralPaperEqualInitialPrefixLifetime.window model W W p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n +
      GeneralPaperEqualBitVertexLifetime.window W p.budget chosen cursor h + parentWindow model W K p
  | .groupedNative small phase => GeneralPaperEqualInputInitializerLifetime.returnedOwner model W K p +
      GeneralPaperEqualInitialPrefixLifetime.window model W W p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n +
      GeneralPaperEqualFullInitializationResources.window model W K (grouped p small) (.inr phase) + parentWindow model W K p
  | .returned => GeneralPaperEqualInputInitializerLifetime.returnedOwner model W K p +
      GeneralPaperEqualInitialPrefixLifetime.window model W W p.k p.values p.budget .returned +
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n +
      GeneralPaperEqualDispatchLocalRates.vertexProfile W p + groupedProfile model W K p + parentWindow model W K p

theorem all_phases (model : RationalCostModel) (W K : ℕ) (p : Input model)
    (hW : 1 ≤ W) (hIndex : binaryWordWidth (p.n + 1) ≤ W) (phase : Phase model W p) :
    window model W K p phase ≤ profile model W K p := by
  have hParent := parent_bound model W K p
  have hReturn := GeneralPaperEqualInputInitializerLifetime.all_phases model W K p .returned
  simp only [GeneralPaperEqualInputInitializerLifetime.window, GeneralPaperEqualInputInitializerLifetime.cursorControls,
    GeneralPaperEqualInputInitializerLifetime.component] at hReturn
  have hPrefix := GeneralPaperEqualInitialPrefixLifetime.all_phases model W W p.k p.values p.selector p.correct p.budget .returned
  have hShort : 3 ≤ GeneralPaperEqualDispatchLocalRates.short p := by
    dsimp only [GeneralPaperEqualDispatchLocalRates.short]; omega
  have hLengths : ∀ j, rationalWordWidth ((lengths model W p).read j) ≤ GeneralPaperEqualDispatchLocalRates.short p :=
    GeneralPaperEqualBitBoundaryScan.native_width model W W p.k p.values p.selector p.correct
  have hScan := GeneralPaperEqualBitScanLifetime.all_cursors model W _ (lengths model W p) hShort hLengths p.n le_rfl
  change GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n ≤
    GeneralPaperEqualDispatchLocalRates.scanProfile model W p at hScan
  cases phase with
  | initialization phase =>
    have h := GeneralPaperEqualInputInitializerLifetime.all_phases model W K p phase
    dsimp only [window, profile]; omega
  | initialPrefix phase =>
    have h := GeneralPaperEqualInitialPrefixLifetime.all_phases model W W p.k p.values p.selector p.correct p.budget phase
    dsimp only [window, profile, GeneralPaperEqualDispatchLocalRates.profile, GeneralPaperEqualDispatchLocalRates.prefixProfile]
    omega
  | scan cursor h =>
    have hs := GeneralPaperEqualBitScanLifetime.all_cursors model W _ (lengths model W p) hShort hLengths cursor h
    dsimp only [window, profile, GeneralPaperEqualDispatchLocalRates.profile, GeneralPaperEqualDispatchLocalRates.prefixProfile,
      GeneralPaperEqualDispatchLocalRates.scanProfile]
    omega
  | vertex chosen cursor h =>
    have hv := GeneralPaperEqualBitVertexLifetime.all_cursors W p.budget chosen hW hIndex cursor h
    dsimp only [window, profile, GeneralPaperEqualDispatchLocalRates.profile, GeneralPaperEqualDispatchLocalRates.prefixProfile,
      GeneralPaperEqualDispatchLocalRates.vertexProfile]
    omega
  | groupedNative small phase =>
    have hn := GeneralPaperEqualFullInitializationResources.all_phases model W K (grouped p small) (.inr phase)
    have hg : GeneralPaperEqualFullInitializationResources.profile model W K (grouped p small) = groupedProfile model W K p := by
      classical
      simp only [groupedProfile, dite_eq_left small]
    rw [hg] at hn
    dsimp only [window, profile, GeneralPaperEqualDispatchLocalRates.profile, GeneralPaperEqualDispatchLocalRates.prefixProfile]
    omega
  | returned =>
    dsimp only [window, profile, GeneralPaperEqualDispatchLocalRates.profile, GeneralPaperEqualDispatchLocalRates.prefixProfile]
    omega

theorem parent_total_work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (GeneralPaperEqualInputPipeline.run model (word K p) K p).2 =
      (GeneralPaperEqualInputInitialization.prepareReference model (word K p) K p).2 + sourceWork model (word K p) p :=
  GeneralPaperEqualInputPipeline.calibrated_work model K p

end Blotto.GeneralPaperEqualDispatchLifetime

import Blotto.GeneralPaperEqualFirstSelectedPreparation

/-! Complete corrected selected-entry phase space after the retained
accuracy index is available. Branch selection remains inside the actual
producer. The grouped reserve is erased conditional analysis, with the
once-built prefix, scan and parent records retained through local closure. -/
namespace Blotto.GeneralPaperEqualFirstSelectedSpace
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEncodedScalarStorage (natBits fields fields_bound)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def SmallBranch (model : RationalCostModel) (W : ℕ) (p : Input model) : Prop :=
  ∀ j, 2*(rounded true model W p.k p.values p.selector p.correct).weight j ≤ 1

noncomputable def groupedProfile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ := by
  classical
  exact if small : SmallBranch model W p then
    GeneralPaperEqualFirstPreparationSpace.profile model W W p.k
      (terminal (rounded true model W p.k p.values p.selector p.correct) small).groups.length
      (count (lottery (rounded true model W p.k p.values p.selector p.correct) small))
      (GeneralPaperEqualFirstNativeCache.prepare true model W p.k p.values p.selector p.correct small p.budget).rangeBits
      p.values p.budget else 0

def lengths (model : RationalCostModel) (W : ℕ) (p : Input model) : FixedArrayTable p.n ℚ :=
  (GeneralPaperEqualFirstPackingCallerLifetime.lengths model W W p.k p.values).1

def short {model : RationalCostModel} (p : Input model) : ℕ := 1+6*(binaryWordWidth p.n+p.k+12)

theorem lengths_width (model : RationalCostModel) (W : ℕ) (p : Input model) :
    ∀ j, rationalWordWidth ((lengths model W p).read j) ≤ short p := by
  dsimp only [lengths,GeneralPaperEqualFirstPackingCallerLifetime.lengths,GeneralPaperEqualFirstInitialPrefixLifetime.raw]
  rw [GeneralPaperEqualFirstRounding.source_successor]
  simpa only [short,Nat.add_assoc] using GeneralPaperEqualBitBoundaryScan.native_width model W W (p.k+1) p.values p.selector p.correct

def branch (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  (GeneralPaperEqualFirstBitDispatch.run model W W p.k p.values p.selector p.correct p.budget).1

def closure (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  GeneralPaperEqualSelectedSampler.close model W p.k p.budget (branch model W p)

def sourceWork (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualFirstBitDispatch.run model W W p.k p.values p.selector p.correct p.budget).2

def totalWork (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualFirstSelectedPreparation.run model W W p.k p.values p.selector p.correct p.budget).2

def parentCap (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  p.n+p.k+W+GeneralPaperEqualFirstSelectedPreparation.bound model W W p.k p.values p.budget+128*W+129

def parentWindow (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  fields W [p.n,p.k,W,(GeneralPaperEqualFirstInitialPrefixLifetime.raw model W p.k p.values).2,
    (GeneralPaperEqualFirstPackingCallerLifetime.lengths model W W p.k p.values).2,
    sourceWork model W p,(closure model W p).2,totalWork model W p]+192*W

def parentProfile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  8*(natBits (parentCap model W p)+W)+224*W

theorem prefix_prices (model : RationalCostModel) (W : ℕ) (p : Input model) :
    (GeneralPaperEqualFirstInitialPrefixLifetime.raw model W p.k p.values).2+
      (GeneralPaperEqualFirstPackingCallerLifetime.lengths model W W p.k p.values).2 ≤ sourceWork model W p := by
  dsimp only [sourceWork,GeneralPaperEqualFirstBitDispatch.run,GeneralPaperEqualFirstInitialPrefixLifetime.raw,
    GeneralPaperEqualFirstPackingCallerLifetime.lengths]
  omega

theorem parent_bound (model : RationalCostModel) (W : ℕ) (p : Input model) :
    parentWindow model W p ≤ parentProfile model W p := by
  have hp := prefix_prices model W p
  have hs := GeneralPaperEqualFirstPreparationWork.work model W W p.k p.values p.selector p.correct p.budget
  have hc := GeneralPaperEqualSelectedClosureWork.work model W p.k p.budget (branch model W p)
  have ht := GeneralPaperEqualFirstSelectedPreparation.work model W W p.k p.values p.selector p.correct p.budget
  change sourceWork model W p ≤ _ at hs
  change (closure model W p).2 ≤ _ at hc
  change totalWork model W p ≤ _ at ht
  unfold GeneralPaperEqualFirstSelectedPreparation.bound at ht
  have hf := fields_bound W (natBits (parentCap model W p))
    [p.n,p.k,W,(GeneralPaperEqualFirstInitialPrefixLifetime.raw model W p.k p.values).2,
      (GeneralPaperEqualFirstPackingCallerLifetime.lengths model W W p.k p.values).2,
      sourceWork model W p,(closure model W p).2,totalWork model W p] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap GeneralPaperEqualFirstSelectedPreparation.bound; omega)
  change fields W _ ≤ 8*(natBits (parentCap model W p)+W)+32*W at hf
  dsimp only [parentWindow,parentProfile]
  omega

noncomputable def profile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualFirstInitialPrefixLifetime.profile model W W p.k p.values p.budget+
    GeneralPaperEqualBitScanLifetime.profile model W p.n (short p)+
    GeneralPaperEqualBitVertexLifetime.profile W p.n (rationalWordWidth p.budget)+
    groupedProfile model W p+
    GeneralPaperEqualFirstSelectedDescription.closureProfile model W p.n p.k (rationalWordWidth p.budget)+parentProfile model W p

inductive Phase (model : RationalCostModel) (W : ℕ) (p : Input model) where
  | initialPrefix (phase : GeneralPaperEqualFirstInitialPrefixLifetime.Phase p.n)
  | scan (cursor : ℕ) (h : cursor ≤ p.n)
  | vertex (chosen : Fin p.n) (cursor : ℕ) (h : cursor ≤ p.n)
  | groupedNative (small : SmallBranch model W p)
      (phase : GeneralPaperEqualFirstPreparationSpace.Phase p.n
        (terminal (rounded true model W p.k p.values p.selector p.correct) small).groups.length
        (count (lottery (rounded true model W p.k p.values p.selector p.correct) small)) (p.k+5)
        (GeneralPaperEqualFirstNativeCache.prepare true model W p.k p.values p.selector p.correct small p.budget).rangeBits)
  | localClosure (phase : GeneralPaperEqualSelectedClosureLifetime.Phase)
  | returned

noncomputable def window (model : RationalCostModel) (W : ℕ) (p : Input model) : Phase model W p → ℕ
  | .initialPrefix phase => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget phase+parentWindow model W p
  | .scan cursor _ => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget .returned+
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) cursor+parentWindow model W p
  | .vertex chosen cursor h => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget .returned+
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n+
      GeneralPaperEqualBitVertexLifetime.window W p.budget chosen cursor h+parentWindow model W p
  | .groupedNative small phase => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget .returned+
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n+
      GeneralPaperEqualFirstPreparationSpace.window model W W p.k p.values p.selector p.correct small p.budget phase+parentWindow model W p
  | .localClosure phase => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget .returned+
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n+
      GeneralPaperEqualBitVertexLifetime.profile W p.n (rationalWordWidth p.budget)+groupedProfile model W p+
      GeneralPaperEqualSelectedClosureLifetime.window model W p.k p.budget (branch model W p) phase+parentWindow model W p
  | .returned => GeneralPaperEqualFirstInitialPrefixLifetime.window model W W p.k p.values p.budget .returned+
      GeneralPaperEqualBitScanLifetime.window model W (lengths model W p) p.n+
      GeneralPaperEqualBitVertexLifetime.profile W p.n (rationalWordWidth p.budget)+groupedProfile model W p+
      GeneralPaperEqualSelectedClosureLifetime.window model W p.k p.budget (branch model W p) .returned+parentWindow model W p

theorem all_phases (model : RationalCostModel) (W : ℕ) (p : Input model)
    (hW : 1 ≤ W) (hIndex : binaryWordWidth (p.n+1) ≤ W) (phase : Phase model W p) :
    window model W p phase ≤ profile model W p := by
  have hParent := parent_bound model W p
  have hPrefix := GeneralPaperEqualFirstInitialPrefixLifetime.all_phases model W W p.k p.values p.selector p.correct p.budget .returned
  have hShort : 3 ≤ short p := by unfold short; omega
  have hScan := GeneralPaperEqualBitScanLifetime.all_cursors model W (short p) (lengths model W p)
    hShort (lengths_width model W p) p.n le_rfl
  cases phase with
  | initialPrefix phase =>
    have h := GeneralPaperEqualFirstInitialPrefixLifetime.all_phases model W W p.k p.values p.selector p.correct p.budget phase
    dsimp only [window,profile]; omega
  | scan cursor h =>
    have hs := GeneralPaperEqualBitScanLifetime.all_cursors model W (short p) (lengths model W p)
      hShort (lengths_width model W p) cursor h
    dsimp only [window,profile]; omega
  | vertex chosen cursor h =>
    have hv := GeneralPaperEqualBitVertexLifetime.all_cursors W p.budget chosen hW hIndex cursor h
    dsimp only [window,profile]; omega
  | groupedNative small phase =>
    have hg := GeneralPaperEqualFirstPreparationSpace.all_phases model W W p.k p.values p.selector p.correct small p.budget phase
    have he : GeneralPaperEqualFirstPreparationSpace.profile model W W p.k
        (terminal (rounded true model W p.k p.values p.selector p.correct) small).groups.length
        (count (lottery (rounded true model W p.k p.values p.selector p.correct) small))
        (GeneralPaperEqualFirstNativeCache.prepare true model W p.k p.values p.selector p.correct small p.budget).rangeBits
        p.values p.budget = groupedProfile model W p := by
      classical
      simp only [groupedProfile,dite_eq_left small]
    rw [he] at hg
    dsimp only [window,profile]; omega
  | localClosure phase =>
    have hc := GeneralPaperEqualFirstSelectedDescription.closure_phases model W W p.k p.values p.selector p.correct p.budget
      (branch model W p) phase
    dsimp only [window,profile]; omega
  | returned =>
    have hc := GeneralPaperEqualFirstSelectedDescription.closure_phases model W W p.k p.values p.selector p.correct p.budget
      (branch model W p) .returned
    dsimp only [window,profile]; omega

theorem actual_return (model : RationalCostModel) (W : ℕ) (p : Input model) :
    (GeneralPaperEqualFirstSelectedPreparation.run model W W p.k p.values p.selector p.correct p.budget).1 =
      (closure model W p).1 := rfl

end Blotto.GeneralPaperEqualFirstSelectedSpace

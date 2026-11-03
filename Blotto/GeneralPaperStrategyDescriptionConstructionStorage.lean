import Blotto.GeneralPaperFramedAccuracyConstructionStorage

/-! The actual description constructor retains the original reduction,
both complete source dictionaries and its returned description. Only the
selected native circle/direct branch contributes a construction window.
The cursor is erased observation of existing constructor calls. -/
namespace Blotto.GeneralPaperStrategyDescriptionConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperStrategyDescription GeneralPaperClosedDescriptionStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

structure Cursor {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (T : ℕ) where
  commonCount : ℕ
  hCommon : commonCount≤o.classified.light.size
  rows : ℕ
  hRows : rows≤T
  count : ℕ
  hCount : count≤o.representatives
  used : ℕ
  copied : ℕ
  active : Option (Fin o.representatives×Fin o.representatives)

def physicalFoot {T m K : ℕ} (W : ℕ) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T m K) : ℕ :=
  columnsFoot W columns.rich+columnsFoot W columns.poor+32*W

def physicalProfile (W T m K H : ℕ) : ℕ := 2*columnsProfile W T m K (1+2*H)+32*W

theorem physical_bound {T m K : ℕ} (W H : ℕ) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T m K)
    (hRich : ∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H) : physicalFoot W columns≤physicalProfile W T m K H := by
  have hr := columns_bound W (1+2*H) columns.rich (fun j l => rationalWordWidth_of_height (hRich j l))
  have hp := columns_bound W (1+2*H) columns.poor (fun j l => rationalWordWidth_of_height (hPoor j l))
  unfold physicalFoot physicalProfile
  omega

def childWork {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) : ℕ :=
  if h:o.replaced=true then (GeneralPaperCachedCircleRows.pair model.rat (fun w => w) W o (hRep h).1 columns).2 else 0

def childWindow {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (c : Cursor o T) : ℕ :=
  if h:o.replaced=true then GeneralPaperCachedPairConstructionStorage.window model W o (hRep h).1 columns
    c.commonCount c.rows c.count c.hCommon c.hRows c.hCount c.used c.copied c.active else 0

def childProfile {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  if o.replaced then GeneralPaperCachedPairConstructionStorage.profile model W T K H o else 0

def price {n : ℕ} (model : RationalCostModel) (W T H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperCachedPairConstructionStorage.price model W T H o+64*W

def cap {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+o.m+T+K+W+price model W T H o+64*W+1

def controls {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) : List ℕ :=
  [W,o.m,T,K,childWork model W o hRep columns,64*W,(make model.rat (fun w => w) W o hRep hNo hR columns).2]

def window {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (c : Cursor o T) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+physicalFoot W columns+
    descriptionFoot W o (make model.rat (fun w => w) W o hRep hNo hR columns).1+
    childWindow model W o hRep columns c+fields W (controls model W o hRep hNo hR columns)+128*W

def profile {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+physicalProfile W T o.m K H+
    descriptionProfile W T K H o+childProfile model W T K H o+
    7*(natBits (cap model W T K H o)+W)+160*W

theorem work_shape {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) :
    (make model.rat (fun w => w) W o hRep hNo hR columns).2=childWork model W o hRep columns+64*W := by
  unfold make childWork
  split_ifs
  · rfl
  · simp only [Nat.zero_add]

theorem bounded {n T K : ℕ} (model : RationalCostModel) (W H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hs : GeneralPaperCircleActualWeights.Conserved o)
    (hRich : ∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H)
    (hW : 1≤W) (hFields : binaryWordWidth (o.m+1)≤W)
    (hLight : binaryWordWidth (o.classified.light.size+1)≤W) (hRows : binaryWordWidth (T+1)≤W)
    (c : Cursor o T) : window model W o hRep hNo hR columns c≤profile model W T K H o ∧
      (make model.rat (fun w => w) W o hRep hNo hR columns).2≤price model W T H o := by
  have hPhysical := physical_bound W H columns hRich hPoor
  have hDescription := make_bound model.rat (fun w => w) W W H o hRep hNo hR columns hs hRich hPoor
  have hChild : childWindow model W o hRep columns c≤childProfile model W T K H o := by
    unfold childWindow childProfile
    split_ifs with h
    · exact GeneralPaperCachedPairConstructionStorage.bounded model W H o (hRep h).1 columns hs hRich hPoor hW hFields hLight hRows
        c.commonCount c.rows c.count c.hCommon c.hRows c.hCount c.used c.copied c.active
    · exact Nat.zero_le _
  have hCW : childWork model W o hRep columns≤GeneralPaperCachedPairConstructionStorage.price model W T H o := by
    unfold childWork
    split_ifs with h
    · exact GeneralPaperCachedPairConstructionStorage.work model W H o (hRep h).1 columns hs hRich hPoor hW hFields hLight hRows
    · exact Nat.zero_le _
  have hShape := work_shape model W o hRep hNo hR columns
  have hw : (make model.rat (fun w => w) W o hRep hNo hR columns).2≤price model W T H o := by unfold price;omega
  have hf := fields_bound W (natBits (cap model W T K H o)) (controls model W o hRep hNo hR columns) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤7*(natBits (cap model W T K H o)+W)+32*W at hf
  refine ⟨?_,hw⟩
  unfold window profile
  omega

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (T H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model W T H o) := by
  unfold price GeneralPaperCachedPairConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.originalPrice
    GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  fun_prop

@[fun_prop]
theorem physical_scaling (T m K H : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => physicalProfile W T m K H) := by
  unfold physicalProfile columnsProfile columnProfile arrayProfile
  fun_prop

@[fun_prop]
theorem child_scaling {n : ℕ} (model : RationalCostModel) (T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => childProfile model W T K H o) := by
  unfold childProfile
  split_ifs <;> fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W T K H o) := by
  unfold profile cap descriptionProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
    GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile columnsProfile columnProfile arrayProfile
  fun_prop

end Blotto.GeneralPaperStrategyDescriptionConstructionStorage

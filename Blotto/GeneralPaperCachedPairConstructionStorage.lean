import Blotto.GeneralPaperCachedRowConstructionStorage

/-! Full actual two-player cache construction. Both source dictionaries,
the original reduction, shared cache, complete sorted-reference tables,
active constructor windows, and native partial/result work fields coexist.
The native original reduction supplies weight conservation without replay. -/
namespace Blotto.GeneralPaperCachedPairConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperCachedCircleRows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def price {n : ℕ} (model : RationalCostModel) (W T H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperSharedCacheConstructionStorage.originalPrice model W o+
    2*GeneralPaperCachedRowConstructionStorage.price model W T o.representatives (1+2*H)+128*W
def cap {n : ℕ} (model : RationalCostModel) (W T H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  T+o.m+price model W T H o+128*W+1

def controls {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) : List ℕ :=
  let common := GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o
  let rich := prepare model.rat (fun w => w) W (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
  let poor := prepare model.rat (fun w => w) W (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
  let made := pair model.rat (fun w => w) W o hm columns
  [common.2,rich.2,poor.2,common.2+rich.2,common.2+rich.2+poor.2,128*W,made.2,T,o.m]

def window {n T K : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (commonCount rows count : ℕ) (hCommon : commonCount≤o.classified.light.size) (hRows : rows≤T)
    (hc : count≤o.representatives) (used copied : ℕ) (active : Option (Fin o.representatives×Fin o.representatives)) : ℕ :=
  GeneralPaperSharedCacheConstructionStorage.originalWindow model W o commonCount hCommon copied+
    GeneralPaperCachedRowConstructionStorage.window model W (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
      rows count hRows hc used copied active+
    GeneralPaperCachedRowConstructionStorage.window model W (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
      rows count hRows hc used copied active+
    GeneralPaperCachedCircleRetainedStorage.pairFoot W o.classified (pair model.rat (fun w => w) W o hm columns).1+
    fields W (controls model W o hm columns)+128*W

def profile {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperSharedCacheConstructionStorage.originalProfile model W o+
    2*GeneralPaperCachedRowConstructionStorage.profile model W T o.classified.heavy.size o.representatives K (1+2*H)+
    GeneralPaperCachedCircleRetainedStorage.pairProfile W T o.classified.heavy.size o.classified.light.size
      o.representatives o.classified.lightWeight K H+
    9*(natBits (cap model W T H o)+W)+160*W

theorem light_sum {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hs : GeneralPaperCircleActualWeights.Conserved o) :
    ∑ j,(GeneralPaperNativeLightWeights.run (fun w => w) W o).1.read j=o.classified.lightWeight := by
  rw [GeneralPaperNativeLightWeights.data]
  change (∑ j,GeneralPaperCircleActualWeights.weights o j)=o.classified.lightWeight at hs
  simpa only [FixedArrayTable.read_ofFn] using hs

theorem work {n T K : ℕ} (model : RationalCostModel) (W H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hs : GeneralPaperCircleActualWeights.Conserved o)
    (hRich : ∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H)
    (hW : 1≤W) (hFields : binaryWordWidth (o.m+1)≤W)
    (hLight : binaryWordWidth (o.classified.light.size+1)≤W) (hRows : binaryWordWidth (T+1)≤W) :
    (pair model.rat (fun w => w) W o hm columns).2≤price model W T H o := by
  have hIndex : binaryWordWidth (o.classified.heavy.size+o.representatives+1)≤W := by rw [←hm];exact hFields
  have hc := GeneralPaperSharedCacheConstructionStorage.original_work model W o (light_sum W o hs) hW hLight
  have hr := GeneralPaperCachedRowConstructionStorage.work model W (1+2*H) (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
    (fun j l => rationalWordWidth_of_height (GeneralPaperPhysicalFieldCast.height hm columns.rich H hRich j l)) hW hIndex hRows
  have hp := GeneralPaperCachedRowConstructionStorage.work model W (1+2*H) (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
    (fun j l => rationalWordWidth_of_height (GeneralPaperPhysicalFieldCast.height hm columns.poor H hPoor j l)) hW hIndex hRows
  unfold pair price
  dsimp only
  omega

theorem bounded {n T K : ℕ} (model : RationalCostModel) (W H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hs : GeneralPaperCircleActualWeights.Conserved o)
    (hRich : ∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H)
    (hW : 1≤W) (hFields : binaryWordWidth (o.m+1)≤W)
    (hLight : binaryWordWidth (o.classified.light.size+1)≤W) (hRowIndex : binaryWordWidth (T+1)≤W)
    (commonCount rows count : ℕ) (hCommon : commonCount≤o.classified.light.size) (hRows : rows≤T)
    (hc : count≤o.representatives) (used copied : ℕ) (active : Option (Fin o.representatives×Fin o.representatives)) :
    window model W o hm columns commonCount rows count hCommon hRows hc used copied active≤profile model W T K H o := by
  have hIndex : binaryWordWidth (o.classified.heavy.size+o.representatives+1)≤W := by rw [←hm];exact hFields
  have hC := GeneralPaperSharedCacheConstructionStorage.original_bounded model W o (light_sum W o hs) hW hLight commonCount hCommon copied
  have hR := GeneralPaperCachedRowConstructionStorage.bounded model W (1+2*H) (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
    (fun j l => rationalWordWidth_of_height (GeneralPaperPhysicalFieldCast.height hm columns.rich H hRich j l))
    hW hIndex hRowIndex rows count hRows hc used copied active
  have hP := GeneralPaperCachedRowConstructionStorage.bounded model W (1+2*H) (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
    (fun j l => rationalWordWidth_of_height (GeneralPaperPhysicalFieldCast.height hm columns.poor H hPoor j l))
    hW hIndex hRowIndex rows count hRows hc used copied active
  have hReturn := GeneralPaperCachedCircleRetainedStorage.pair_bound model.rat (fun w => w) W W H o hm columns hs hRich hPoor
  have hw := work model W H o hm columns hs hRich hPoor hW hFields hLight hRowIndex
  have hShape : (pair model.rat (fun w => w) W o hm columns).2=
      (GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o).2+
      (prepare model.rat (fun w => w) W (GeneralPaperPhysicalFieldCast.columns hm columns.rich)).2+
      (prepare model.rat (fun w => w) W (GeneralPaperPhysicalFieldCast.columns hm columns.poor)).2+128*W := rfl
  have hf := fields_bound W (natBits (cap model W T H o)) (controls model W o hm columns) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤9*(natBits (cap model W T H o)+W)+32*W at hf
  unfold window profile
  omega

theorem original_bounded {n : ℕ} (bits : Bool) (inputModel model : RationalCostModel) (Wv W k T K H : ℕ)
    (input : FixedArrayTable n ℚ) :
    let o := (GeneralPaperOriginalValueReduction.run bits inputModel Wv k input).1
    ∀ (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K),
    (∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H) →
    (∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H) →
    1≤W → binaryWordWidth (o.m+1)≤W → binaryWordWidth (o.classified.light.size+1)≤W → binaryWordWidth (T+1)≤W →
    ∀ (commonCount rows count : ℕ) (hCommon : commonCount≤o.classified.light.size) (hRows : rows≤T)
      (hc : count≤o.representatives) (used copied : ℕ) (active : Option (Fin o.representatives×Fin o.representatives)),
    window model W o hm columns commonCount rows count hCommon hRows hc used copied active≤profile model W T K H o := by
  dsimp only
  intro hm columns hRich hPoor hW hFields hLight hRowIndex commonCount rows count hCommon hRows hc used copied active
  exact bounded model W H _ hm columns (GeneralPaperCircleActualWeights.original_sum bits inputModel Wv k input)
    hRich hPoor hW hFields hLight hRowIndex commonCount rows count hCommon hRows hc used copied active

end Blotto.GeneralPaperCachedPairConstructionStorage

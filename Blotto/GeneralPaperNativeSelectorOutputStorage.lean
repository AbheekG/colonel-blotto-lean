import Blotto.GeneralPaperRowTrimStorage

/-! Erased observers of actual native root/decode/trim/fallback values.
Every finite-index word and returned-list length is intrinsic. Bounds
cover failed root/trim branches without an optimizer-success premise.
The selector still executes each phase once; observers introduce no pass. -/
namespace Blotto.GeneralPaperNativeSelectorOutputStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedLabelStorage GeneralPaperEncodedFixedVector
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rootFootprint {K J : ℕ} (W : ℕ) : Option (Fin J × List (Fin K)) → ℕ
  | none => 32*W
  | some result => rankBits result.1+listFootprint W result.2+64*W

def rootProfile (W K J h : ℕ) : ℕ := 2^h*(rankWord K+34*W)+rankWord J+64*W

theorem root_bound {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    rootFootprint W (GeneralPaperOrderedRootExecution.run bits index price A grid tree budget).1≤rootProfile W K grid.size h := by
  cases hs : (GeneralPaperOrderedRootExecution.run bits index price A grid tree budget).1 with
  | none => simp only [rootFootprint,rootProfile]; omega
  | some result =>
    have hl := GeneralPaperRootReturnedRows.length bits index price A grid tree budget result hs
    have hb := list_power W h result.2 hl.le
    have hr := rank_bound result.1
    simp only [rootFootprint,rootProfile]
    omega

def decodePeak {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) : ℕ :=
  let computed := (GeneralPaperOrderedDPExecution.run bits index price A grid tree).1
  match (GeneralPaperRootSelectPrice.run bits index price A computed.table budget).1 with
  | none => 0
  | some label => GeneralPaperTypedDecodeStorage.peak W h computed label

theorem decode_peak_bound {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    decodePeak bits index price W A grid tree budget≤GeneralPaperTypedDecodeStorage.profile W K grid.size h h := by
  unfold decodePeak
  dsimp only
  split
  · exact Nat.zero_le _
  · exact GeneralPaperTypedDecodeStorage.bounded W h _ _

def finishWindow {K J : ℕ} (index : ℕ → ℕ) (W A m : ℕ) : Option (Fin J × List (Fin K)) → ℕ
  | none => 32*W
  | some result => GeneralPaperRowTrimStorage.window index W A m result.2

theorem finish_bound {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A trimA m : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    finishWindow index W trimA m (GeneralPaperOrderedRootExecution.run bits index price A grid tree budget).1≤
      GeneralPaperRowTrimStorage.profile W K m (2^h)+32*W := by
  cases hs : (GeneralPaperOrderedRootExecution.run bits index price A grid tree budget).1 with
  | none => simp only [finishWindow]; omega
  | some result =>
    have hb := GeneralPaperRowTrimStorage.returned_window index W trimA m result.2
    rw [GeneralPaperRootReturnedRows.length bits index price A grid tree budget result hs] at hb
    exact hb.trans (Nat.le_add_right _ _)

def fallbackPrefix (bits : Bool) (index : ℕ → ℕ) (W A m k count : ℕ) (hc : count≤m) : ℕ :=
  arrayFootprint W m (PaperIndexedArrayConstruction.fill index
    (if bits then GeneralPaperSummaryArrayExecution.arrayWord A m else A)
    (fun _ : Fin m => ((0 : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*A)) count hc).1

def window {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) (count : ℕ) (hc : count≤m) : ℕ :=
  let primitive := if bits then price else fun _ => 1
  let tree := (GeneralPaperNativeSelectorExecution.prepareTree bits index price A prepared T r weights prefixes).1
  let root := (GeneralPaperOrderedRootExecution.run bits index primitive A prepared.grid tree (budget B)).1
  let trimA := if bits then GeneralPaperRowTrimPrice.word A m prepared.parameters.leafCount else A
  decodePeak bits index primitive W A prepared.grid tree (budget B)+rootFootprint W root+
    finishWindow index W trimA m root+
    GeneralPaperRowTrimStorage.optionalFootprint W (GeneralPaperNativeSelectorExecution.run bits index price A prepared T r weights prefixes B).1+
    rowFootprint W (GeneralPaperZeroRowPrice.run bits index A m k).1+
    rowFootprint W (GeneralPaperNativeSelectorExecution.pick bits index price A prepared T r weights prefixes B).1+
    fallbackPrefix bits index W A m k count hc+128*W

def profile (W m K J h : ℕ) : ℕ :=
  GeneralPaperTypedDecodeStorage.profile W K J h h+rootProfile W K J h+
    GeneralPaperRowTrimStorage.profile W K m (2^h)+4*m*(rankWord K+W)+352*W

theorem native {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) (count : ℕ) (hc : count≤m) :
    window bits index price W A prepared T r weights prefixes B count hc≤
      profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size prepared.parameters.height := by
  let primitive := if bits then price else fun _ => 1
  let tree := (GeneralPaperNativeSelectorExecution.prepareTree bits index price A prepared T r weights prefixes).1
  let trimA := if bits then GeneralPaperRowTrimPrice.word A m prepared.parameters.leafCount else A
  have hd := decode_peak_bound bits index primitive W A prepared.grid tree (budget B)
  have hr := root_bound bits index primitive W A prepared.grid tree (budget B)
  have hf := finish_bound bits index primitive W A trimA m prepared.grid tree (budget B)
  have ho := GeneralPaperRowTrimStorage.optional_bound W
    (GeneralPaperNativeSelectorExecution.run bits index price A prepared T r weights prefixes B).1
  have hz := GeneralPaperRowTrimStorage.zero bits index W A m k
  have hp := row_bound W (GeneralPaperNativeSelectorExecution.pick bits index price A prepared T r weights prefixes B).1
  have hprefix := indexed_reserved_prefix index
    (if bits then GeneralPaperSummaryArrayExecution.arrayWord A m else A) W count
    (fun _ : Fin m => ((0 : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*A)) hc
  change fallbackPrefix bits index W A m k count hc≤_ at hprefix
  unfold window profile
  dsimp only
  change _≤GeneralPaperTypedDecodeStorage.profile W _ prepared.grid.size prepared.parameters.height prepared.parameters.height+
    rootProfile W _ prepared.grid.size prepared.parameters.height+
    GeneralPaperRowTrimStorage.profile W _ m (2^prepared.parameters.height)+
    4*m*(rankWord ((GeneralPaperSourceParameters.prepare k).summarySize+2)+W)+352*W
  nlinarith only [hd,hr,hf,ho,hz,hp,hprefix]

theorem successful_copy {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A trimA m count : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag)
    (result : Fin grid.size × List (Fin K))
    (hs : (GeneralPaperOrderedRootExecution.run bits index price A grid tree budget).1=some result)
    (hm : m≤2^h) (hc : count≤m) :
    ∃ hfit : m≤result.2.toArray.size,
      listFootprint W result.2+arrayFootprint W result.2.length (PaperListReferenceArray.run index trimA result.2).1+
        arrayFootprint W m (PaperIndexedArrayConstruction.fill index trimA
          (fun i : Fin m => (result.2.toArray[i.val]'(i.isLt.trans_le hfit),64*trimA)) count hc).1+
        GeneralPaperRowTrimStorage.loopFrames W m result.2.length+64*W≤GeneralPaperRowTrimStorage.profile W K m (2^h) := by
  have hl := GeneralPaperRootReturnedRows.length bits index price A grid tree budget result hs
  have hfit : m≤result.2.toArray.size := by rw [List.size_toArray,hl]; exact hm
  refine ⟨hfit,?_⟩
  have hw := GeneralPaperRowTrimStorage.copying_window index W trimA m count result.2 hfit hc
  simpa only [hl] using hw

theorem source_copy {m K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A trimA lambda k Qv count : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared)
    (hPrepared : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (tree : Tree Tag K prepared.parameters.height) (budget : Tag)
    (result : Fin prepared.grid.size × List (Fin K))
    (hs : (GeneralPaperOrderedRootExecution.run bits index price A prepared.grid tree budget).1=some result)
    (hc : count≤m) :
    ∃ hfit : m≤result.2.toArray.size,
      listFootprint W result.2+arrayFootprint W result.2.length (PaperListReferenceArray.run index trimA result.2).1+
        arrayFootprint W m (PaperIndexedArrayConstruction.fill index trimA
          (fun i : Fin m => (result.2.toArray[i.val]'(i.isLt.trans_le hfit),64*trimA)) count hc).1+
        GeneralPaperRowTrimStorage.loopFrames W m result.2.length+64*W≤
          GeneralPaperRowTrimStorage.profile W K m (2^prepared.parameters.height) := by
  have hh : prepared.parameters.height=(GeneralPaperProfitParameters.parameters m lambda k Qv).height := by
    rw [hPrepared]
    rfl
  have hm : m≤2^prepared.parameters.height := by
    rw [hh]
    have h := GeneralPaperProfitParameters.covers_fields m lambda k Qv
    rw [GeneralPaperProfitParameters.leaf_count_spec] at h
    exact h
  exact successful_copy bits index price W A trimA m count prepared.grid tree budget result hs hm hc

end Blotto.GeneralPaperNativeSelectorOutputStorage

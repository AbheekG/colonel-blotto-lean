import Blotto.GeneralPaperForestFamilyConstructionStorage
import Blotto.GeneralPaperSummaryFamilyStorage

/-! Complete four-family summary construction joins reserved old/new
buffers, full returned arrays, outer controls/height scratch and one guarded
inner summary/quantile child. No old tree or parameter preparation is replayed. -/
namespace Blotto.GeneralPaperFourSummaryConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def returnedFamilyProfile (W m k height : ℕ) : ℕ := m*(GeneralPaperSummaryFamilyStorage.summaryProfile W k height+W)+32*W

theorem returned_family_mono (W m k h H : ℕ) (hh : h≤H) : returnedFamilyProfile W m k h≤returnedFamilyProfile W m k H := by
  unfold returnedFamilyProfile GeneralPaperSummaryFamilyStorage.summaryProfile
  gcongr

theorem family_returned (model : RationalCostModel) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (nodes : FixedArrayTable m (Node height)) (hh : height≤lambda+1)
    (hv : ∀ j,Valid lambda k (nodes.read j)) (hp : ∀ j,PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 (nodes.read j)) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W)
      (GeneralPaperSummaryFamilyPrice.run true (fun w => w) model.rat W m lambda k Qv c hc digits height nodes).1≤returnedFamilyProfile W m k height := by
  apply GeneralPaperEncodedFixedVector.bounded
  intro j
  rw [GeneralPaperSummaryFamilyPrice.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperSummaryFamilyStorage.native_summary true (fun w => w) model.rat W m lambda k Qv digits height c hc (nodes.read j) hh (hv j) (hp j)

def arraysFootprint {m k : ℕ} (W : ℕ) (arrays : GeneralPaperFourSummaryArrays.Arrays m k) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.p+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.q+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.lambda+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.mu+128*W

def returnedProfile (W m lambda k : ℕ) : ℕ := 4*returnedFamilyProfile W m k (lambda+1)+128*W

theorem returned (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hv : GeneralPaperCatalogueTreeCache.Valid a k trees) (hp : Paths a k trees) :
    arraysFootprint W (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc digits trees).1≤returnedProfile W m a.lambda k := by
  have h0 := (family_returned model W m a.lambda k Qv digits a.lambda c hc trees.p (by omega) (hv .p) (hp .p)).trans
    (returned_family_mono W m k a.lambda (a.lambda+1) (by omega))
  have h1 := (family_returned model W m a.lambda k Qv digits a.lambda c hc trees.q (by omega) (hv .q) (hp .q)).trans
    (returned_family_mono W m k a.lambda (a.lambda+1) (by omega))
  have h2 := family_returned model W m a.lambda k Qv digits (a.lambda+1) c hc trees.lambda (Nat.le_refl _) (hv .lambda) (hp .lambda)
  have h3 := family_returned model W m a.lambda k Qv digits (a.lambda+1) c hc trees.mu (Nat.le_refl _) (hv .mu) (hp .mu)
  dsimp only [arraysFootprint,GeneralPaperFourSummaryArrays.run,returnedProfile]
  omega

theorem inner_profile_mono (model : RationalCostModel) (W m lambda k Qv h H : ℕ) (hh : h≤H) :
    GeneralPaperSummaryConstructionStorage.profile model W m lambda k Qv h≤GeneralPaperSummaryConstructionStorage.profile model W m lambda k Qv H := by
  have hprice := model.monotone (show 8+2*(h+1)≤8+2*(H+1) by omega)
  unfold GeneralPaperSummaryConstructionStorage.profile GeneralPaperQuantileQueryStorage.profile GeneralPaperQuantileSearchPrice.profile
  dsimp only
  gcongr

def prefixes (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (count : ℕ) (hcount : count≤m) : ℕ :=
  GeneralPaperSummaryFamilyStorage.buffer true (fun w => w) model.rat W m a.lambda k Qv c hc digits a.lambda trees.p count hcount+
    GeneralPaperSummaryFamilyStorage.buffer true (fun w => w) model.rat W m a.lambda k Qv c hc digits a.lambda trees.q count hcount+
    GeneralPaperSummaryFamilyStorage.buffer true (fun w => w) model.rat W m a.lambda k Qv c hc digits (a.lambda+1) trees.lambda count hcount+
    GeneralPaperSummaryFamilyStorage.buffer true (fun w => w) model.rat W m a.lambda k Qv c hc digits (a.lambda+1) trees.mu count hcount

def active {m : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (a : Alphabet) (trees : Trees m a.lambda) (digits count innerCount : ℕ) (hi : innerCount≤c.controls.source.summarySize)
    (r : Fin c.controls.source.summarySize) (learner : Learner) : ℕ :=
  if h : count<m then GeneralPaperSummaryConstructionStorage.window model (fun w => w) W c digits
    (treeHeight learner a.lambda) (node learner trees ⟨count,h⟩) innerCount hi r+16*W else 0

def controlWord (m lambda k : ℕ) : ℕ :=
  natBits (m+1)+natBits (lambda+2)+natBits (k+1)+natBits ((GeneralPaperSourceParameters.prepare k).summarySize+2)

def window (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (count innerCount : ℕ) (hcount : count≤m)
    (hi : innerCount≤c.controls.source.summarySize) (r : Fin c.controls.source.summarySize) (learner : Learner) : ℕ :=
  2*prefixes model W m k Qv a c hc digits trees count hcount+
    arraysFootprint W (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc digits trees).1+
    active model W c a trees digits count innerCount hi r learner+
    fields W [m,a.lambda,a.lambda+1,k,count,count+1,(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+1,innerCount,innerCount+1]+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) a.lambda 1+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  8*GeneralPaperSummaryFamilyStorage.familyProfile W m k (lambda+1)+returnedProfile W m lambda k+
    GeneralPaperSummaryConstructionStorage.profile model W m lambda k Qv (lambda+1)+16*W+
    (10*(controlWord m lambda k+W)+32*W)+2*model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+256*W

theorem bounded (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hd : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hv : GeneralPaperCatalogueTreeCache.Valid a k trees) (hp : Paths a k trees)
    (count innerCount : ℕ) (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (r : Fin c.controls.source.summarySize) (learner : Learner) :
    window model W m k Qv a c hc digits trees count innerCount hcount hi r learner≤profile model W m a.lambda k Qv := by
  have hbuf := GeneralPaperSummaryFamilyStorage.four_prefixes true (fun w => w) model.rat W m k Qv digits a c hc trees hv hp count hcount
  change prefixes model W m k Qv a c hc digits trees count hcount≤_ at hbuf
  have hr := returned model W m k Qv a c hc digits trees hv hp
  have ha : active model W c a trees digits count innerCount hi r learner≤
      GeneralPaperSummaryConstructionStorage.profile model W m a.lambda k Qv (a.lambda+1)+16*W := by
    unfold active
    split
    · exact Nat.add_le_add_right ((GeneralPaperSummaryConstructionStorage.bounded model (fun w => w) W m a.lambda k Qv digits _ c hc hd _
        (tree_height_bound learner a.lambda) (hv learner _) (hp learner _) innerCount hi r).trans
          (inner_profile_mono model W m a.lambda k Qv _ (a.lambda+1) (tree_height_bound learner a.lambda))) _
    · exact Nat.zero_le _
  have hn : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  have hinner : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize := hi.trans_eq hn
  have hctrl := fields_bound W (controlWord m a.lambda k)
    [m,a.lambda,a.lambda+1,k,count,count+1,(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+1,innerCount,innerCount+1] (by
      have hmw := GeneralPaperRankStorageMonotonicity.nat_word m (m+1) (by omega)
      have hlw := GeneralPaperRankStorageMonotonicity.nat_word a.lambda (a.lambda+2) (by omega)
      have hl1 := GeneralPaperRankStorageMonotonicity.nat_word (a.lambda+1) (a.lambda+2) (by omega)
      have hkw := GeneralPaperRankStorageMonotonicity.nat_word k (k+1) (by omega)
      have hc0 := GeneralPaperRankStorageMonotonicity.nat_word count (m+1) (by omega)
      have hc1 := GeneralPaperRankStorageMonotonicity.nat_word (count+1) (m+1) (by omega)
      have hs0 := GeneralPaperRankStorageMonotonicity.nat_word (GeneralPaperSourceParameters.prepare k).summarySize ((GeneralPaperSourceParameters.prepare k).summarySize+2) (by omega)
      have hs1 := GeneralPaperRankStorageMonotonicity.nat_word ((GeneralPaperSourceParameters.prepare k).summarySize+1) ((GeneralPaperSourceParameters.prepare k).summarySize+2) (by omega)
      have hi0 := GeneralPaperRankStorageMonotonicity.nat_word innerCount ((GeneralPaperSourceParameters.prepare k).summarySize+2) (by omega)
      have hi1 := GeneralPaperRankStorageMonotonicity.nat_word (innerCount+1) ((GeneralPaperSourceParameters.prepare k).summarySize+2) (by omega)
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals (unfold controlWord; omega))
  have hheight := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun x y => x+y) a.lambda 1 (a.lambda+2)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (model.monotone (GeneralPaperQuantileDescentControls.height_word m a.lambda k Qv)))
  simp only [List.length_cons,List.length_nil] at hctrl
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperFourSummaryConstructionStorage

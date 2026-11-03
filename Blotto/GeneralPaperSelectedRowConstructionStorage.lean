import Blotto.GeneralPaperSourceUpdateConstructionStorage

/-! Selected-row code copies retain full code words, borrowed catalogue
and row indices, reserved old/new buffers, frames and complete returns.
Both native row constructors join the actual source/update/selector context;
there is no decoder, re-encoding or second selector pass. -/
namespace Blotto.GeneralPaperSelectedRowConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def callback {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) : ℕ × ℕ :=
  let code := (r.data.codes.read j).read (row.read j)
  (code,natBits code+64*W+64*GeneralPaperSummaryArrayExecution.arrayWord W ((GeneralPaperSourceParameters.prepare k).summarySize+2))

theorem native_data {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) :
    (PaperIndexedArrayConstruction.run (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) (callback W r row)).1=
      (GeneralPaperSelectedRowCodesPrice.run true (fun w => w) W r.data row).1 := rfl

theorem value_bound {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    (callback W r row j).1≤2^r.alphabet.lambda := by
  have h := GeneralPaperCatalogueArrays.code_bound r.alphabet r.response k r.summaries j (row.read j)
  rw [←r.data_spec] at h
  exact h.le.trans_eq r.alphabet.dyadic

def elementWindow {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) : ℕ :=
  fields W [(callback W r row j).1]+fields W [m,j.val,(GeneralPaperSourceParameters.prepare k).summarySize+2,(row.read j).val]+
    (callback W r row j).2+256*W

def elementProfile (W m lambda k : ℕ) : ℕ :=
  let L := GeneralPaperDecoderControls.operandWidth lambda
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  (1*(L+W)+32*W)+(4*(natBits (m+1)+natBits (K+1)+W)+32*W)+
    L+64*W+64*GeneralPaperSummaryArrayExecution.arrayWord W K+256*W

theorem element_bounded {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    elementWindow W r row j≤elementProfile W m r.alphabet.lambda k := by
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  have hw : natBits (callback W r row j).1≤GeneralPaperDecoderControls.operandWidth r.alphabet.lambda :=
    GeneralPaperSelectedRowCodesPrice.code_word r row j
  have hf := fields_bound W (GeneralPaperDecoderControls.operandWidth r.alphabet.lambda) [(callback W r row j).1] (by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    exact hw)
  have hi := fields_bound W (natBits (m+1)+natBits (K+1)) [m,j.val,K,(row.read j).val] (by
    intro x hx
    have hm := GeneralPaperRankStorageMonotonicity.nat_word m (m+1) (by omega)
    have hj := GeneralPaperRankStorageMonotonicity.nat_word j.val (m+1) (by have := j.isLt; omega)
    have hK := GeneralPaperRankStorageMonotonicity.nat_word K (K+1) (by omega)
    have hq := GeneralPaperRankStorageMonotonicity.nat_word (row.read j).val (K+1) (by have := (row.read j).isLt; omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals omega)
  have hp : (callback W r row j).2≤GeneralPaperDecoderControls.operandWidth r.alphabet.lambda+
      64*W+64*GeneralPaperSummaryArrayExecution.arrayWord W K := Nat.add_le_add_right (Nat.add_le_add_right hw _) _
  simp only [List.length_cons,List.length_nil] at hf hi
  dsimp only [elementWindow,elementProfile]
  dsimp only [K] at hi hp
  omega

def active {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (count : ℕ) : ℕ :=
  if h : count<m then elementWindow W r row ⟨count,h⟩ else 0

def window {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W (callback W r row) count hc+active W r row count+256*W

def profile (W m lambda k : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W m (2^lambda)+elementProfile W m lambda k+256*W

theorem bounded {m k : ℕ} (W : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (count : ℕ) (hc : count≤m) :
    window W r row count hc≤profile W m r.alphabet.lambda k := by
  have hf := GeneralPaperNativeNatFillStorage.bounded W _ _ (value_bound W r row) count hc
  have ha : active W r row count≤elementProfile W m r.alphabet.lambda k := by
    unfold active
    split
    · exact element_bounded W r row _
    · exact Nat.zero_le _
  exact Nat.add_le_add_right (Nat.add_le_add hf ha) _

def sourceWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  let rows := rowsAt current time
  GeneralPaperSourceUpdateConstructionStorage.window model W k Qv a shared weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount+
    window W cache.candidate rows.candidate rowCount hr+window W cache.response rows.response rowCount hr

def sourceProfile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperSourceUpdateConstructionStorage.profile model W k Qv a weights Bc Br+2*profile W m a.lambda k

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) :
    sourceWindow model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      sourceProfile model W k Qv a weights Bc Br := by
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let rows := rowsAt (epochRun shared a k trees) time
  have hbase := GeneralPaperSourceUpdateConstructionStorage.actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right innerCount
  have hp := bounded W cache.candidate rows.candidate rowCount hr
  have hq := bounded W cache.response rows.response rowCount hr
  have hca : cache.candidate.alphabet=a := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=a := by rw [cache.response_spec]; rfl
  rw [hca] at hp
  rw [hra] at hq
  exact (Nat.add_le_add (Nat.add_le_add hbase hp) hq).trans_eq (by unfold sourceProfile; ring)

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) (innerCount : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    ∀ left right : Fin (GeneralPaperProfitParameters.prepare m ready.1.1.1.2.lambda k Qv).grid.size,
    sourceWindow model W k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      sourceProfile model W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  intro left right
  exact actual model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht
    j i count copied rowCount hc hr left right innerCount

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount : ℕ) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      sourceWindow model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+sourceProfile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right innerCount)

end Blotto.GeneralPaperSelectedRowConstructionStorage

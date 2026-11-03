import Blotto.GeneralPaperNaturalSumStorage
import Blotto.GeneralPaperStoredScoreMaximum

/-! Native stored-score maximum guard. The actual loaded top-score array,
every load-constructor prefix/frame, natural sum prefixes and primitive
peak, top-index subtraction and native return metadata are included. The
matrix is borrowed; the caller retains its payload and the original DP table. -/
namespace Blotto.GeneralPaperStoredMaximumStorage
open GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperSummaryArrayExecution GeneralPaperScoreConstructionStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def callback {m K : ℕ} (W : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K)) (j : Fin m) : ℕ×ℕ :=
  (((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1,64*arrayWord W m)

def loadPrice (W m : ℕ) : ℕ := m*(64*arrayWord W m)+(m+1)*(6*arrayWord W m+10*binaryWordWidth (m+1)+28)

theorem load_work {m K : ℕ} (W : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K)) :
    (GeneralPaperStoredScoreMaximum.values true W hK matrix).2≤loadPrice W m := by
  have h := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) (arrayWord W m) (callback W hK matrix)
  change (GeneralPaperStoredScoreMaximum.values true W hK matrix).2≤
    (∑ _ : Fin m,64*arrayWord W m)+(m+1)*(6*arrayWord W m+10*1*binaryWordWidth (m+1)+28) at h
  simpa only [loadPrice,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] using h

theorem total_bound {m K : ℕ} (model : RationalCostModel) (W S : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K))
    (hs : (∑ j,((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S) :
    (GeneralPaperValueWeightSum.scan true model W (GeneralPaperStoredScoreMaximum.values true W hK matrix).1 m le_rfl).1≤S := by
  rw [GeneralPaperValueWeightSum.total,GeneralPaperStoredScoreMaximum.values_data]
  simpa only [FixedArrayTable.read_ofFn] using hs

theorem item_bound {m K : ℕ} (S : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K))
    (hs : (∑ j,((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S) (j : Fin m) :
    ((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1≤S :=
  (Finset.single_le_sum (f:=fun t => ((matrix.read t).read (GeneralPaperScoreMaximum.topLabel K hK)).1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hs

def maximumPrice (model : RationalCostModel) (W m K S : ℕ) : ℕ :=
  m*(2*model.rat (1+binaryWordWidth S)+256*arrayWord W m)+160*arrayWord W m+2*model.rat (1+binaryWordWidth K)

def metadataCap (model : RationalCostModel) (W m K S : ℕ) : ℕ :=
  m+K+S+1+loadPrice W m+GeneralPaperNaturalSumStorage.workCap model W m S+maximumPrice model W m K S

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K))
    (loadCount : ℕ) (hl : loadCount≤m) (sumCount : ℕ) (hc : sumCount≤m) : ℕ :=
  let loaded := GeneralPaperStoredScoreMaximum.values true W hK matrix
  let total := GeneralPaperValueWeightSum.scan true model W loaded.1 m le_rfl
  let result := GeneralPaperStoredScoreMaximum.run true model W hK matrix
  reservedFootprint W m natBits (PaperIndexedArrayConstruction.fill (fun w => w) (arrayWord W m)
      (callback W hK matrix) loadCount hl).1+GeneralPaperEncodedNatArray.footprint W loaded.1+
    constructorFrames (fun w => w) (arrayWord W m) W (callback W hK matrix) loadCount hl+
    GeneralPaperNaturalSumStorage.frames model W loaded.1 sumCount hc+GeneralPaperNaturalSumStorage.primitivePeak model W loaded.1 sumCount hc+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1+
    fields W [m,K,K-1,loaded.2,total.1,total.2,result.1,result.2]+256*arrayWord W m

def profile (model : RationalCostModel) (W m K S : ℕ) : ℕ :=
  (m*(natBits S+W)+64*W)+(m*(natBits S+W)+32*W)+constructorProfile W m (loadPrice W m)+
    GeneralPaperNaturalSumStorage.profile model W m S+2*model.rat (1+binaryWordWidth K)+
    8*(natBits (metadataCap model W m K S)+W)+32*W+256*arrayWord W m

theorem bounded {m K : ℕ} (model : RationalCostModel) (W S : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (Field K))
    (hs : (∑ j,((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S)
    (loadCount : ℕ) (hl : loadCount≤m) (sumCount : ℕ) (hc : sumCount≤m) :
    window model W hK matrix loadCount hl sumCount hc≤profile model W m K S := by
  let loaded := GeneralPaperStoredScoreMaximum.values true W hK matrix
  let total := GeneralPaperValueWeightSum.scan true model W loaded.1 m le_rfl
  let result := GeneralPaperStoredScoreMaximum.run true model W hK matrix
  have hTotal := total_bound model W S hK matrix hs
  change total.1≤S at hTotal
  have hLoadWork := load_work W hK matrix
  change loaded.2≤loadPrice W m at hLoadWork
  have hSumWork := GeneralPaperNaturalSumStorage.prefix_work model W S loaded.1 hTotal m le_rfl
  change total.2≤GeneralPaperNaturalSumStorage.workCap model W m S at hSumWork
  have hValue : result.1≤S := by rw [GeneralPaperStoredScoreMaximum.data]; exact hs
  have hWork := GeneralPaperStoredScoreMaximum.bit_work model W S hK matrix hs
  change result.2≤maximumPrice model W m K S at hWork
  have hPrefix := indexed_reserved_prefix (fun w => w) (arrayWord W m) W (natBits S) natBits (callback W hK matrix)
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (item_bound S hK matrix hs j)) 1) loadCount hl
  have hArray := GeneralPaperEncodedNatArray.bounded W (natBits S) loaded.1 (by
    intro j
    exact Nat.add_le_add_left (binaryWordWidth_mono ((GeneralPaperValueWeightSum.item_le_total true model W loaded.1 j).trans hTotal)) 1)
  have hFrames := constructor_bound (fun w => w) (arrayWord W m) W (loadPrice W m) (callback W hK matrix) hLoadWork loadCount hl
  have hSum := GeneralPaperNaturalSumStorage.bounded model W S loaded.1 hTotal sumCount hc
  have hTop := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b) K 1 K le_rfl
    (by omega) (Nat.sub_le K 1)
  have hf := fields_bound W (natBits (metadataCap model W m K S)) [m,K,K-1,loaded.2,total.1,total.2,result.1,result.2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap model W m K S)+W)+32*W at hf
  dsimp only [loaded,total,result] at *
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperStoredMaximumStorage

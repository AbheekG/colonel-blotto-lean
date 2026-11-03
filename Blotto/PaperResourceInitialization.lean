import Blotto.PaperStoredFallbackConstruction

/-! Source initialization builds its resource array, index labels and strict
active list with priced loops. The runtime fields and typed state equal the
existing initial state. Rational copies/comparisons retain their old ledger;
reference/index/list and record fields are added explicitly in the paper model.
-/

namespace Blotto.PaperResourceInitialization
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def labels (primitive : ℕ → ℕ) (A n : ℕ) : List (Fin n) × ℕ :=
  let indexed := PaperIndexedArrayConstruction.run primitive A (fun j : Fin n => (j,binaryWordWidth (j.val+1)))
  (StoredArrayReferenceList.list indexed.1.data,indexed.2+StoredArrayReferenceList.work primitive A n)

theorem labels_data (primitive : ℕ → ℕ) (A n : ℕ) : (labels primitive A n).1 = List.finRange n := by
  unfold labels
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,StoredArrayReferenceList.list_data]
  simp only [FixedArrayTable.ofFn,Array.toList_ofFn,List.finRange]

theorem labels_work (primitive : ℕ → ℕ) (A n : ℕ) :
    (labels primitive A n).2 = (∑ j : Fin n,binaryWordWidth (j.val+1))+
      PaperIndexedArrayConstruction.overhead primitive A n n+StoredArrayReferenceList.work primitive A n := by
  exact congrArg (fun w => w+StoredArrayReferenceList.work primitive A n)
    (PaperIndexedArrayConstruction.run_work primitive A (fun j : Fin n => (j,binaryWordWidth (j.val+1))))

def filterStepWork {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (j : Fin n) : ℕ :=
  6*A+2*primitive (binaryWordWidth (j.val+1))+2*binaryWordWidth (j.val+1)+12

def filterOverhead {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ) : List (Fin n) → ℕ
  | [] => 2*A+4
  | j::rest => filterStepWork primitive A j+filterOverhead primitive A rest

def filterRun {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (L r : Fin n → ℚ) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([],2*A+4)
  | j::rest =>
      let keep := rationalFractionalAt L r j
      let later := filterRun model primitive A L r rest
      (if keep then j::later.1 else later.1,
        rationalFractionalBitCost model L r j+filterStepWork primitive A j+later.2)

theorem filterRun_data {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (L r : Fin n → ℚ) (items : List (Fin n)) :
    (filterRun model primitive A L r items).1 = items.filter (rationalFractionalAt L r) := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [filterRun,List.filter_cons,ih]

theorem filterRun_work {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (L r : Fin n → ℚ) (items : List (Fin n)) :
    (filterRun model primitive A L r items).2 =
      (items.map (rationalFractionalBitCost model L r)).sum+filterOverhead primitive A items := by
  induction items with
  | nil => simp only [filterRun,List.map_nil,List.sum_nil,filterOverhead,Nat.zero_add]
  | cons j rest ih => simp only [filterRun,List.map_cons,List.sum_cons,filterOverhead,ih]; omega

theorem filterOverhead_bound {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (A : ℕ) (items : List (Fin n)) :
    filterOverhead primitive A items ≤
      items.length*(6*A+(2*c+2)*binaryWordWidth (n+1)+12)+2*A+4 := by
  induction items with
  | nil => simp only [filterOverhead,List.length_nil,Nat.zero_mul,Nat.zero_add]; omega
  | cons j rest ih =>
      have hw := binaryWordWidth_mono (show j.val+1 ≤ n+1 by omega)
      have hp := (hPrimitive (binaryWordWidth (j.val+1))).trans (Nat.mul_le_mul_left c hw)
      simp only [filterOverhead,filterStepWork,List.length_cons]
      nlinarith only [ih,hw,hp]

def build {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    (RationalResourceArray n × List (Fin n)) × ℕ :=
  let array := PaperIndexedArrayConstruction.run primitive A (fun j => (r j,2*rationalWordWidth (r j)))
  let row := PaperStoredRowConstruction.resourceArray array.1
  let indices := labels primitive A n
  let active := filterRun model primitive A L row.allocation indices.1
  ((row,active.1),array.2+indices.2+active.2+4*A+8)

theorem build_data {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    (build model primitive A L r).1 =
      ((RationalActiveResources.initial L r).resource,(RationalActiveResources.initial L r).active) := by
  unfold build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,labels_data,filterRun_data]
  change (RationalResourceArray.ofAllocation r,
    (List.finRange n).filter (rationalFractionalAt L (RationalResourceArray.ofAllocation r).allocation)) = _
  rfl

def metadata (primitive : ℕ → ℕ) (A n : ℕ) : ℕ :=
  PaperIndexedArrayConstruction.overhead primitive A n n+(labels primitive A n).2+
    filterOverhead primitive A (List.finRange n)+4*A+8

theorem build_work {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    (build model primitive A L r).2 = rationalInitialDataBitCost model L r+metadata primitive A n := by
  unfold build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work,PaperIndexedArrayConstruction.run_data,
    labels_data,filterRun_work]
  change _+_+(((List.finRange n).map (rationalFractionalBitCost model L
    (RationalResourceArray.ofAllocation r).allocation)).sum+_)+_+_ = _
  rw [RationalResourceArray.allocation_ofAllocation]
  unfold rationalInitialDataBitCost rationalInitialResourceCopyBitCost rationalInitialFractionalBitCost metadata
  rw [Finset.mul_sum]
  dsimp only
  omega

def initial {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    RationalActiveResources L × ℕ :=
  let returned := build model primitive A L r
  have hData := build_data model primitive A L r
  (⟨returned.1.1,returned.1.2,
    by rw [congrArg Prod.snd hData]; exact (RationalActiveResources.initial L r).nodup,
    by rw [congrArg Prod.fst hData,congrArg Prod.snd hData]; exact (RationalActiveResources.initial L r).membership⟩,
    returned.2)

theorem initial_data {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    (initial model primitive A L r).1 = RationalActiveResources.initial L r := by
  have hr := congrArg Prod.fst (build_data model primitive A L r)
  have ha := congrArg Prod.snd (build_data model primitive A L r)
  have hExt (first second : RationalActiveResources L)
      (hResource : first.resource=second.resource) (hActive : first.active=second.active) : first=second := by
    cases first
    cases second
    cases hResource
    cases hActive
    rfl
  exact hExt (initial model primitive A L r).1 (RationalActiveResources.initial L r) hr ha

theorem initial_work {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (L r : Fin n → ℚ) :
    (initial model primitive A L r).2 = rationalInitialDataBitCost model L r+metadata primitive A n :=
  build_work model primitive A L r

theorem metadata_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (n W : ℕ) (hn : n ≤ W) (hW : 1 ≤ W) (hLog : binaryWordWidth (W+2)+1 ≤ W) :
    metadata primitive (StoredArrayReferenceList.poolAddressWidth n W) n ≤ 1024*(c+1)*(n+1)*W := by
  let A := StoredArrayReferenceList.poolAddressWidth n W
  have hIndex : binaryWordWidth (n+1) ≤ W :=
    ((binaryWordWidth_mono (by omega : n+1 ≤ W+2)).trans (Nat.le_succ _)).trans hLog
  have hWord : binaryWordWidth (W+1) ≤ W :=
    ((binaryWordWidth_mono (by omega : W+1 ≤ W+2)).trans (Nat.le_succ _)).trans hLog
  have hAddress := StoredArrayReferenceList.poolAddressWidth_log_bound n W
  have hA : A ≤ 2*W := by dsimp only [A]; omega
  have hLabels : (∑ j : Fin n,binaryWordWidth (j.val+1)) ≤ n*W := by
    calc
      _ ≤ ∑ _j : Fin n,W := Finset.sum_le_sum (fun j _ =>
        (binaryWordWidth_mono (show j.val+1 ≤ n+1 by omega)).trans hIndex)
      _ = _ := by simp
  have hOverhead := (PaperIndexedArrayConstruction.pool_overhead_bound primitive c hPrimitive n W hn).trans
    (Nat.mul_le_mul_left (64*(c+1)*(n+1)) hLog)
  have hExtract := StoredArrayReferenceList.pool_work_bound primitive c hPrimitive n W
  have hExtractWord := Nat.mul_le_mul_left ((5*c+6)*(n+1)) (show A+1 ≤ 3*W by omega)
  have hFilter := filterOverhead_bound primitive c hPrimitive A (List.finRange n)
  simp only [List.length_finRange] at hFilter
  have hFilterWord := Nat.mul_le_mul_left (n*(2*c+2)) hIndex
  have hARepeat := Nat.mul_le_mul_left (6*n) hA
  have hLoopPad := Nat.mul_le_mul_left (12*n) hW
  have hPad : W ≤ (n+1)*W := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1 ≤ n+1 by omega)
  have hSmall := Nat.mul_le_mul_left (64*(c+1)) hPad
  change metadata primitive A n ≤ 1024*(c+1)*(n+1)*W
  unfold metadata
  rw [labels_work]
  change _ ≤ 1024*(c+1)*(n+1)*W
  change StoredArrayReferenceList.work primitive A n ≤ (5*c+6)*(n+1)*(A+1) at hExtract
  change PaperIndexedArrayConstruction.overhead primitive A n n ≤ 64*(c+1)*(n+1)*W at hOverhead
  nlinarith only [hLabels,hOverhead,hExtract,hExtractWord,hFilter,hFilterWord,hARepeat,hLoopPad,hPad,hSmall,hA,hW]

end Blotto.PaperResourceInitialization

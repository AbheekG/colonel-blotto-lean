import Blotto.GeneralPaperNativeScaleConstructionStorage

/-! The native classifier's original-index arrays, literal scan frames,
primitive scratch and complete scale/scan/representative-count caller.
Array payloads are retained at fixed capacity; recursive frames borrow
their buffers and own only scalar/control/work fields. -/
namespace Blotto.GeneralPaperLightFieldScanConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperLightFieldScan GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W n r Q : ℕ) : ℕ :=
  n*(5*model.rat (1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude r Q))+128*arrayWord W n)+64*arrayWord W n
def cap (model : RationalCostModel) (W n r Q : ℕ) : ℕ :=
  n+r+Q+GeneralPaperLightFieldScanPrice.magnitude r Q+price model W n r Q+128*arrayWord W n+1

def stateFoot {n : ℕ} (A : ℕ) (s : State n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint A n (fun j : Fin n => natBits j.val) s.heavy+
    GeneralPaperEncodedReferenceVector.reservedFootprint A n (fun j : Fin n => natBits j.val) s.light+
    natBits s.lightWeight+64*A
def stateProfile (A n Q : ℕ) : ℕ := 2*(n*(natBits n+A)+64*A)+natBits Q+64*A

theorem state_bound {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    stateFoot (arrayWord W n) (scan true model W r Q weights count hc).1≤stateProfile (arrayWord W n) n Q := by
  have hSizes := sizes true model W r Q weights count hc
  have hMass := GeneralPaperLightFieldScanPrice.prefix_bound true model W r Q weights hs count hc
  have hh := GeneralPaperEncodedReferenceVector.reserved_bound (arrayWord W n) (natBits n) n
    (fun j : Fin n => natBits j.val) (scan true model W r Q weights count hc).1.heavy (by omega)
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (scan true model W r Q weights count hc).1.heavy[i.val].isLt.le) 1)
  have hl := GeneralPaperEncodedReferenceVector.reserved_bound (arrayWord W n) (natBits n) n
    (fun j : Fin n => natBits j.val) (scan true model W r Q weights count hc).1.light (by omega)
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (scan true model W r Q weights count hc).1.light[i.val].isLt.le) 1)
  have hw := Nat.add_le_add_left (binaryWordWidth_mono hMass) 1
  change natBits (scan true model W r Q weights count hc).1.lightWeight≤natBits Q at hw
  unfold stateFoot stateProfile
  omega

theorem work {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    (scan true model W r Q weights count hc).2≤price model W n r Q :=
  (GeneralPaperLightFieldScanPrice.bit_work model W r Q weights hs count hc).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _)

def frame {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,hc =>
    let A := arrayWord W n
    fields A [n,r,Q,0,64*A,(scan true model W r Q weights 0 hc).2]+128*A
  | count+1,hc =>
    let A := arrayWord W n
    let old := scan true model W r Q weights count (by omega)
    let value := weights.read ⟨count,by omega⟩
    let product := r*value
    let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) r value
    let compare := GeneralPaperIntegerWordPrice.compare model.rat product Q
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) A count
    let overhead := multiply+compare+step+64*A
    let add := if product≤Q then GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) old.1.lightWeight value else 0
    let made := scan true model W r Q weights (count+1) hc
    fields A [n,r,Q,count,count+1,value,product,old.1.lightWeight,made.1.lightWeight,
      old.1.heavy.size,old.1.light.size,made.1.heavy.size,made.1.light.size,old.2,multiply,compare,step,64*A,
      overhead,add,made.2,old.2+overhead]+multiply+compare+add+step+128*A

def frameProfile (model : RationalCostModel) (W n r Q : ℕ) : ℕ :=
  22*(natBits (cap model W n r Q)+arrayWord W n)+
    5*model.rat (1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude r Q))+224*arrayWord W n

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    frame model W r Q weights count hc≤frameProfile model W n r Q := by
  let A := arrayWord W n
  have hw := work model W r Q weights hs count hc
  cases count with
  | zero =>
    have hShape : (scan true model W r Q weights 0 hc).2=64*A := rfl
    have hf := fields_bound A (natBits (cap model W n r Q)) [n,r,Q,0,64*A,(scan true model W r Q weights 0 hc).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields A _≤6*(natBits (cap model W n r Q)+A)+32*A at hf
    change fields A [n,r,Q,0,64*A,(scan true model W r Q weights 0 hc).2]+128*A≤_
    unfold frameProfile
    dsimp only [A] at *
    omega
  | succ count =>
    let old := scan true model W r Q weights count (by omega)
    let value := weights.read ⟨count,by omega⟩
    let product := r*value
    let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) r value
    let compare := GeneralPaperIntegerWordPrice.compare model.rat product Q
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) A count
    let overhead := multiply+compare+step+64*A
    let add := if product≤Q then GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) old.1.lightWeight value else 0
    let made := scan true model W r Q weights (count+1) hc
    let M := GeneralPaperLightFieldScanPrice.magnitude r Q
    have hQ : Q≤M := by unfold M GeneralPaperLightFieldScanPrice.magnitude;nlinarith
    have hr : r≤M := by unfold M GeneralPaperLightFieldScanPrice.magnitude;nlinarith
    have hValue : value≤Q := by
      rw [←hs]
      exact Finset.single_le_sum (f:=fun j : Fin n => weights.read j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (⟨count,by omega⟩:Fin n))
    have hProduct : product≤M := by
      have h := Nat.mul_le_mul_left r hValue
      unfold M GeneralPaperLightFieldScanPrice.magnitude product
      nlinarith only [h]
    have hOld := GeneralPaperLightFieldScanPrice.prefix_bound true model W r Q weights hs count (by omega)
    have hNext := GeneralPaperLightFieldScanPrice.prefix_bound true model W r Q weights hs (count+1) hc
    have hSum := GeneralPaperLightFieldScanPrice.addition_bound true model W r Q weights hs count hc
    have hOldSizes := sizes true model W r Q weights count (by omega)
    have hNextSizes := sizes true model W r Q weights (count+1) hc
    change old.1.lightWeight≤Q at hOld
    change made.1.lightWeight≤Q at hNext
    change old.1.lightWeight+value≤Q at hSum
    change old.1.heavy.size+old.1.light.size=count at hOldSizes
    change made.1.heavy.size+made.1.light.size=count+1 at hNextSizes
    have hMul : multiply≤2*model.rat (1+binaryWordWidth M) :=
      GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) r value M hr (hValue.trans hQ) hProduct
    have hCompare : compare≤model.rat (1+binaryWordWidth M) := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone
      product Q _ (Nat.add_le_add_left (binaryWordWidth_mono hProduct) 1) (Nat.add_le_add_left (binaryWordWidth_mono hQ) 1)
    have hAdd : add≤2*model.rat (1+binaryWordWidth M) := by
      unfold add
      split_ifs
      · exact GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
          old.1.lightWeight value M (hOld.trans hQ) (hValue.trans hQ) (hSum.trans hQ)
      · exact Nat.zero_le _
    have hIndex := GeneralPaperSummaryArrayControls.array_index W n count (by omega)
    have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
    have hStep : step≤64*A := by unfold step PaperIndexedArrayConstruction.stepWork;dsimp only;change binaryWordWidth (count+1)≤A at hIndex;omega
    have hShape : made.2=old.2+overhead+add := by
      change (scan true model W r Q weights (count+1) hc).2=old.2+overhead+add
      rw [scan]
      simp only [GeneralPaperSourceRowsExecution.index,GeneralPaperSourceRowsExecution.address,ite_true]
      split_ifs with hBranch
      · change old.2+overhead+GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) old.1.lightWeight value=old.2+overhead+add
        change product≤Q at hBranch
        unfold add
        rw [ite_eq_left hBranch]
      · change old.2+overhead=old.2+overhead+add
        change ¬product≤Q at hBranch
        unfold add
        rw [ite_eq_right hBranch,Nat.add_zero]
    change made.2≤price model W n r Q at hw
    have hf := fields_bound A (natBits (cap model W n r Q))
      [n,r,Q,count,count+1,value,product,old.1.lightWeight,made.1.lightWeight,
        old.1.heavy.size,old.1.light.size,made.1.heavy.size,made.1.light.size,old.2,multiply,compare,step,64*A,overhead,add,made.2,old.2+overhead] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          dsimp only [A] at * <;> omega)
    change fields A _≤22*(natBits (cap model W n r Q)+A)+32*A at hf
    change fields A [n,r,Q,count,count+1,value,product,old.1.lightWeight,made.1.lightWeight,
      old.1.heavy.size,old.1.light.size,made.1.heavy.size,made.1.light.size,old.2,multiply,compare,step,64*A,overhead,add,made.2,old.2+overhead]+
      multiply+compare+add+step+128*A≤_
    unfold frameProfile
    dsimp only [A,M] at *
    omega

def frames {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,hc => frame model W r Q weights 0 hc
  | count+1,hc => frame model W r Q weights (count+1) hc+frames model W r Q weights count (by omega)

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    frames model W r Q weights count hc≤(count+1)*frameProfile model W n r Q := by
  induction count with
  | zero => simpa only [frames,Nat.zero_add,Nat.one_mul] using frame_bound model W r Q weights hs 0 hc
  | succ count ih => exact (Nat.add_le_add (frame_bound model W r Q weights hs (count+1) hc) (ih (by omega))).trans_eq (by ring)

def window {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  let A := arrayWord W n
  let current := scan true model W r Q weights count hc
  let complete := scan true model W r Q weights n le_rfl
  arrayFootprint A natBits weights+2*stateFoot A current.1+stateFoot A complete.1+
    frames model W r Q weights count hc+fields A [count,current.2,complete.2,complete.1.lightWeight]+128*A

def profile (model : RationalCostModel) (W n r Q : ℕ) : ℕ :=
  arrayProfile (arrayWord W n) n (natBits Q)+3*stateProfile (arrayWord W n) n Q+
    (n+1)*frameProfile model W n r Q+4*(natBits (cap model W n r Q)+arrayWord W n)+160*arrayWord W n

theorem bounded {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) : window model W r Q weights count hc≤profile model W n r Q := by
  have hInput := array_bound (arrayWord W n) (natBits Q) natBits weights (by
    intro j
    have h : weights.read j≤Q := by rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact Nat.add_le_add_left (binaryWordWidth_mono h) 1)
  have hCurrent := state_bound model W r Q weights hs count hc
  have hComplete := state_bound model W r Q weights hs n le_rfl
  have hFrames := (frames_bound model W r Q weights hs count hc).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))
  have hWork := work model W r Q weights hs count hc
  have hCompleteWork := work model W r Q weights hs n le_rfl
  have hMass := GeneralPaperLightFieldScanPrice.prefix_bound true model W r Q weights hs n le_rfl
  have hf := fields_bound (arrayWord W n) (natBits (cap model W n r Q))
    [count,(scan true model W r Q weights count hc).2,(scan true model W r Q weights n le_rfl).2,(scan true model W r Q weights n le_rfl).1.lightWeight] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields _ _≤4*(natBits (cap model W n r Q)+arrayWord W n)+32*arrayWord W n at hf
  unfold window profile
  dsimp only
  omega

@[fun_prop]
theorem scaling (model : RationalCostModel) (n r Q : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile model W n r Q) := by
  unfold profile stateProfile frameProfile cap price arrayProfile arrayWord
  fun_prop

def classificationPrice (model : RationalCostModel) (W n k Q : ℕ) : ℕ :=
  GeneralPaperNativeScaleConstructionStorage.price model W 10 1 k+
    price model W n (GeneralPaperLightFieldScanContract.multiplier k) Q+
    GeneralPaperNativeScaleConstructionStorage.price model W 8 1 k+128*arrayWord W n
def classificationCap (model : RationalCostModel) (W n k Q : ℕ) : ℕ :=
  n+k+Q+GeneralPaperLightFieldScanContract.multiplier k+GeneralPaperLightFieldReduction.representatives k+
    classificationPrice model W n k Q+128*arrayWord W n+1

def classificationControls {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : List ℕ :=
  let threshold := GeneralPaperValueRoundingPaperContract.scaleRun true model W 10 1 k
  let scanned := scan true model W threshold.1 Q weights n le_rfl
  let reps := GeneralPaperValueRoundingPaperContract.scaleRun true model W 8 1 k
  let made := GeneralPaperLightFieldClassification.run true model W k Q weights
  [n,k,Q,threshold.1,reps.1,threshold.2,scanned.2,reps.2,threshold.2+scanned.2,
    threshold.2+scanned.2+reps.2,128*arrayWord W n,made.2]

def classificationWindow {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  let threshold := GeneralPaperValueRoundingPaperContract.scaleRun true model W 10 1 k
  let made := GeneralPaperLightFieldClassification.run true model W k Q weights
  GeneralPaperNativeScaleConstructionStorage.window model W 10 1 k+window model W threshold.1 Q weights count hc+
    GeneralPaperNativeScaleConstructionStorage.window model W 8 1 k+stateFoot (arrayWord W n) made.1.1+
    fields (arrayWord W n) (classificationControls model W k Q weights)+128*arrayWord W n

def classificationProfile (model : RationalCostModel) (W n k Q : ℕ) : ℕ :=
  GeneralPaperNativeScaleConstructionStorage.profile model W 10 1 k+
    profile model W n (GeneralPaperLightFieldScanContract.multiplier k) Q+
    GeneralPaperNativeScaleConstructionStorage.profile model W 8 1 k+stateProfile (arrayWord W n) n Q+
    12*(natBits (classificationCap model W n k Q)+arrayWord W n)+160*arrayWord W n

theorem classification_work {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperLightFieldClassification.run true model W k Q weights).2≤classificationPrice model W n k Q := by
  have ht := GeneralPaperNativeScaleConstructionStorage.work model W 10 1 k
  have hr := GeneralPaperNativeScaleConstructionStorage.work model W 8 1 k
  have hScan := work model W (GeneralPaperLightFieldScanContract.multiplier k) Q weights hs n le_rfl
  unfold GeneralPaperLightFieldClassification.run classificationPrice
  dsimp only
  rw [GeneralPaperValueRoundingPaperContract.scale_data]
  simp only [GeneralPaperValueRoundingPaperContract.scale,Nat.mul_one,GeneralPaperSourceRowsExecution.address,ite_true]
  unfold GeneralPaperLightFieldScanContract.multiplier at *
  omega

theorem classification_bounded {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    classificationWindow model W k Q weights count hc≤classificationProfile model W n k Q := by
  have ht := GeneralPaperNativeScaleConstructionStorage.bounded model W 10 1 k
  have hr := GeneralPaperNativeScaleConstructionStorage.bounded model W 8 1 k
  have hScan := bounded model W (GeneralPaperLightFieldScanContract.multiplier k) Q weights hs count hc
  have hState : stateFoot (arrayWord W n) (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1≤
      stateProfile (arrayWord W n) n Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact state_bound model W _ Q weights hs n le_rfl
  have hw := classification_work model W k Q weights hs
  have hShape : (GeneralPaperLightFieldClassification.run true model W k Q weights).2=
      (GeneralPaperValueRoundingPaperContract.scaleRun true model W 10 1 k).2+
      (scan true model W (GeneralPaperValueRoundingPaperContract.scaleRun true model W 10 1 k).1 Q weights n le_rfl).2+
      (GeneralPaperValueRoundingPaperContract.scaleRun true model W 8 1 k).2+128*arrayWord W n := rfl
  have hThreshold : (GeneralPaperValueRoundingPaperContract.scaleRun true model W 10 1 k).1=GeneralPaperLightFieldScanContract.multiplier k := by
    rw [GeneralPaperValueRoundingPaperContract.scale_data]
    rfl
  have hReps : (GeneralPaperValueRoundingPaperContract.scaleRun true model W 8 1 k).1=GeneralPaperLightFieldReduction.representatives k := by
    rw [GeneralPaperValueRoundingPaperContract.scale_data]
    rfl
  have hf := fields_bound (arrayWord W n) (natBits (classificationCap model W n k Q)) (classificationControls model W k Q weights) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [classificationControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold classificationCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields _ _≤12*(natBits (classificationCap model W n k Q)+arrayWord W n)+32*arrayWord W n at hf
  unfold classificationWindow classificationProfile
  dsimp only
  rw [hThreshold]
  omega

@[fun_prop]
theorem classification_scaling (model : RationalCostModel) (n k Q : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => classificationProfile model W n k Q) := by
  unfold classificationProfile classificationCap classificationPrice price stateProfile
    GeneralPaperNativeScaleConstructionStorage.price GeneralPaperOriginalSourceValuePrice.scalePrice arrayWord
  fun_prop

theorem original_rounded_bounded {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (count : ℕ) (hc : count≤n) :
    let rounded := (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1
    classificationWindow model W k rounded.2 rounded.1 count hc≤classificationProfile model W n k rounded.2 := by
  dsimp only
  exact classification_bounded model W k _ _
    (GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values) count hc

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n r Q : Input → ℕ) (hW : Tight W) (hn : Small n) (hr : Small r) (hQ : Small Q) :
    Linear (fun x => profile model (W x) (n x) (r x) (Q x)) n := by
  have hw := of_tight hW
  have hWP : Polylog W := poly_tight W hW
  have hOperand : Polylog (fun x => 1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude (r x) (Q x))) := by
    unfold GeneralPaperLightFieldScanPrice.magnitude
    fun_prop
  have hOperandSmall := small_of_poly hOperand
  have hRat : Polylog (fun x => model.rat (1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude (r x) (Q x)))) :=
    primitive_preserves hg hOperand hOperandSmall
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hOperandSmall
  unfold profile stateProfile frameProfile cap price arrayProfile arrayWord natBits GeneralPaperLightFieldScanPrice.magnitude
  fun_prop (config := {maxSteps := 20000})

theorem classification_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n Q : Input → ℕ) (hW : Tight W) (hn : Small n) (hQ : Small Q) :
    Linear (fun x => classificationProfile model (W x) (n x) x.k (Q x)) n := by
  have hw := of_tight hW
  have hWP : Polylog W := poly_tight W hW
  have hPowerSmall : Small (fun x => 2^x.k) := pow_two _ k_tight
  have hThresholdSmall : Small (fun x => GeneralPaperLightFieldScanContract.multiplier x.k) := by
    unfold GeneralPaperLightFieldScanContract.multiplier
    fun_prop
  have hScan := profile_rate hg W n (fun x => GeneralPaperLightFieldScanContract.multiplier x.k) Q hW hn hThresholdSmall hQ
  have hThreshold := GeneralPaperNativeScaleConstructionStorage.profile_poly hg W (fun _ => 10) (fun _ => 1) hW (small_constant 10) (small_constant 1)
  have hReps := GeneralPaperNativeScaleConstructionStorage.profile_poly hg W (fun _ => 8) (fun _ => 1) hW (small_constant 8) (small_constant 1)
  have hPriceT := GeneralPaperNativeScaleConstructionStorage.price_poly hg W (fun _ => 10) (fun _ => 1) hW (small_constant 10) (small_constant 1)
  have hPriceR := GeneralPaperNativeScaleConstructionStorage.price_poly hg W (fun _ => 8) (fun _ => 1) hW (small_constant 8) (small_constant 1)
  have hPriceTSmall := small_of_poly hPriceT
  have hPriceRSmall := small_of_poly hPriceR
  have hOperand : Polylog (fun x => 1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude (GeneralPaperLightFieldScanContract.multiplier x.k) (Q x))) := by
    unfold GeneralPaperLightFieldScanPrice.magnitude
    fun_prop
  have hRatSmall := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ (small_of_poly hOperand)
  have hTail : Polylog (fun x => 12*(natBits (classificationCap model (W x) (n x) x.k (Q x))+arrayWord (W x) (n x))+160*arrayWord (W x) (n x)) := by
    unfold classificationCap classificationPrice price arrayWord natBits GeneralPaperLightFieldReduction.representatives
    fun_prop (config := {maxSteps := 20000})
  have hTailLinear : Linear (fun x => 12*(natBits (classificationCap model (W x) (n x) x.k (Q x))+arrayWord (W x) (n x))+160*arrayWord (W x) (n x)) n :=
    linear_poly _ n hTail
  have hTLinear := linear_poly _ n hThreshold
  have hRLinear := linear_poly _ n hReps
  have hState : Linear (fun x => stateProfile (arrayWord (W x) (n x)) (n x) (Q x)) n := by
    unfold stateProfile arrayWord natBits
    fun_prop
  have hAll := linear_add _ _ n
    (linear_add _ _ n (linear_add _ _ n (linear_add _ _ n hTLinear hScan) hRLinear) hState) hTailLinear
  simpa only [classificationProfile,Nat.add_assoc] using hAll

end Blotto.GeneralPaperLightFieldScanConstructionStorage

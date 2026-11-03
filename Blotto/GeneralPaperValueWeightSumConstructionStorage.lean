import Blotto.GeneralPaperOriginalValueRoundConstructionStorage

/-! Actual short-integer summation frames and the complete rational
rounding/summation caller. Long original values are retained once; the
integer loop owns only short accumulators and encoded native work fields. -/
namespace Blotto.GeneralPaperValueWeightSumConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperValueWeightSum GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W n B : ℕ) : ℕ :=
  n*(2*model.rat (1+binaryWordWidth B)+128*arrayWord W n)+64*arrayWord W n
def cap (model : RationalCostModel) (W n B : ℕ) : ℕ := n+B+price model W n B+128*arrayWord W n+1

def frame {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,hc =>
    let A := arrayWord W n
    fields A [n,0,0,64*A,(scan true model W values 0 hc).2]+128*A
  | count+1,hc =>
    let A := arrayWord W n
    let old := scan true model W values count (by omega)
    let value := values.read ⟨count,by omega⟩
    let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) old.1 value
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) A count
    let made := scan true model W values (count+1) hc
    fields A [n,count,count+1,old.1,value,made.1,old.2,add,step,64*A,made.2,old.2+add,old.2+add+step]+
      add+step+128*A

def frameProfile (model : RationalCostModel) (W n B : ℕ) : ℕ :=
  13*(natBits (cap model W n B)+arrayWord W n)+2*model.rat (1+binaryWordWidth B)+224*arrayWord W n

theorem work {n : ℕ} (model : RationalCostModel) (W B : ℕ) (values : FixedArrayTable n ℕ)
    (hB : (scan true model W values n le_rfl).1≤B) (count : ℕ) (hc : count≤n) :
    (scan true model W values count hc).2≤price model W n B :=
  (bit_work model W B values hB count hc).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _)

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W B : ℕ) (values : FixedArrayTable n ℕ)
    (hB : (scan true model W values n le_rfl).1≤B) (count : ℕ) (hc : count≤n) :
    frame model W values count hc≤frameProfile model W n B := by
  let A := arrayWord W n
  have hWork := work model W B values hB count hc
  cases count with
  | zero =>
    have hShape : (scan true model W values 0 hc).2=64*A := rfl
    have hf := fields_bound A (natBits (cap model W n B)) [n,0,0,64*A,(scan true model W values 0 hc).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      change (scan true model W values 0 hc).2≤price model W n B at hWork
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> dsimp only [A] at * <;> omega)
    change fields A _≤5*(natBits (cap model W n B)+A)+32*A at hf
    change fields A [n,0,0,64*A,(scan true model W values 0 hc).2]+128*A≤_
    unfold frameProfile
    change _≤13*(natBits (cap model W n B)+A)+2*model.rat (1+binaryWordWidth B)+224*A
    omega
  | succ count =>
    let old := scan true model W values count (by omega)
    let value := values.read ⟨count,by omega⟩
    let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) old.1 value
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) A count
    let made := scan true model W values (count+1) hc
    have hOld : old.1≤B := (prefix_mono true model W values count n (by omega) le_rfl).trans hB
    have hValue : value≤B := (item_le_total true model W values ⟨count,by omega⟩).trans hB
    have hTotal : made.1≤B := (prefix_mono true model W values (count+1) n hc le_rfl).trans hB
    have hSum : old.1+value≤B := hTotal
    have hAdd : add≤2*model.rat (1+binaryWordWidth B) :=
      GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) old.1 value B hOld hValue hSum
    have hIndex := GeneralPaperSummaryArrayControls.array_index W n count (by omega)
    have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
    have hStep : step≤64*A := by unfold step PaperIndexedArrayConstruction.stepWork;dsimp only;change binaryWordWidth (count+1)≤A at hIndex;omega
    have hShape : made.2=old.2+add+step+64*A := rfl
    change made.2≤price model W n B at hWork
    have hf := fields_bound A (natBits (cap model W n B))
      [n,count,count+1,old.1,value,made.1,old.2,add,step,64*A,made.2,old.2+add,old.2+add+step] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [A] at * <;> omega)
    change fields A _≤13*(natBits (cap model W n B)+A)+32*A at hf
    change fields A [n,count,count+1,old.1,value,made.1,old.2,add,step,64*A,made.2,old.2+add,old.2+add+step]+add+step+128*A≤_
    unfold frameProfile
    change _≤13*(natBits (cap model W n B)+A)+2*model.rat (1+binaryWordWidth B)+224*A
    omega

def frames {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) : (count : ℕ) → count≤n → ℕ
  | 0,hc => frame model W values 0 hc
  | count+1,hc => frame model W values (count+1) hc+frames model W values count (by omega)

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W B : ℕ) (values : FixedArrayTable n ℕ)
    (hB : (scan true model W values n le_rfl).1≤B) (count : ℕ) (hc : count≤n) :
    frames model W values count hc≤(count+1)*frameProfile model W n B := by
  induction count with
  | zero => simpa only [frames,Nat.zero_add,Nat.one_mul] using frame_bound model W B values hB 0 hc
  | succ count ih =>
    exact (Nat.add_le_add (frame_bound model W B values hB (count+1) hc) (ih (by omega))).trans_eq (by ring)

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  let A := arrayWord W n
  let made := scan true model W values count hc
  let complete := scan true model W values n le_rfl
  arrayFootprint A natBits values+frames model W values count hc+
    fields A [n,count,made.1,made.2,complete.1,complete.2]+128*A

def profile (model : RationalCostModel) (W n B : ℕ) : ℕ :=
  arrayProfile (arrayWord W n) n (natBits B)+(n+1)*frameProfile model W n B+
    6*(natBits (cap model W n B)+arrayWord W n)+160*arrayWord W n

theorem bounded {n : ℕ} (model : RationalCostModel) (W B : ℕ) (values : FixedArrayTable n ℕ)
    (hB : (scan true model W values n le_rfl).1≤B) (count : ℕ) (hc : count≤n) :
    window model W values count hc≤profile model W n B := by
  let A := arrayWord W n
  have hItems := array_bound A (natBits B) natBits values
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono ((item_le_total true model W values j).trans hB)) 1)
  have hFrames := (frames_bound model W B values hB count hc).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))
  have hTotal := (prefix_mono true model W values count n hc le_rfl).trans hB
  have hWork := work model W B values hB count hc
  have hCompleteWork := work model W B values hB n le_rfl
  have hf := fields_bound A (natBits (cap model W n B))
    [n,count,(scan true model W values count hc).1,(scan true model W values count hc).2,
      (scan true model W values n le_rfl).1,(scan true model W values n le_rfl).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤6*(natBits (cap model W n B)+A)+32*A at hf
  unfold window profile
  change arrayFootprint A natBits values+frames model W values count hc+
    fields A [n,count,(scan true model W values count hc).1,(scan true model W values count hc).2,
      (scan true model W values n le_rfl).1,(scan true model W values n le_rfl).2]+128*A≤_
  dsimp only [A] at *
  omega

def driverPrice (model : RationalCostModel) (W n M S : ℕ) : ℕ :=
  let A := arrayWord W n
  GeneralPaperNativePayloadFillStorage.workCap A n (GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice model A
    (GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth M S))+price model W n (M+n)+128*A

def driverWindow {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  let rounded := GeneralPaperValueRoundArray.run true model W M values
  let total := scan true model W rounded.1 n le_rfl
  let made := GeneralPaperValueRoundingDriver.run true model W M values
  let A := arrayWord W n
  GeneralPaperOriginalValueRoundConstructionStorage.window model W M values count hc+
    window model W rounded.1 count hc+fields A [rounded.2,total.2,128*A,rounded.2+total.2,made.2]+128*A

def driverProfile (model : RationalCostModel) (W n M S : ℕ) : ℕ :=
  let A := arrayWord W n
  GeneralPaperOriginalValueRoundConstructionStorage.profile model W n M S+profile model W n (M+n)+
    5*(natBits (driverPrice model W n M S+128*A+1)+A)+160*A

theorem driver_total_bound {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (scan true model W (GeneralPaperValueRoundArray.run true model W M values).1 n le_rfl).1≤M+n :=
  (GeneralPaperValueRoundingDriver.total_bounds true model W M values v hv).2.le

theorem driver_work {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperValueRoundingDriver.run true model W M values).2≤driverPrice model W n M (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have hRound := GeneralPaperOriginalValueRoundConstructionStorage.work model W M values
  have hSum := work model W (M+n) (GeneralPaperValueRoundArray.run true model W M values).1
    (driver_total_bound model W M values v hv) n le_rfl
  unfold GeneralPaperValueRoundingDriver.run driverPrice
  dsimp only [GeneralPaperSourceRowsExecution.address]
  simp only [ite_true]
  omega

theorem driver_bounded {n : ℕ} (model : RationalCostModel) (W M : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (count : ℕ) (hc : count≤n) :
    driverWindow model W M values count hc≤driverProfile model W n M (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  let A := arrayWord W n
  have hRound := GeneralPaperOriginalValueRoundConstructionStorage.native_bounded model W M values v hv count hc
  have hSum := bounded model W (M+n) (GeneralPaperValueRoundArray.run true model W M values).1
    (driver_total_bound model W M values v hv) count hc
  have hw := driver_work model W M values v hv
  have hShape : (GeneralPaperValueRoundingDriver.run true model W M values).2=
      (GeneralPaperValueRoundArray.run true model W M values).2+
      (scan true model W (GeneralPaperValueRoundArray.run true model W M values).1 n le_rfl).2+128*A := rfl
  have hf := fields_bound A (natBits (driverPrice model W n M (GeneralPaperValueRoundingInputPrice.inputSize values)+128*A+1))
    [(GeneralPaperValueRoundArray.run true model W M values).2,
      (scan true model W (GeneralPaperValueRoundArray.run true model W M values).1 n le_rfl).2,128*A,
      (GeneralPaperValueRoundArray.run true model W M values).2+
      (scan true model W (GeneralPaperValueRoundArray.run true model W M values).1 n le_rfl).2,
      (GeneralPaperValueRoundingDriver.run true model W M values).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields A _≤5*(natBits (driverPrice model W n M (GeneralPaperValueRoundingInputPrice.inputSize values)+128*A+1)+A)+32*A at hf
  unfold driverWindow driverProfile
  dsimp only
  change _≤GeneralPaperOriginalValueRoundConstructionStorage.profile model W n M (GeneralPaperValueRoundingInputPrice.inputSize values)+
    profile model W n (M+n)+5*(natBits (driverPrice model W n M (GeneralPaperValueRoundingInputPrice.inputSize values)+128*A+1)+A)+160*A
  dsimp only [A] at *
  omega

@[fun_prop]
theorem profile_scaling (model : RationalCostModel) (n B : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W n B) := by
  unfold profile frameProfile cap price arrayProfile arrayWord
  fun_prop

@[fun_prop]
theorem driver_profile_scaling (model : RationalCostModel) (n M S : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => driverProfile model W n M S) := by
  unfold driverProfile driverPrice price
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
    GeneralPaperNativePayloadFillStorage.workCap arrayWord
  dsimp only
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem primitive_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (f : Input → ℕ) (hf : Small f) : Small (fun x => model.rat (f x)) :=
  GeneralPaperSourceWordGrowth.dominated (GeneralPaperConstructedWordGrowth.fast_charge C d f hf) (fun x => hg (f x))

theorem fill_short_frames (n W P C : Input → ℕ) (hn : Small n) (hW : Tight W) (hp : Polylog P) (hc : Small C) :
    Linear (fun x => GeneralPaperNativePayloadFillStorage.profile (W x) (P x) (n x) (C x) 0) n := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap natBits
  fun_prop (config := {maxSteps := 20000})

theorem fill_long_child (n S W P C Q : Input → ℕ) (hn : Small n) (hW : Tight W) (hp : Polylog P) (hc : Small C)
    (hq : Linear Q S) :
    Soft (fun x => S x+n x+1) (fun x => GeneralPaperNativePayloadFillStorage.profile (W x) (P x) (n x) (C x) (Q x)) := by
  have hBase := rate_mono (fill_short_frames n W P C hn hW hp hc) (fun x => by omega : ∀ x,n x+1≤S x+n x+1)
  have hChild := rate_mono hq (fun x => by omega : ∀ x,S x+1≤S x+n x+1)
  apply GeneralPaperSourceSoftBounds.dominated (add_same hBase hChild)
  intro x
  unfold GeneralPaperNativePayloadFillStorage.profile
  omega

theorem round_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n M S : Input → ℕ) (hW : Tight W) (hn : Small n) (hM : Small M) (hS : Small S) :
    Soft (fun x => S x+n x+1) (fun x => GeneralPaperOriginalValueRoundConstructionStorage.profile model (W x) (n x) (M x) (S x)) := by
  let A := fun x => arrayWord (W x) (n x)
  let H := fun x => GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth (M x) (S x)
  have hATight : Tight A := by unfold A arrayWord;fun_prop
  have hAPoly : Polylog A := poly_tight A hATight
  have hASmall := of_tight hATight
  have hHSmall : Small H := by unfold H GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth;fun_prop
  have hHLinear : Linear H S := by unfold H GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth;fun_prop
  have hRat : Linear (fun x => model.rat (H x)) S := primitive_preserves hg hHLinear hHSmall
  have hRatSmall := primitive_small hg H hHSmall
  have hCallbackSmall : Small (fun x => GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice model (A x) (H x)) := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
    fun_prop
  have hPayload : Polylog (fun x => natBits (M x)) := by unfold natBits;fun_prop
  have hChild : Linear (fun x => GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile model (A x) (n x) (M x) (H x)) S := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile
      GeneralPaperOriginalValueRoundConstructionStorage.scalarProfile GeneralPaperPositiveCeilingConstructionStorage.profile
      GeneralPaperPositiveCeilingConstructionStorage.price GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice
      GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice natBits
    fun_prop (config := {maxSteps := 20000})
  have hFill := fill_long_child n S A (fun x => natBits (M x))
    (fun x => GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice model (A x) (H x))
    (fun x => GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile model (A x) (n x) (M x) (H x))
    hn hATight hPayload hCallbackSmall hChild
  have hTail : Polylog (fun x => 64*A x+4*(natBits (GeneralPaperOriginalValueRoundConstructionStorage.cap model (A x) (n x) (M x) (H x))+A x)+160*A x) := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.cap GeneralPaperNativePayloadFillStorage.workCap natBits
    fun_prop
  have hInput : Soft (fun x => S x+n x+1) S := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by omega)
  have hN : Soft (fun x => S x+n x+1) n := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by omega)
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤S x+n x+1)
  apply GeneralPaperSourceSoftBounds.dominated (add_same (add_same (add_same hInput (mul_poly hN hAPoly)) hFill) hTail')
  intro x
  unfold GeneralPaperOriginalValueRoundConstructionStorage.profile
  dsimp only [A,H]
  omega

theorem sum_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n B : Input → ℕ) (hW : Tight W) (hn : Small n) (hB : Small B) :
    Linear (fun x => profile model (W x) (n x) (B x)) n := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hOperand : Polylog (fun x => 1+binaryWordWidth (B x)) := by fun_prop
  have hOperandSmall := small_of_poly hOperand
  have hRatPoly : Polylog (fun x => model.rat (1+binaryWordWidth (B x))) := primitive_preserves hg hOperand hOperandSmall
  have hRat : Linear (fun x => model.rat (1+binaryWordWidth (B x))) n := linear_poly _ n hRatPoly
  have hRatSmall := primitive_small hg _ hOperandSmall
  unfold profile frameProfile cap price arrayProfile arrayWord natBits
  fun_prop (config := {maxSteps := 20000})

theorem driver_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n M S : Input → ℕ) (hW : Tight W) (hn : Small n) (hM : Small M) (hS : Small S) :
    Soft (fun x => S x+n x+1) (fun x => driverProfile model (W x) (n x) (M x) (S x)) := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hRound := round_profile_rate hg W n M S hW hn hM hS
  have hSum := rate_mono (sum_profile_rate hg W n (fun x => M x+n x) hW hn (by fun_prop))
    (fun x => by omega : ∀ x,n x+1≤S x+n x+1)
  have hLong : Small (fun x => GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth (M x) (S x)) := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
    fun_prop
  have hLongPrice := primitive_small hg _ hLong
  have hShort : Small (fun x => 1+binaryWordWidth (M x+n x)) := by fun_prop
  have hShortPrice := primitive_small hg _ hShort
  have hTail : Polylog (fun x =>
      5*(natBits (driverPrice model (W x) (n x) (M x) (S x)+128*arrayWord (W x) (n x)+1)+arrayWord (W x) (n x))+
        160*arrayWord (W x) (n x)) := by
    unfold driverPrice price GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice
      GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice GeneralPaperNativePayloadFillStorage.workCap arrayWord natBits
    dsimp only
    fun_prop (config := {maxSteps := 20000})
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤S x+n x+1)
  simpa only [driverProfile,Nat.add_assoc] using add_same (add_same hRound hSum) hTail'

end Blotto.GeneralPaperValueWeightSumConstructionStorage

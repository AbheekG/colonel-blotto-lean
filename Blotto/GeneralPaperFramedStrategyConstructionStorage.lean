import Blotto.GeneralPaperAccuracyStrategyConstructionStorage

/-! Actual framed strategy caller, with complete successful and rejected
branches. The parsed words/suffix coexist with once-only preparation, and
the full returned strategy/suffix and every parent work field are covered. -/
namespace Blotto.GeneralPaperFramedStrategyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
open GeneralPaperAccuracyStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem read_suffix_length (W : ℕ) (frame : List Bool) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some parsed) : parsed.2.length≤frame.length := by
  simp only [GeneralPaperBinaryAccuracy.read] at hRead
  cases hn:(BinaryPositiveWordReadWork.read frame).1 with
  | none => simp only [hn] at hRead;cases hRead
  | some numerator =>
    simp only [hn] at hRead
    cases hd:(BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => simp only [hd] at hRead;cases hRead
    | some denominator =>
      simp only [hd] at hRead
      have hs : denominator.2=parsed.2 := congrArg Prod.snd (Option.some.inj hRead)
      rw [←hs]
      exact (BinaryPositiveWordReadWork.read_suffix_length numerator.2 denominator hd).trans
        (BinaryPositiveWordReadWork.read_suffix_length frame numerator hn)

def returnedFoot {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : ℕ :=
  match (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1 with
  | none => 0
  | some prepared => GeneralPaperClosedDescriptionStorage.rawFoot W prepared.1+
      listFootprint W (fun _ : Bool => 1) prepared.2+64*W

noncomputable def price {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperFramedAccuracyConstructionStorage.price W E+exponentPrice model C d W k S Qv B H red+64*W

noncomputable def cap {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ := n+k+E+W+price model C d W E k S Qv B H red+64*W+1

def controls {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool)
    (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  let core := GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.1.exponent values v hv b hb
  let read := GeneralPaperBinaryAccuracy.read (fun w => w) W frame
  [n,W,parsed.1.exponent,read.2,core.2,read.2+core.2,64*W,
    (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2]

noncomputable def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool)
    (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced.m
      parsed.1.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced
      (rows parsed.1.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced)) : ℕ :=
  GeneralPaperFramedAccuracyConstructionStorage.window W frame+
    exponentWindow model W parsed.1.exponent values v hv b hb cS cD+
    GeneralPaperFramedAccuracyConstructionStorage.returnedFoot W frame+returnedFoot model W frame values v hv b hb+
    fields W (controls model W frame parsed values v hv b hb)+128*W

noncomputable def profile {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  3*GeneralPaperFramedAccuracyConstructionStorage.profile W E+2*exponentProfile model C d W k S Qv B H red+
    8*(natBits (cap model C d W E k S Qv B H red)+W)+224*W

theorem returned_covered {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool)
    (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced.m
      parsed.1.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced
      (rows parsed.1.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1.reduced)) :
    returnedFoot model W frame values v hv b hb≤window model W frame parsed values v hv b hb cS cD := by unfold window;omega

theorem bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W E B : ℕ) (frame : List Bool) (hc : frame.length≤E) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p parsed.1.exponent B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m parsed.1.exponent p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows parsed.1.exponent p.reduced)),
      window model W frame parsed values v hv b hb cS cD≤profile model C d W E parsed.1.exponent
        (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
        (GeneralPaperSourcePairAnchorHeights.width p.reduced.m parsed.1.exponent) p.reduced ∧
      (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤
        price model C d W E parsed.1.exponent (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
          (GeneralPaperSourcePairAnchorHeights.width p.reduced.m parsed.1.exponent) p.reduced := by
  dsimp only
  intro hReference cS cD
  let k := parsed.1.exponent
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width p.reduced.m k
  have hCore := exponent_bounded hg W k B values v hv b hb hB hOriginalIndex hReference cS cD
  change exponentWindow model W k values v hv b hb cS cD≤exponentProfile model C d W k S p.Qv B H p.reduced ∧
    (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2≤
      exponentPrice model C d W k S p.Qv B H p.reduced at hCore
  have hRaw := (exponent_return_covered model W k values v hv b hb cS cD).trans hCore.1
  have hAccuracy := GeneralPaperFramedAccuracyConstructionStorage.bounded W E frame hc
  have hAccuracyWork := GeneralPaperFramedAccuracyConstructionStorage.work W E frame hc
  have hReadReturn := GeneralPaperFramedAccuracyConstructionStorage.returned_bounded W E frame hc
  have hSuffix : listFootprint W (fun _ : Bool => 1) parsed.2≤GeneralPaperFramedAccuracyConstructionStorage.returnedFoot W frame := by
    unfold GeneralPaperFramedAccuracyConstructionStorage.returnedFoot
    rw [hRead]
    dsimp only
    omega
  have hFrame := GeneralPaperAccuracyStrategyDriver.frame_some model W W W frame values v hv b hb parsed hRead
  have hReturned : returnedFoot model W frame values v hv b hb≤
      exponentProfile model C d W k S p.Qv B H p.reduced+GeneralPaperFramedAccuracyConstructionStorage.profile W E+64*W := by
    unfold returnedFoot
    rw [hFrame.1]
    change GeneralPaperClosedDescriptionStorage.rawFoot W
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1+
      listFootprint W (fun _ : Bool => 1) parsed.2+64*W≤_
    omega
  have hShape : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2=
      (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2+
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2+64*W := by
    simp only [GeneralPaperAccuracyStrategyDriver.frame,hRead]
    rfl
  have hWork : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤
      price model C d W E k S p.Qv B H p.reduced := by unfold price;omega
  have hf := fields_bound W (natBits (cap model C d W E k S p.Qv B H p.reduced)) (controls model W frame parsed values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[n,W,k,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2,
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2,
      (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2+
        (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2,64*W,
      (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤8*(natBits (cap model C d W E k S p.Qv B H p.reduced)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  change window model W frame parsed values v hv b hb cS cD≤profile model C d W E k S p.Qv B H p.reduced
  unfold window profile
  change GeneralPaperFramedAccuracyConstructionStorage.window W frame+exponentWindow model W k values v hv b hb cS cD+
    GeneralPaperFramedAccuracyConstructionStorage.returnedFoot W frame+returnedFoot model W frame values v hv b hb+
    fields W (controls model W frame parsed values v hv b hb)+128*W≤
    3*GeneralPaperFramedAccuracyConstructionStorage.profile W E+2*exponentProfile model C d W k S p.Qv B H p.reduced+
      8*(natBits (cap model C d W E k S p.Qv B H p.reduced)+W)+224*W
  omega

def rejectedPrice (W E : ℕ) : ℕ := GeneralPaperFramedAccuracyConstructionStorage.price W E+64*W

def rejectedCap (W E n : ℕ) : ℕ := n+E+W+rejectedPrice W E+64*W+1

def rejectedControls {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  [n,W,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2,64*W,
    (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2]

def rejectedWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : ℕ :=
  GeneralPaperFramedAccuracyConstructionStorage.window W frame+arrayFootprint W rationalWordWidth values+rationalWordWidth b+
    fields W (rejectedControls model W frame values v hv b hb)+128*W

def rejectedProfile (W E n S B : ℕ) : ℕ :=
  GeneralPaperFramedAccuracyConstructionStorage.profile W E+(S+n*W+64*W)+(1+2*B)+
    5*(natBits (rejectedCap W E n)+W)+160*W

theorem rejected_bounded {n : ℕ} (model : RationalCostModel) (W E B : ℕ) (frame : List Bool) (hc : frame.length≤E)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=none) :
    rejectedWindow model W frame values v hv b hb≤rejectedProfile W E n (GeneralPaperValueRoundingInputPrice.inputSize values) B ∧
      (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤rejectedPrice W E ∧
      returnedFoot model W frame values v hv b hb=0 := by
  have hAccuracy := GeneralPaperFramedAccuracyConstructionStorage.bounded W E frame hc
  have hAccuracyWork := GeneralPaperFramedAccuracyConstructionStorage.work W E frame hc
  have hShape : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2=
      (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2+64*W := by simp only [GeneralPaperAccuracyStrategyDriver.frame,hRead]
  have hWork : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤rejectedPrice W E := by unfold rejectedPrice;omega
  have hInput : arrayFootprint W rationalWordWidth values=GeneralPaperValueRoundingInputPrice.inputSize values+n*W+64*W := by
    unfold arrayFootprint GeneralPaperValueRoundingInputPrice.inputSize
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  have hBudget := rationalWordWidth_of_height hB
  have hf := fields_bound W (natBits (rejectedCap W E n)) (rejectedControls model W frame values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [rejectedControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold rejectedCap
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (rejectedCap W E n)+W)+32*W at hf
  refine ⟨?_,hWork,?_⟩
  · unfold rejectedWindow rejectedProfile
    omega
  · simp only [returnedFoot,GeneralPaperAccuracyStrategyDriver.frame,hRead]

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model C d W E k S Qv B H red) := by
  unfold price GeneralPaperFramedAccuracyConstructionStorage.price GeneralPaperBinaryAccuracyConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.step
  fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model C d W E k S Qv B H red) := by unfold profile cap;fun_prop

@[fun_prop]
theorem rejected_price_scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => rejectedPrice W E) := by
  unfold rejectedPrice GeneralPaperFramedAccuracyConstructionStorage.price GeneralPaperBinaryAccuracyConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.step
  fun_prop

@[fun_prop]
theorem rejected_scaling (E n S B : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => rejectedProfile W E n S B) := by
  unfold rejectedProfile rejectedCap
  fun_prop

end Blotto.GeneralPaperFramedStrategyConstructionStorage

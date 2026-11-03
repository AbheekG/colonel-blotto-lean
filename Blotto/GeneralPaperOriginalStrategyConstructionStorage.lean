import Blotto.GeneralPaperOriginalSourceDriverConstructionStorage

/-! Full native original-input strategy preparation. Source output stays
retained while its actual description is attached; the full original input,
returned strategy, every parent work field and both phase windows coexist.
All cursors are erased observers of existing once-only calls. -/
namespace Blotto.GeneralPaperOriginalStrategyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperProxyParameters
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperStrategyDescriptionConstructionStorage
open GeneralPaperStrategyDescription GeneralPaperClosedDescriptionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def rows {n : ℕ} (k : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  (GeneralPaperTrajectoryParameters.prepare (alphabet red.m k).lambda k).rows

def preparedFoot {n k : ℕ} (W : ℕ) (prepared : GeneralPaperOriginalStrategyDriver.Prepared n k) : ℕ :=
  originalFoot W prepared.original+
    (match prepared.description with | none => 0 | some description => descriptionFoot W prepared.original.reduced description)+64*W

def preparedProfile {n : ℕ} (W k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  originalProfile W Qv red+descriptionProfile W (rows k red) (prepare red.m k).K H red+64*W

def attachChildWork {n k : ℕ} (model : RationalCostModel) (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives) : ℕ :=
  match source.physical with
  | none => 0
  | some columns => (make model.rat (fun w => w) W source.original.reduced hRep hNo hR columns).2

def attachChildWindow {n k : ℕ} (model : RationalCostModel) (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives)
    (c : GeneralPaperStrategyDescriptionConstructionStorage.Cursor source.original.reduced (rows k source.original.reduced)) : ℕ :=
  match source.physical with
  | none => 0
  | some columns => GeneralPaperStrategyDescriptionConstructionStorage.window model W source.original.reduced hRep hNo hR columns c

def attachPrice {n : ℕ} (model : RationalCostModel) (W k H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperStrategyDescriptionConstructionStorage.price model W (rows k red) H red+64*W

def attachCap {n : ℕ} (model : RationalCostModel) (W k H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  W+attachPrice model W k H red+64*W+1

def attachControls {n k : ℕ} (model : RationalCostModel) (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives) : List ℕ :=
  [W,attachChildWork model W source hRep hNo hR,64*W,
    (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).2]

def attachWindow {n k : ℕ} (model : RationalCostModel) (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives)
    (c : GeneralPaperStrategyDescriptionConstructionStorage.Cursor source.original.reduced (rows k source.original.reduced)) : ℕ :=
  sourceFoot W source+attachChildWindow model W source hRep hNo hR c+
    preparedFoot W (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).1+
    fields W (attachControls model W source hRep hNo hR)+128*W

def attachProfile {n : ℕ} (model : RationalCostModel) (W k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  returnProfile W k Qv H red+GeneralPaperStrategyDescriptionConstructionStorage.profile model W (rows k red) (prepare red.m k).K H red+
    preparedProfile W k Qv H red+4*(natBits (attachCap model W k H red)+W)+160*W

theorem attach_work_shape {n k : ℕ} (model : RationalCostModel) (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives) :
    (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).2=
      attachChildWork model W source hRep hNo hR+64*W := by
  unfold GeneralPaperOriginalStrategyDriver.attach attachChildWork
  cases source.physical with
  | none => simp only [Nat.zero_add]
  | some columns => rfl

theorem attach_bounded {n k : ℕ} (model : RationalCostModel) (W H : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape source.original.reduced)
    (hNo : GeneralPaperUnreplacedShape.Shape source.original.reduced) (hR : 0<source.original.reduced.representatives)
    (hs : GeneralPaperCircleActualWeights.Conserved source.original.reduced)
    (hHeights : ∀ columns,source.physical=some columns →
      (∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H) ∧
      (∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H))
    (hW : 1≤W) (hFields : binaryWordWidth (source.original.reduced.m+1)≤W)
    (hLight : binaryWordWidth (source.original.reduced.classified.light.size+1)≤W)
    (hRows : binaryWordWidth (rows k source.original.reduced+1)≤W)
    (c : GeneralPaperStrategyDescriptionConstructionStorage.Cursor source.original.reduced (rows k source.original.reduced)) :
    attachWindow model W source hRep hNo hR c≤attachProfile model W k source.original.Qv H source.original.reduced ∧
      (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).2≤attachPrice model W k H source.original.reduced := by
  let red := source.original.reduced
  have hOriginal := original_bound W source.original
  have hAll : attachChildWindow model W source hRep hNo hR c≤
        GeneralPaperStrategyDescriptionConstructionStorage.profile model W (rows k red) (prepare red.m k).K H red ∧
      attachChildWork model W source hRep hNo hR≤GeneralPaperStrategyDescriptionConstructionStorage.price model W (rows k red) H red ∧
      sourceFoot W source≤returnProfile W k source.original.Qv H red ∧
      preparedFoot W (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).1≤
        preparedProfile W k source.original.Qv H red := by
    cases he:source.physical with
    | none =>
      refine ⟨?_,?_,?_,?_⟩
      · unfold attachChildWindow;rw [he];exact Nat.zero_le _
      · unfold attachChildWork;rw [he];exact Nat.zero_le _
      · unfold sourceFoot returnProfile
        rw [he]
        change originalFoot W source.original+0+64*W≤originalProfile W source.original.Qv red+
          physicalProfile W (rows k red) red.m (prepare red.m k).K H+64*W
        change originalFoot W source.original≤originalProfile W source.original.Qv red at hOriginal
        omega
      · unfold preparedFoot GeneralPaperOriginalStrategyDriver.attach preparedProfile
        rw [he]
        dsimp only
        change originalFoot W source.original≤originalProfile W source.original.Qv red at hOriginal
        omega
    | some columns =>
      obtain ⟨hRich,hPoor⟩ := hHeights columns he
      have hChild := GeneralPaperStrategyDescriptionConstructionStorage.bounded model W H red hRep hNo hR columns
        hs hRich hPoor hW hFields hLight hRows c
      have hDescription := make_bound model.rat (fun w => w) W W H red hRep hNo hR columns hs hRich hPoor
      have hPhysical := physical_bound W H columns hRich hPoor
      have hAttach := GeneralPaperOriginalStrategyDriver.attach_some model.rat (fun w => w) W source hRep hNo hR columns he
      refine ⟨?_,?_,?_,?_⟩
      · unfold attachChildWindow;rw [he];exact hChild.1
      · unfold attachChildWork;rw [he];exact hChild.2
      · unfold sourceFoot returnProfile
        rw [he]
        change originalFoot W source.original+physicalFoot W columns+64*W≤originalProfile W source.original.Qv red+
          physicalProfile W (rows k red) red.m (prepare red.m k).K H+64*W
        change originalFoot W source.original≤originalProfile W source.original.Qv red at hOriginal
        change physicalFoot W columns≤physicalProfile W (rows k red) red.m (prepare red.m k).K H at hPhysical
        omega
      · unfold preparedFoot preparedProfile
        rw [hAttach.1]
        change originalFoot W source.original+descriptionFoot W red (make model.rat (fun w => w) W red hRep hNo hR columns).1+64*W≤
          originalProfile W source.original.Qv red+descriptionProfile W (rows k red) (prepare red.m k).K H red+64*W
        change originalFoot W source.original≤originalProfile W source.original.Qv red at hOriginal
        change descriptionFoot W red _≤descriptionProfile W (rows k red) (prepare red.m k).K H red at hDescription
        omega
  have hShape := attach_work_shape model W source hRep hNo hR
  have hWork : (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source hRep hNo hR).2≤attachPrice model W k H red := by
    unfold attachPrice
    omega
  have hf := fields_bound W (natBits (attachCap model W k H red)) (attachControls model W source hRep hNo hR) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [attachControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold attachCap
    rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (attachCap model W k H red)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  unfold attachWindow attachProfile
  dsimp only [red] at *
  omega

noncomputable def price {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalSourceDriverConstructionStorage.price model C d W k S Qv B red+attachPrice model W k H red+128*W

noncomputable def cap {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+k+W+price model C d W k S Qv B H red+128*W+1

def controls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  let source := GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb
  let stored := GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source.1
    (GeneralPaperNativeReductionShape.original_shape true model W k values)
    (GeneralPaperUnreplacedShape.original_shape true model W k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model W k values)
  [n,k,W,source.2,stored.2,source.2+stored.2,128*W,(GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2]

noncomputable def window {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced
      (rows k (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced)) : ℕ :=
  let source := GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb
  let hRep := GeneralPaperNativeReductionShape.original_shape true model W k values
  let hNo := GeneralPaperUnreplacedShape.original_shape true model W k values
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model W k values
  GeneralPaperOriginalSourceDriverConstructionStorage.window model W k values v hv b hb cS+
    attachWindow model W source.1 hRep hNo hR cD+sourceFoot W source.1+
    preparedFoot W (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1+
    fields W (controls model W k values v hv b hb)+256*W

noncomputable def profile {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d W k S Qv B H red+2*attachProfile model W k Qv H red+
    8*(natBits (cap model C d W k S Qv B H red)+W)+288*W

theorem bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m k p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
      window model W k values v hv b hb cS cD≤profile model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
        (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced ∧
      (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2≤
        price model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
          (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced := by
  dsimp only
  intro hReference cS cD
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
  let source := GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb
  let red := p.reduced
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width red.m k
  let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
  let hRep := GeneralPaperNativeReductionShape.original_shape true model W k values
  let hNo := GeneralPaperUnreplacedShape.original_shape true model W k values
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model W k values
  let stored := GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W source.1 hRep hNo hR
  change GeneralPaperFastDriverReference.width C d x≤W at hReference
  have hSource := GeneralPaperOriginalSourceDriverConstructionStorage.bounded hg W k B values v hv b hb hB hReference cS
  change GeneralPaperOriginalSourceDriverConstructionStorage.window model W k values v hv b hb cS≤
      GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d W k S p.Qv B H red ∧
      source.2≤GeneralPaperOriginalSourceDriverConstructionStorage.price model C d W k S p.Qv B red at hSource
  have hs := GeneralPaperCircleActualWeights.original_sum true model W k values
  have hW := (GeneralPaperFastDriverReference.positive_width C d x).trans hReference
  have hFields := (GeneralPaperFastDriverReference.local_words C d x).2.2.1.trans hReference
  change binaryWordWidth (red.m+1)≤W at hFields
  have hRows := (GeneralPaperFastDriverReference.row_words C d x).1.trans hReference
  change binaryWordWidth (rows k red+1)≤W at hRows
  have hLight : binaryWordWidth (red.classified.light.size+1)≤W := by
    have h := GeneralPaperStrategyPreparationWork.light_size true model W k values
    change red.classified.light.size≤n at h
    exact (binaryWordWidth_mono (Nat.add_le_add_right h 1)).trans hOriginalIndex
  obtain ⟨physical,hPhysical,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model W W k values v hv b hb
  have hHeights : ∀ columns,source.1.physical=some columns →
      (∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H) ∧
      (∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H) := by
    intro columns hColumns
    have he : columns=physical := Option.some.inj (hColumns.symm.trans hPhysical)
    subst columns
    exact ⟨hRich,hPoor⟩
  have hAttach := attach_bounded model W H source.1 hRep hNo hR hs hHeights hW hFields hLight hRows cD
  change attachWindow model W source.1 hRep hNo hR cD≤attachProfile model W k p.Qv H red ∧
      stored.2≤attachPrice model W k H red at hAttach
  have hOwners : sourceFoot W source.1+preparedFoot W (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1≤
      attachWindow model W source.1 hRep hNo hR cD := by
    unfold attachWindow
    change sourceFoot W source.1+preparedFoot W stored.1≤
      sourceFoot W source.1+attachChildWindow model W source.1 hRep hNo hR cD+preparedFoot W stored.1+
        fields W (attachControls model W source.1 hRep hNo hR)+128*W
    omega
  have hOwners' := hOwners.trans hAttach.1
  have hShape : (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2=source.2+stored.2+128*W := rfl
  have hWork : (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2≤price model C d W k S p.Qv B H red := by
    unfold price
    omega
  have hf := fields_bound W (natBits (cap model C d W k S p.Qv B H red)) (controls model W k values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [source,stored,hRep,hNo,hR] at * <;> omega)
  change fields W _≤8*(natBits (cap model C d W k S p.Qv B H red)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  change GeneralPaperOriginalSourceDriverConstructionStorage.window model W k values v hv b hb cS+
    attachWindow model W source.1 hRep hNo hR cD+sourceFoot W source.1+
    preparedFoot W (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1+
    fields W (controls model W k values v hv b hb)+256*W≤
    GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d W k S p.Qv B H red+
      2*attachProfile model W k p.Qv H red+8*(natBits (cap model C d W k S p.Qv B H red)+W)+288*W
  omega

theorem returned_covered {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced
      (rows k (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced)) :
    preparedFoot W (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1≤window model W k values v hv b hb cS cD := by
  unfold window
  dsimp only
  omega

theorem raw_foot {n k : ℕ} (W : ℕ) (budget : ℚ) (prepared : GeneralPaperOriginalStrategyDriver.Prepared n k) :
    GeneralPaperClosedDescriptionStorage.rawFoot W (⟨k,budget,prepared⟩:GeneralPaperAccuracyStrategyDriver.Prepared n)=
      preparedFoot W prepared+natBits k+rationalWordWidth budget := by
  unfold GeneralPaperClosedDescriptionStorage.rawFoot preparedFoot originalFoot
  cases prepared.description <;> dsimp only <;> omega

@[fun_prop]
theorem prepared_scaling {n : ℕ} (k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => preparedProfile W k Qv H red) := by
  unfold preparedProfile descriptionProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
    GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile GeneralPaperEnclosingSourceOwners.columnsProfile
    GeneralPaperEnclosingSourceOwners.columnProfile arrayProfile
  fun_prop

@[fun_prop]
theorem attach_price_scaling {n : ℕ} (model : RationalCostModel) (k H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => attachPrice model W k H red) := by unfold attachPrice;fun_prop

@[fun_prop]
theorem attach_scaling {n : ℕ} (model : RationalCostModel) (k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => attachProfile model W k Qv H red) := by unfold attachProfile attachCap;fun_prop

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model C d W k S Qv B H red) := by unfold price;fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model C d W k S Qv B H red) := by unfold profile cap;fun_prop

end Blotto.GeneralPaperOriginalStrategyConstructionStorage

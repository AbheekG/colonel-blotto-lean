import Blotto.GeneralPaperFramedStrategyConstructionStorage

/-! Complete native final sampler caller. Its once-only raw preparation and
close call retain all owners, parent scalar/work fields and returned sampler.
The same parent proof applies to the successful frame branch; rejection has
a separate complete window and cannot execute close. -/
namespace Blotto.GeneralPaperClosedStrategyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperClosedDescriptionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def closePrice (W T k : ℕ) : ℕ :=
  GeneralPaperSamplerControlsConstructionStorage.price GeneralPaperSamplerControlsConstructionStorage.indexModel W T k+128*W

theorem close_work {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    (GeneralPaperClosedStrategyDriver.close (fun w => w) W raw).2≤
      closePrice W (GeneralPaperClosedSamplerConstructionStorage.rows raw) raw.exponent := by
  cases he:raw.strategies.description with
  | none => simp only [GeneralPaperClosedStrategyDriver.close,he];unfold closePrice;omega
  | some description =>
    have h := GeneralPaperSamplerControlsConstructionStorage.work GeneralPaperSamplerControlsConstructionStorage.indexModel W
      raw.exponent raw.strategies.original.reduced (GeneralPaperClosedStrategyDriver.fields_positive raw) description
      ⟨_,GeneralPaperTrajectoryParameters.rows_power
        (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent⟩
    change (GeneralPaperSamplingControls.make (fun w => w) W raw.exponent raw.strategies.original.reduced
      (GeneralPaperClosedStrategyDriver.fields_positive raw) description
      ⟨_,GeneralPaperTrajectoryParameters.rows_power
        (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent⟩).2≤
      GeneralPaperSamplerControlsConstructionStorage.price GeneralPaperSamplerControlsConstructionStorage.indexModel W
        (GeneralPaperClosedSamplerConstructionStorage.rows raw) raw.exponent at h
    simp only [GeneralPaperClosedStrategyDriver.close,he,GeneralPaperStoredStrategySampler.store]
    unfold closePrice
    omega

def price (W T k rawPrice : ℕ) : ℕ := rawPrice+closePrice W T k+128*W

def cap (W n T k m rawPrice : ℕ) : ℕ := n+k+m+W+price W T k rawPrice+128*W+1

def controls {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) (rawWork : ℕ) : List ℕ :=
  let closed := GeneralPaperClosedStrategyDriver.close (fun w => w) W raw
  [n,W,raw.exponent,raw.strategies.original.reduced.m,rawWork,closed.2,rawWork+closed.2,128*W,rawWork+closed.2+128*W]

def returnedFoot {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  preparedFoot W ⟨raw,(GeneralPaperClosedStrategyDriver.close (fun w => w) W raw).1⟩

def window {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) (rawWork rawWindow : ℕ) : ℕ :=
  rawWindow+GeneralPaperClosedSamplerConstructionStorage.window W raw+returnedFoot W raw+rawFoot W raw+
    fields W (controls W raw rawWork)+256*W

def profile (W n T K k m rawProfile rawPrice : ℕ) : ℕ :=
  9*rawProfile+2*GeneralPaperClosedSamplerConstructionStorage.extraProfile W n T K k m+
    9*(natBits (cap W n T k m rawPrice)+W)+384*W

theorem returned_shape {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) :
    returnedFoot W raw=rawFoot W raw+GeneralPaperClosedSamplerConstructionStorage.returnedFoot W raw+96*W := by
  unfold returnedFoot preparedFoot GeneralPaperClosedSamplerConstructionStorage.returnedFoot
  dsimp only
  cases (GeneralPaperClosedStrategyDriver.close (fun w => w) W raw).1 <;> rfl

theorem returned_covered {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) (rawWork rawWindow : ℕ) :
    returnedFoot W raw≤window W raw rawWork rawWindow := by unfold window;omega

theorem bounded {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) (rawWork rawWindow rawProfile rawPrice : ℕ)
    (hWindow : rawWindow≤rawProfile) (hOwner : rawFoot W raw≤rawWindow) (hWork : rawWork≤rawPrice) :
    window W raw rawWork rawWindow≤profile W n (GeneralPaperClosedSamplerConstructionStorage.rows raw)
      (GeneralPaperClosedSamplerConstructionStorage.labels raw) raw.exponent raw.strategies.original.reduced.m rawProfile rawPrice ∧
      rawWork+(GeneralPaperClosedStrategyDriver.close (fun w => w) W raw).2+128*W≤
        price W (GeneralPaperClosedSamplerConstructionStorage.rows raw) raw.exponent rawPrice := by
  have hClose := GeneralPaperClosedSamplerConstructionStorage.bounded W raw
  change GeneralPaperClosedSamplerConstructionStorage.window W raw≤3*rawFoot W raw+
    GeneralPaperClosedSamplerConstructionStorage.extraProfile W n (GeneralPaperClosedSamplerConstructionStorage.rows raw)
      (GeneralPaperClosedSamplerConstructionStorage.labels raw) raw.exponent raw.strategies.original.reduced.m at hClose
  have hReturn := GeneralPaperClosedSamplerConstructionStorage.returned_covered W raw
  have hReturn' : returnedFoot W raw≤rawFoot W raw+GeneralPaperClosedSamplerConstructionStorage.window W raw+96*W := by
    rw [returned_shape]
    omega
  have hCloseWork := close_work W raw
  have hTotal : rawWork+(GeneralPaperClosedStrategyDriver.close (fun w => w) W raw).2+128*W≤
      price W (GeneralPaperClosedSamplerConstructionStorage.rows raw) raw.exponent rawPrice := by unfold price;omega
  have hf := fields_bound W (natBits (cap W n (GeneralPaperClosedSamplerConstructionStorage.rows raw)
    raw.exponent raw.strategies.original.reduced.m rawPrice)) (controls W raw rawWork) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤9*(natBits (cap W n (GeneralPaperClosedSamplerConstructionStorage.rows raw)
    raw.exponent raw.strategies.original.reduced.m rawPrice)+W)+32*W at hf
  refine ⟨?_,hTotal⟩
  unfold window profile
  omega

open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage

theorem native_bit_bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W B : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m k p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
      let raw := GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb
      let rawWindow := GeneralPaperAccuracyStrategyConstructionStorage.window model W words values v hv b hb cS cD
      let rawProfile := GeneralPaperAccuracyStrategyConstructionStorage.profile model C d W
        (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) k (GeneralPaperValueRoundingInputPrice.inputSize values)
        p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced
      let rawPrice := GeneralPaperAccuracyStrategyConstructionStorage.price model C d W
        (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) k (GeneralPaperValueRoundingInputPrice.inputSize values)
        p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced
      window W raw.1 raw.2 rawWindow≤profile W n (GeneralPaperClosedSamplerConstructionStorage.rows raw.1)
        (GeneralPaperClosedSamplerConstructionStorage.labels raw.1) raw.1.exponent raw.1.strategies.original.reduced.m rawProfile rawPrice ∧
      (GeneralPaperClosedStrategyDriver.bit model W W W words values v hv b hb).2≤
        price W (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) raw.1.exponent rawPrice ∧
      preparedFoot W (GeneralPaperClosedStrategyDriver.bit model W W W words values v hv b hb).1≤
        profile W n (GeneralPaperClosedSamplerConstructionStorage.rows raw.1)
          (GeneralPaperClosedSamplerConstructionStorage.labels raw.1) raw.1.exponent raw.1.strategies.original.reduced.m rawProfile rawPrice := by
  dsimp only
  intro hReference cS cD
  have hRaw := GeneralPaperAccuracyStrategyConstructionStorage.bounded hg W B words values v hv b hb hB hOriginalIndex hReference cS cD
  have hOwner := GeneralPaperAccuracyStrategyConstructionStorage.returned_covered model W words values v hv b hb cS cD
  have h := bounded W (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1 _ _ _ _ hRaw.1 hOwner hRaw.2
  refine ⟨h.1,h.2,?_⟩
  exact (returned_covered W _ _ _).trans h.1

def frameReturnedFoot {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : ℕ :=
  match (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).1 with
  | none => 0
  | some prepared => preparedFoot W prepared.1+listFootprint W (fun _ : Bool => 1) prepared.2+64*W

def frameWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (raw : GeneralPaperAccuracyStrategyDriver.Prepared n×List Bool) (rawWindow : ℕ) : ℕ :=
  window W raw.1 (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2 rawWindow+
    listFootprint W (fun _ : Bool => 1) raw.2+64*W

def frameProfile (W E n T K k m rawProfile rawPrice : ℕ) : ℕ :=
  profile W n T K k m rawProfile rawPrice+E*(1+2*W)+96*W

theorem frame_return_covered {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (raw : GeneralPaperAccuracyStrategyDriver.Prepared n×List Bool) (rawWindow : ℕ)
    (hRaw : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1=some raw) :
    frameReturnedFoot model W frame values v hv b hb≤frameWindow model W frame values v hv b hb raw rawWindow := by
  have hr := GeneralPaperClosedStrategyDriver.frame_some model W W W frame values v hv b hb raw hRaw
  unfold frameReturnedFoot
  rw [hr]
  change returnedFoot W raw.1+listFootprint W (fun _ : Bool => 1) raw.2+64*W≤_
  unfold frameWindow
  exact Nat.add_le_add_right (Nat.add_le_add_right (returned_covered W raw.1 _ rawWindow) _) _

theorem frame_bounded {n : ℕ} (model : RationalCostModel) (W E : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (raw : GeneralPaperAccuracyStrategyDriver.Prepared n×List Bool)
    (hRaw : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1=some raw)
    (hSuffix : raw.2.length≤E) (rawWindow rawProfile rawPrice : ℕ) (hWindow : rawWindow≤rawProfile)
    (hOwner : rawFoot W raw.1≤rawWindow)
    (hWork : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤rawPrice) :
    frameWindow model W frame values v hv b hb raw rawWindow≤frameProfile W E n
      (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) (GeneralPaperClosedSamplerConstructionStorage.labels raw.1)
      raw.1.exponent raw.1.strategies.original.reduced.m rawProfile rawPrice ∧
      (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2≤
        price W (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) raw.1.exponent rawPrice := by
  have h := bounded W raw.1 _ rawWindow rawProfile rawPrice hWindow hOwner hWork
  have hs := list_bound W 1 (fun _ : Bool => 1) raw.2 (fun _ _ => le_rfl)
  have hs' := Nat.mul_le_mul_right (1+2*W) hSuffix
  have hShape : (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2=
      (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2+
      (GeneralPaperClosedStrategyDriver.close (fun w => w) W raw.1).2+128*W := by
    simp only [GeneralPaperClosedStrategyDriver.frame,hRaw]
  refine ⟨?_,by omega⟩
  unfold frameWindow frameProfile
  omega

def rejectedPrice (W rawPrice : ℕ) : ℕ := rawPrice+64*W

def rejectedCap (W n rawPrice : ℕ) : ℕ := n+W+rejectedPrice W rawPrice+64*W+1

def rejectedControls {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  [n,W,(GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2,64*W,
    (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2]

def rejectedWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (rawWindow : ℕ) : ℕ :=
  rawWindow+fields W (rejectedControls model W frame values v hv b hb)+128*W

def rejectedProfile (W n rawProfile rawPrice : ℕ) : ℕ := rawProfile+5*(natBits (rejectedCap W n rawPrice)+W)+160*W

theorem rejected_bounded {n : ℕ} (model : RationalCostModel) (W : ℕ) (frame : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (hRaw : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1=none)
    (rawWindow rawProfile rawPrice : ℕ) (hWindow : rawWindow≤rawProfile)
    (hWork : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2≤rawPrice) :
    rejectedWindow model W frame values v hv b hb rawWindow≤rejectedProfile W n rawProfile rawPrice ∧
      (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2≤rejectedPrice W rawPrice ∧
      frameReturnedFoot model W frame values v hv b hb=0 := by
  have hShape : (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2=
      (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).2+64*W := by
    simp only [GeneralPaperClosedStrategyDriver.frame,hRaw]
  have hTotal : (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2≤rejectedPrice W rawPrice := by
    unfold rejectedPrice
    omega
  have hf := fields_bound W (natBits (rejectedCap W n rawPrice)) (rejectedControls model W frame values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [rejectedControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold rejectedCap
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (rejectedCap W n rawPrice)+W)+32*W at hf
  refine ⟨?_,hTotal,?_⟩
  · unfold rejectedWindow rejectedProfile
    omega
  · simp only [frameReturnedFoot,GeneralPaperClosedStrategyDriver.frame,hRaw]

theorem native_frame_bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W E B : ℕ) (frame : List Bool) (hc : frame.length≤E) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let k := parsed.1.exponent
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m k p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
      let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1,parsed.2)
      let rawWindow := GeneralPaperFramedStrategyConstructionStorage.window model W frame parsed values v hv b hb cS cD
      let rawProfile := GeneralPaperFramedStrategyConstructionStorage.profile model C d W E k
        (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced
      let rawPrice := GeneralPaperFramedStrategyConstructionStorage.price model C d W E k
        (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced
      frameWindow model W frame values v hv b hb raw rawWindow≤frameProfile W E n
        (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) (GeneralPaperClosedSamplerConstructionStorage.labels raw.1)
        raw.1.exponent raw.1.strategies.original.reduced.m rawProfile rawPrice ∧
      (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2≤
        price W (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) raw.1.exponent rawPrice ∧
      frameReturnedFoot model W frame values v hv b hb≤frameProfile W E n
        (GeneralPaperClosedSamplerConstructionStorage.rows raw.1) (GeneralPaperClosedSamplerConstructionStorage.labels raw.1)
        raw.1.exponent raw.1.strategies.original.reduced.m rawProfile rawPrice := by
  dsimp only
  intro hReference cS cD
  let k := parsed.1.exponent
  let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1,parsed.2)
  have hr := (GeneralPaperAccuracyStrategyDriver.frame_some model W W W frame values v hv b hb parsed hRead).1
  change (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1=some raw at hr
  have hRaw := GeneralPaperFramedStrategyConstructionStorage.bounded hg W E B frame hc parsed hRead values v hv b hb hB hOriginalIndex hReference cS cD
  have hReturned := GeneralPaperFramedStrategyConstructionStorage.returned_covered model W frame parsed values v hv b hb cS cD
  have hOwner : rawFoot W raw.1≤GeneralPaperFramedStrategyConstructionStorage.window model W frame parsed values v hv b hb cS cD := by
    have hFoot : rawFoot W raw.1≤GeneralPaperFramedStrategyConstructionStorage.returnedFoot model W frame values v hv b hb := by
      unfold GeneralPaperFramedStrategyConstructionStorage.returnedFoot
      rw [hr]
      dsimp only
      omega
    exact hFoot.trans hReturned
  have h := frame_bounded model W E frame values v hv b hb raw hr
    ((GeneralPaperFramedStrategyConstructionStorage.read_suffix_length W frame parsed hRead).trans hc) _ _ _ hRaw.1 hOwner hRaw.2
  refine ⟨h.1,h.2,?_⟩
  exact (frame_return_covered model W frame values v hv b hb raw _ hr).trans h.1

theorem native_rejected_bounded {n : ℕ} (model : RationalCostModel) (W E B : ℕ) (frame : List Bool) (hc : frame.length≤E)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=none) :
    rejectedWindow model W frame values v hv b hb
        (GeneralPaperFramedStrategyConstructionStorage.rejectedWindow model W frame values v hv b hb)≤
      rejectedProfile W n (GeneralPaperFramedStrategyConstructionStorage.rejectedProfile W E n
        (GeneralPaperValueRoundingInputPrice.inputSize values) B) (GeneralPaperFramedStrategyConstructionStorage.rejectedPrice W E) ∧
      (GeneralPaperClosedStrategyDriver.frame model W W W frame values v hv b hb).2≤
        rejectedPrice W (GeneralPaperFramedStrategyConstructionStorage.rejectedPrice W E) ∧
      frameReturnedFoot model W frame values v hv b hb=0 := by
  have hRaw := GeneralPaperFramedStrategyConstructionStorage.rejected_bounded model W E B frame hc values v hv b hb hB hRead
  have hr : (GeneralPaperAccuracyStrategyDriver.frame model W W W frame values v hv b hb).1=none := by
    simp only [GeneralPaperAccuracyStrategyDriver.frame,hRead]
  exact rejected_bounded model W frame values v hv b hb hr _ _ _ hRaw.1 hRaw.2.1

@[fun_prop]
theorem close_price_scaling (T k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => closePrice W T k) := by
  unfold closePrice GeneralPaperSamplerControlsConstructionStorage.price GeneralPaperSamplingControls.profile
  fun_prop

@[fun_prop]
theorem price_scaling (T k : ℕ) (rawPrice : ℕ → ℕ) (h : GeneralPaperReferenceScaling.Scale rawPrice) :
    GeneralPaperReferenceScaling.Scale (fun W => price W T k (rawPrice W)) := by unfold price;fun_prop

@[fun_prop]
theorem scaling (n T K k m : ℕ) (rawProfile rawPrice : ℕ → ℕ)
    (hP : GeneralPaperReferenceScaling.Scale rawProfile) (hR : GeneralPaperReferenceScaling.Scale rawPrice) :
    GeneralPaperReferenceScaling.Scale (fun W => profile W n T K k m (rawProfile W) (rawPrice W)) := by unfold profile cap;fun_prop

@[fun_prop]
theorem frame_scaling (E n T K k m : ℕ) (rawProfile rawPrice : ℕ → ℕ)
    (hP : GeneralPaperReferenceScaling.Scale rawProfile) (hR : GeneralPaperReferenceScaling.Scale rawPrice) :
    GeneralPaperReferenceScaling.Scale (fun W => frameProfile W E n T K k m (rawProfile W) (rawPrice W)) := by unfold frameProfile;fun_prop

@[fun_prop]
theorem rejected_price_scaling (rawPrice : ℕ → ℕ) (h : GeneralPaperReferenceScaling.Scale rawPrice) :
    GeneralPaperReferenceScaling.Scale (fun W => rejectedPrice W (rawPrice W)) := by unfold rejectedPrice;fun_prop

@[fun_prop]
theorem rejected_scaling (n : ℕ) (rawProfile rawPrice : ℕ → ℕ)
    (hP : GeneralPaperReferenceScaling.Scale rawProfile) (hR : GeneralPaperReferenceScaling.Scale rawPrice) :
    GeneralPaperReferenceScaling.Scale (fun W => rejectedProfile W n (rawProfile W) (rawPrice W)) := by unfold rejectedProfile rejectedCap;fun_prop

end Blotto.GeneralPaperClosedStrategyConstructionStorage

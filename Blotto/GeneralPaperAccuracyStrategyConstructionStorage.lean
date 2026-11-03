import Blotto.GeneralPaperOriginalStrategyConstructionStorage

/-! Complete outer accuracy-driven preparation. The exponent wrapper and
word-input caller retain complete original/accuracy/returned owners, once-only
child windows and literal parent scalar/work fields. Observers are erased. -/
namespace Blotto.GeneralPaperAccuracyStrategyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def ownerTail (k B : ℕ) : ℕ := natBits k+1+2*B

noncomputable def exponentPrice {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalStrategyConstructionStorage.price model C d W k S Qv B H red+64*W

noncomputable def exponentCap {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ := n+k+W+exponentPrice model C d W k S Qv B H red+64*W+1

def exponentControls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  [n,k,W,(GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2,64*W,
    (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2]

noncomputable def exponentWindow {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced
      (rows k (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced)) : ℕ :=
  GeneralPaperOriginalStrategyConstructionStorage.window model W k values v hv b hb cS cD+
    preparedFoot W (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1+
    GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1+
    fields W (exponentControls model W k values v hv b hb)+128*W

noncomputable def exponentProfile {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  3*GeneralPaperOriginalStrategyConstructionStorage.profile model C d W k S Qv B H red+ownerTail k B+
    6*(natBits (exponentCap model C d W k S Qv B H red)+W)+160*W

theorem exponent_return_covered {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced
      (rows k (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced)) :
    GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1≤
      exponentWindow model W k values v hv b hb cS cD := by unfold exponentWindow;omega

theorem exponent_bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m k p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
      exponentWindow model W k values v hv b hb cS cD≤
        exponentProfile model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
          (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced ∧
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2≤
        exponentPrice model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
          (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced := by
  dsimp only
  intro hReference cS cD
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width p.reduced.m k
  have hCore := GeneralPaperOriginalStrategyConstructionStorage.bounded hg W k B values v hv b hb hB hOriginalIndex hReference cS cD
  change GeneralPaperOriginalStrategyConstructionStorage.window model W k values v hv b hb cS cD≤
    GeneralPaperOriginalStrategyConstructionStorage.profile model C d W k S p.Qv B H p.reduced ∧
    (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2≤
      GeneralPaperOriginalStrategyConstructionStorage.price model C d W k S p.Qv B H p.reduced at hCore
  have hReturn := (GeneralPaperOriginalStrategyConstructionStorage.returned_covered model W k values v hv b hb cS cD).trans hCore.1
  have hBudget := rationalWordWidth_of_height hB
  have hRaw : GeneralPaperClosedDescriptionStorage.rawFoot W
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1≤
      GeneralPaperOriginalStrategyConstructionStorage.profile model C d W k S p.Qv B H p.reduced+ownerTail k B := by
    rw [show (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1=
      ⟨k,b,(GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).1⟩ from rfl,raw_foot]
    unfold ownerTail
    omega
  have hShape : (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2=
      (GeneralPaperOriginalStrategyDriver.bit model W W W k values v hv b hb).2+64*W := rfl
  have hWork : (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2≤
      exponentPrice model C d W k S p.Qv B H p.reduced := by unfold exponentPrice;omega
  have hf := fields_bound W (natBits (exponentCap model C d W k S p.Qv B H p.reduced))
    (exponentControls model W k values v hv b hb) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [exponentControls,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold exponentCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤6*(natBits (exponentCap model C d W k S p.Qv B H p.reduced)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  change exponentWindow model W k values v hv b hb cS cD≤exponentProfile model C d W k S p.Qv B H p.reduced
  unfold exponentWindow exponentProfile
  omega

noncomputable def price {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.price W E+exponentPrice model C d W k S Qv B H red+64*W

noncomputable def cap {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ := n+k+E+W+price model C d W E k S Qv B H red+64*W+1

def controls {n : ℕ} (model : RationalCostModel) (W : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  let accuracy := GeneralPaperBinaryAccuracy.prepare (fun w => w) W words
  let core := GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W accuracy.1 values v hv b hb
  [n,W,accuracy.1,accuracy.2,core.2,accuracy.2+core.2,64*W,
    (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2]

noncomputable def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced.m
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
      (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced
      (rows (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
        (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced)) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.window W words+
    exponentWindow model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv b hb cS cD+
    GeneralPaperBooleanRulerWorkStorage.wordFoot W words.numerator+GeneralPaperBooleanRulerWorkStorage.wordFoot W words.denominator+
    GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1+
    fields W (controls model W words values v hv b hb)+128*W

noncomputable def profile {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.profile W E+2*exponentProfile model C d W k S Qv B H red+
    E*(1+2*W)+8*(natBits (cap model C d W E k S Qv B H red)+W)+352*W

theorem returned_covered {n : ℕ} (model : RationalCostModel) (W : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced.m
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
      (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
      (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced
      (rows (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
        (GeneralPaperOriginalSourceValuePreparation.run true model W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1 values v hv).1.reduced)) :
    GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1≤
      window model W words values v hv b hb cS cD := by unfold window;omega

theorem bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W B : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hOriginalIndex : binaryWordWidth (n+1)≤W) :
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (cS : SourceCursor p.reduced.m k p.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
      window model W words values v hv b hb cS cD≤profile model C d W (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) k
        (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced ∧
      (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2≤
        price model C d W (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) k
          (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced := by
  dsimp only
  intro hReference cS cD
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
  let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize words
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width p.reduced.m k
  have hCore := exponent_bounded hg W k B values v hv b hb hB hOriginalIndex hReference cS cD
  change exponentWindow model W k values v hv b hb cS cD≤exponentProfile model C d W k S p.Qv B H p.reduced ∧
    (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2≤
      exponentPrice model C d W k S p.Qv B H p.reduced at hCore
  have hRaw := (exponent_return_covered model W k values v hv b hb cS cD).trans hCore.1
  change GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1≤
    exponentProfile model C d W k S p.Qv B H p.reduced at hRaw
  have hAccuracy := GeneralPaperBinaryAccuracyConstructionStorage.bounded W words
  have hAccuracyWork := GeneralPaperBinaryAccuracyConstructionStorage.work W words
  change GeneralPaperBinaryAccuracyConstructionStorage.window W words≤GeneralPaperBinaryAccuracyConstructionStorage.profile W E at hAccuracy
  change (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2≤GeneralPaperBinaryAccuracyConstructionStorage.price W E at hAccuracyWork
  have hN := GeneralPaperBooleanRulerWorkStorage.word_bound W words.numerator
  have hD := GeneralPaperBooleanRulerWorkStorage.word_bound W words.denominator
  have hSize : words.numerator.width+words.denominator.width=E := by unfold E GeneralPaperBinaryAccuracyConstructionStorage.inputSize;omega
  have hShape : (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2=
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2+
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2+64*W := rfl
  have hWork : (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2≤
      price model C d W E k S p.Qv B H p.reduced := by unfold price;omega
  have hf := fields_bound W (natBits (cap model C d W E k S p.Qv B H p.reduced)) (controls model W words values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[n,W,k,(GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2,
      (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2,
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2+
        (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).2,64*W,
      (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤8*(natBits (cap model C d W E k S p.Qv B H p.reduced)+W)+32*W at hf
  have hWords : GeneralPaperBooleanRulerWorkStorage.wordFoot W words.numerator+
    GeneralPaperBooleanRulerWorkStorage.wordFoot W words.denominator≤E*(1+2*W)+192*W := by nlinarith only [hN,hD,hSize]
  refine ⟨?_,hWork⟩
  change window model W words values v hv b hb cS cD≤profile model C d W E k S p.Qv B H p.reduced
  unfold window profile
  change GeneralPaperBinaryAccuracyConstructionStorage.window W words+exponentWindow model W k values v hv b hb cS cD+
    GeneralPaperBooleanRulerWorkStorage.wordFoot W words.numerator+GeneralPaperBooleanRulerWorkStorage.wordFoot W words.denominator+
    GeneralPaperClosedDescriptionStorage.rawFoot W (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1+
    fields W (controls model W words values v hv b hb)+128*W≤
    GeneralPaperBinaryAccuracyConstructionStorage.profile W E+2*exponentProfile model C d W k S p.Qv B H p.reduced+
      E*(1+2*W)+8*(natBits (cap model C d W E k S p.Qv B H p.reduced)+W)+352*W
  omega

@[fun_prop]
theorem exponent_price_scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => exponentPrice model C d W k S Qv B H red) := by unfold exponentPrice;fun_prop

@[fun_prop]
theorem exponent_scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => exponentProfile model C d W k S Qv B H red) := by unfold exponentProfile exponentCap;fun_prop

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model C d W E k S Qv B H red) := by
  unfold price GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.step
  fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model C d W E k S Qv B H red) := by unfold profile cap;fun_prop

end Blotto.GeneralPaperAccuracyStrategyConstructionStorage

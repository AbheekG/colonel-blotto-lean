import Blotto.GeneralPaperNativeCompilerPairEquilibrium

/-! Actual normalized value-array construction. Complete input weights,
returned values, native fill buffers/frames, one reached cast/division and
parent work fields are counted. All bounds are erased, without a census. -/
namespace Blotto.GeneralPaperRetainedFieldValuesStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def width (Q : ℕ) : ℕ := GeneralPaperReducedValueArrayPrice.width Q 1

def callback {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable m ℕ) (j : Fin m) : ℚ×ℕ :=
  ((weights.read j:ℚ)/Q,model.rat (rationalWordWidth (weights.read j:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (weights.read j) Q+32*arrayWord W m)

def callbackPrice (model : RationalCostModel) (W m Q : ℕ) : ℕ := 3*model.rat (width Q)+32*arrayWord W m

def scalarCap (model : RationalCostModel) (W m Q : ℕ) : ℕ := m+Q+callbackPrice model W m Q+1

def scalarWindow {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable m ℕ) (j : Fin m) : ℕ :=
  let w := weights.read j
  let cast := model.rat (rationalWordWidth (w:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) w Q
  natBits w+rationalWordWidth (w:ℚ)+rationalWordWidth (Q:ℚ)+rationalWordWidth (callback model W Q weights j).1+
    cast+division+fields (arrayWord W m) [m,Q,j.val,w,cast,division,(callback model W Q weights j).2,cast+division,32*arrayWord W m]+128*arrayWord W m

def scalarProfile (model : RationalCostModel) (W m Q : ℕ) : ℕ :=
  natBits Q+3*width Q+3*model.rat (width Q)+9*(natBits (scalarCap model W m Q)+arrayWord W m)+160*arrayWord W m

theorem callback_bounds {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable m ℕ)
    (hw : ∀ j,weights.read j≤Q) (j : Fin m) :
    rationalWordWidth (callback model W Q weights j).1≤width Q ∧
      (callback model W Q weights j).2≤callbackPrice model W m Q := by
  have hCast := model.monotone (GeneralPaperReducedValueArrayPrice.cast_width _ Q 1 (hw j))
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (weights.read j) Q
    (width Q) (GeneralPaperReducedValueArrayPrice.cast_width _ Q 1 (hw j))
    (GeneralPaperReducedValueArrayPrice.cast_width Q Q 1 le_rfl) (GeneralPaperReducedValueArrayPrice.ratio_width _ Q 1 (hw j))
  change model.rat (rationalWordWidth (weights.read j:ℚ))≤model.rat (width Q) at hCast
  exact ⟨GeneralPaperReducedValueArrayPrice.ratio_width _ Q 1 (hw j),by unfold callback callbackPrice;omega⟩

theorem scalar_bound {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable m ℕ)
    (hw : ∀ j,weights.read j≤Q) (j : Fin m) : scalarWindow model W Q weights j≤scalarProfile model W m Q := by
  let A := arrayWord W m
  let cast := model.rat (rationalWordWidth (weights.read j:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (weights.read j) Q
  have hwN : natBits (weights.read j)≤natBits Q := Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1
  have hCastWord : rationalWordWidth (weights.read j:ℚ)≤width Q := GeneralPaperReducedValueArrayPrice.cast_width _ Q 1 (hw j)
  have hQWord : rationalWordWidth (Q:ℚ)≤width Q := GeneralPaperReducedValueArrayPrice.cast_width Q Q 1 le_rfl
  have hEntry := (callback_bounds model W Q weights hw j).1
  have hCallback := (callback_bounds model W Q weights hw j).2
  have hCast : cast≤model.rat (width Q) := model.monotone hCastWord
  have hDiv : division≤2*model.rat (width Q) := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (weights.read j) Q
    (width Q) hCastWord hQWord hEntry
  have hWeight := hw j
  have hf := fields_bound A (natBits (scalarCap model W m Q))
    [m,Q,j.val,weights.read j,cast,division,(callback model W Q weights j).2,cast+division,32*A] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals
        unfold scalarCap callbackPrice at *
        try dsimp only [A] at *
        have := j.isLt
        omega)
  change fields A _≤9*(natBits (scalarCap model W m Q)+A)+32*A at hf
  unfold scalarWindow scalarProfile
  change natBits (weights.read j)+rationalWordWidth (weights.read j:ℚ)+rationalWordWidth (Q:ℚ)+
    rationalWordWidth (callback model W Q weights j).1+cast+division+
    fields A [m,Q,j.val,weights.read j,cast,division,(callback model W Q weights j).2,cast+division,32*A]+128*A≤_
  change _≤natBits Q+3*width Q+3*model.rat (width Q)+9*(natBits (scalarCap model W m Q)+A)+160*A
  omega

def price (model : RationalCostModel) (W m Q : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap (arrayWord W m) m (callbackPrice model W m Q)+model.rat (width Q)+192*arrayWord W m

def metadataCap (model : RationalCostModel) (W m Q : ℕ) : ℕ := m+Q+price model W m Q+1

def window {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) (cursor : ℕ) (hc : cursor≤m) : ℕ :=
  let A := arrayWord W m
  let built := PaperIndexedArrayConstruction.run (fun w => w) A (callback model W Q weights)
  let result := GeneralPaperRetainedFieldValues.run true model W Q hQ weights hp hs
  let qCast := model.rat (rationalWordWidth (Q:ℚ))
  GeneralPaperEncodedNatArray.footprint W weights+rationalWordWidth (Q:ℚ)+
    GeneralPaperEncodedRationalRows.rowFootprint W result.1.values+
    GeneralPaperNativePayloadFillStorage.window A rationalWordWidth (callback model W Q weights)
      (scalarWindow model W Q weights) cursor hc+qCast+
    fields W [m,Q,W,A,cursor,built.2,result.2,qCast,128*A,64*A,built.2+qCast,built.2+qCast+128*A]+128*A

def profile (model : RationalCostModel) (W m Q : ℕ) : ℕ :=
  m*(natBits Q+W)+32*W+width Q+GeneralPaperEncodedRationalRows.rowProfile W m (width Q)+
    GeneralPaperNativePayloadFillStorage.profile (arrayWord W m) (width Q) m (callbackPrice model W m Q) (scalarProfile model W m Q)+
    model.rat (width Q)+12*(natBits (metadataCap model W m Q)+W)+160*arrayWord W m

theorem data {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperRetainedFieldValues.run true model W Q hQ weights hp hs).1.values=
      (PaperIndexedArrayConstruction.run (fun w => w) (arrayWord W m) (callback model W Q weights)).1 := by
  rw [GeneralPaperRetainedFieldValues.data,PaperIndexedArrayConstruction.run_data]
  rfl

theorem bounded {m : ℕ} (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) (cursor : ℕ) (hc : cursor≤m) :
    window model W Q hQ weights hp hs cursor hc≤profile model W m Q ∧
      (GeneralPaperRetainedFieldValues.run true model W Q hQ weights hp hs).2≤price model W m Q := by
  let A := arrayWord W m
  let built := PaperIndexedArrayConstruction.run (fun w => w) A (callback model W Q weights)
  let result := GeneralPaperRetainedFieldValues.run true model W Q hQ weights hp hs
  let qCast := model.rat (rationalWordWidth (Q:ℚ))
  have hw (j) : weights.read j≤Q := GeneralPaperSourceScoreHeights.weight_le Q weights hs j
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W m
  have hIndex := GeneralPaperSummaryArrayControls.array_index W m m le_rfl
  have hCallback j := callback_bounds model W Q weights hw j
  have hFill := GeneralPaperNativePayloadFillStorage.bounded A (width Q) (callbackPrice model W m Q) (scalarProfile model W m Q)
    rationalWordWidth (callback model W Q weights) (scalarWindow model W Q weights) (fun j => (hCallback j).1)
    (fun j => (hCallback j).2) (scalar_bound model W Q weights hw) hA hIndex cursor hc
  have hBuilt := GeneralPaperNativePayloadFillStorage.prefix_work A (callbackPrice model W m Q) (callback model W Q weights)
    (fun j => (hCallback j).2) hA hIndex m le_rfl
  change built.2≤GeneralPaperNativePayloadFillStorage.workCap A m (callbackPrice model W m Q) at hBuilt
  have hQWord : rationalWordWidth (Q:ℚ)≤width Q := GeneralPaperReducedValueArrayPrice.cast_width Q Q 1 le_rfl
  have hQCast : qCast≤model.rat (width Q) := model.monotone hQWord
  have hShape : result.2=built.2+qCast+192*A := by
    change built.2+qCast+128*A+64*A=built.2+qCast+192*A
    omega
  have hWork : result.2≤price model W m Q := by unfold price;simp only [A] at *;omega
  have hWeights := GeneralPaperEncodedNatArray.bounded W (natBits Q) weights (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hValues := GeneralPaperEncodedRationalRows.row_bound W (width Q) result.1.values (by
    intro j
    rw [GeneralPaperRetainedFieldValues.data,FixedArrayTable.read_ofFn]
    exact (GeneralPaperSourceScoreHeights.value_height Q hQ weights hp hs j).mono (by unfold width GeneralPaperReducedValueArrayPrice.width;omega))
  have hControlA : A≤price model W m Q := by unfold price;dsimp only [A];omega
  have hW : W≤A := by unfold A arrayWord;omega
  have hf := fields_bound W (natBits (metadataCap model W m Q))
    [m,Q,W,A,cursor,built.2,result.2,qCast,128*A,64*A,built.2+qCast,built.2+qCast+128*A] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price at *;simp only [A] at *;omega)
  change fields W _≤12*(natBits (metadataCap model W m Q)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  unfold window profile
  change GeneralPaperEncodedNatArray.footprint W weights+rationalWordWidth (Q:ℚ)+
    GeneralPaperEncodedRationalRows.rowFootprint W result.1.values+
    GeneralPaperNativePayloadFillStorage.window A rationalWordWidth (callback model W Q weights)
      (scalarWindow model W Q weights) cursor hc+qCast+
    fields W [m,Q,W,A,cursor,built.2,result.2,qCast,128*A,64*A,built.2+qCast,built.2+qCast+128*A]+128*A≤_
  change _≤m*(natBits Q+W)+32*W+width Q+GeneralPaperEncodedRationalRows.rowProfile W m (width Q)+
    GeneralPaperNativePayloadFillStorage.profile A (width Q) m (callbackPrice model W m Q) (scalarProfile model W m Q)+
    model.rat (width Q)+12*(natBits (metadataCap model W m Q)+W)+160*A
  omega

end Blotto.GeneralPaperRetainedFieldValuesStorage

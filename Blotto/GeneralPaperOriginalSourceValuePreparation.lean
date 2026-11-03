import Blotto.GeneralPaperArithmeticDriverSharpTime

/-! Retain the original reduction and second value-rounding return once.
The actual positive integer weights and denominator feed the source; the
first weights/maps remain available for original-field reconstruction. -/
namespace Blotto.GeneralPaperOriginalSourceValuePreparation
open GeneralPaperSourceRowsExecution GeneralPaperSourceWordGrowth
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

structure Output (n : ℕ) where
  reduced : GeneralPaperReducedValuesDriver.Output n
  weights : FixedArrayTable reduced.m ℕ
  Qv : ℕ
  Qv_positive : 0<Qv
  weights_positive : ∀ j,0<weights.read j
  weight_sum : ∑ j,weights.read j=Qv

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) : Output n×ℕ :=
  let reduced := GeneralPaperOriginalValueReduction.run bits model W k values
  let rounded := GeneralPaperValueRoundingPaperContract.run bits model W 512 k reduced.1.values
  let hp : 0<rounded.1.2 ∧ ∀ j,0<rounded.1.1.read j := by
    exact GeneralPaperValueRoundingPaperContract.positivity bits model W 512 k (by decide) reduced.1.values
      (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl)
  (⟨reduced.1,rounded.1.1,rounded.1.2,hp.1,hp.2,
    GeneralPaperValueRoundingPaperContract.source_sum bits model W 512 k reduced.1.values⟩,
    reduced.2+rounded.2+128*address bits W (n+reduced.1.m))

theorem reduced_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W k values v hv).1.reduced=(GeneralPaperOriginalValueReduction.run bits model W k values).1 := rfl

theorem weights_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W k values v hv).1.weights=
      (GeneralPaperValueRoundingPaperContract.run bits model W 512 k (GeneralPaperOriginalValueReduction.run bits model W k values).1.values).1.1 := rfl

theorem denominator_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W k values v hv).1.Qv=
      (GeneralPaperValueRoundingPaperContract.run bits model W 512 k (GeneralPaperOriginalValueReduction.run bits model W k values).1.values).1.2 := rfl

def input {n : ℕ} (o : Output n) (k B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) : Input where
  m := o.reduced.m
  k := k
  Qv := o.Qv
  B := B
  b := b
  hb := hb
  hB := hB
  reciprocal := false
  weights := o.weights
  weight_sum := o.weight_sum

theorem input_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    input (run bits model W k values v hv).1 k B b hb hB=
      GeneralPaperRoundedValueSourceInput.input bits model W k B
        (GeneralPaperOriginalValueReduction.run bits model W k values).1.values b hb hB false := rfl

theorem count_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    0<(run bits model W k values v hv).1.reduced.m ∧
      (run bits model W k values v hv).1.reduced.m≤n ∧
      (run bits model W k values v hv).1.reduced.m<18*2^k :=
  GeneralPaperOriginalValueReduction.count_bounds bits model W k values v hv

theorem denominator {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W k values v hv).1.Qv≤513*(run bits model W k values v hv).1.reduced.m*2^k :=
  GeneralPaperValueRoundingPaperContract.reduced_denominator bits model W k _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl)

theorem denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    binaryWordWidth (run bits model W k values v hv).1.Qv≤binaryWordWidth (run bits model W k values v hv).1.reduced.m+k+11 :=
  GeneralPaperValueRoundingPaperContract.reduced_denominator_word bits model W k _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl)

theorem original_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (run bits model W k values v hv).1
    (∑ j,|(o.reduced.firstWeights.read j:ℚ)/o.reduced.denominator-v.weight j|)≤(1/(2:ℚ)^k)/128 :=
  GeneralPaperReducedInputContract.retained_original_error bits model W k values v hv

theorem reduced_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (run bits model W k values v hv).1
    (∑ j,|(o.weights.read j:ℚ)/o.Qv-o.reduced.values.read j|)≤(1/(2:ℚ)^k)/256 :=
  GeneralPaperValueRoundingPaperContract.reduced_error bits model W k _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl)

theorem equal_representatives {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (run bits model W k values v hv).1
    ∀ (i j : Fin o.reduced.m),o.reduced.replaced=true → o.reduced.classified.heavy.size≤ i.val → o.reduced.classified.heavy.size≤ j.val →
      o.weights.read i=o.weights.read j :=
  GeneralPaperReducedInputContract.rounded_equal_representatives bits bits model W W k values v hv

theorem field_cap {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    (input (run bits model W k values v hv).1 k B b hb hB).m≤
      18*GeneralPaperNativeSourceRates.accuracy (input (run bits model W k values v hv).1 k B b hb hB) :=
  (count_bounds bits model W k values v hv).2.2.le

end Blotto.GeneralPaperOriginalSourceValuePreparation

import Blotto.GeneralPaperValueRoundingPaperContract

/-! Erased source-input observation of the actual reduced-value rounding
return. Positive weights, normalization and short Qv are derived. Final
execution must retain this return once; this observer is not a replay in
that driver and does not claim reduction/lifting or original-input closure. -/
namespace Blotto.GeneralPaperRoundedValueSourceInput
open GeneralPaperSourceWordGrowth
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

noncomputable def input {m : ℕ} (bits : Bool) (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) : Input :=
  let rounded := (GeneralPaperValueRoundingPaperContract.run bits actual W 512 k values).1
  {m:=m,k:=k,Qv:=rounded.2,B:=B,b:=b,hb:=hb,hB:=hB,reciprocal:=reciprocal,weights:=rounded.1,
    weight_sum:=GeneralPaperValueRoundingPaperContract.source_sum bits actual W 512 k values}

theorem positive {m : ℕ} (bits : Bool) (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let x := input bits actual W k B values b hb hB reciprocal
    0<x.Qv ∧ ∀ j,0<x.weights.read j :=
  GeneralPaperValueRoundingPaperContract.positivity bits actual W 512 k (by decide) values v hv

theorem denominator {m : ℕ} (bits : Bool) (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    (input bits actual W k B values b hb hB reciprocal).Qv≤513*m*2^k :=
  GeneralPaperValueRoundingPaperContract.reduced_denominator bits actual W k values v hv

theorem denominator_word {m : ℕ} (bits : Bool) (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    binaryWordWidth (input bits actual W k B values b hb hB reciprocal).Qv≤binaryWordWidth m+k+11 :=
  GeneralPaperValueRoundingPaperContract.reduced_denominator_word bits actual W k values v hv

theorem approximation {m : ℕ} (bits : Bool) (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let x := input bits actual W k B values b hb hB reciprocal
    (∑ j,|(x.weights.read j:ℚ)/x.Qv-v.weight j|)≤(1/(2:ℚ)^k)/256 :=
  GeneralPaperValueRoundingPaperContract.reduced_error bits actual W k values v hv

theorem models_data {m : ℕ} (actual : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    input true actual W k B values b hb hB reciprocal=input false actual 1 k B values b hb hB reciprocal := by
  have h := GeneralPaperValueRoundingPaperContract.models_data actual W 512 k values v hv
  unfold input
  dsimp only
  congr 1
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h

theorem source_checks {m : ℕ} (bits valueBits : Bool) (actual : RationalCostModel) (W Wv k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let x := input valueBits actual Wv k B values b hb hB reciprocal
    (GeneralPaperPhysicalResponseRowsContract.preparedRun bits actual W x).1.2=true := by
  dsimp only
  exact GeneralPaperPhysicalResponseRowsContract.native_checks bits actual W _ v.fields_positive
    (positive valueBits actual Wv k B values v hv b hb hB reciprocal).1

theorem source_hard_budget {m : ℕ} (bits valueBits : Bool) (actual : RationalCostModel) (W Wv k B : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows) :
    let x := input valueBits actual Wv k B values b hb hB reciprocal
    Feasible (GeneralPaperInitializerPreparedPoint.ownBudget m k (b:ℝ) reciprocal:ℝ)
      (fun j => (((GeneralPaperPhysicalResponseRowsContract.preparedRun bits actual W x).1.1.read i).read j:ℝ)) := by
  dsimp only
  exact GeneralPaperPhysicalResponseRowsContract.native_hard_budget bits actual W _ v.fields_positive
    (positive valueBits actual Wv k B values v hv b hb hB reciprocal).1 i

end Blotto.GeneralPaperRoundedValueSourceInput

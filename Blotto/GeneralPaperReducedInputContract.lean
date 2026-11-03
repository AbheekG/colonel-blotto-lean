import Blotto.GeneralPaperOriginalValueReductionPrice

/-! Original native input preparation now supplies the reduced game's
values and all source premises. This semantic source/compiler join uses the
same returned arrays and preserves actual independent laws and hard budgets.
Finite-circle lifting and the full priced final driver remain separate. -/
namespace Blotto.GeneralPaperReducedInputContract
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def EqualRepresentatives {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) : Prop :=
  ∀ (i j : Fin o.m),o.replaced=true → o.classified.heavy.size ≤ i.val → o.classified.heavy.size ≤ j.val →
    o.values.read i=o.values.read j

theorem equal_representatives {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    EqualRepresentatives (GeneralPaperReducedValuesDriver.run bits model W k Q weights).1 := by
  rw [GeneralPaperReducedValuesDriver.data]
  unfold GeneralPaperReducedValuesDriver.specification
  split_ifs
  · intro i j _ hi hj
    simp only [FixedArrayTable.read_ofFn]
    rw [dite_eq_right (not_lt.mpr hi),dite_eq_right (not_lt.mpr hj)]
  · intro _ _ h
    cases h

theorem original_equal_representatives {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    EqualRepresentatives (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact equal_representatives bits model W k _ _

theorem rounded_equal_representatives {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    ∀ (i j : Fin reduced.m),reduced.replaced=true → reduced.classified.heavy.size ≤ i.val → reduced.classified.heavy.size ≤ j.val →
      (GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k reduced.values).1.1.read i=
        (GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k reduced.values).1.1.read j := by
  dsimp only
  intro i j h hi hj
  exact GeneralPaperValueRoundingPaperContract.equal_entries valueBits model Wv 512 k _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) i j
    (original_equal_representatives bits model W k values i j h hi hj)

theorem source_positive {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let x := GeneralPaperRoundedValueSourceInput.input valueBits model Wv k B reduced.values b hb hB reciprocal
    0<x.Qv ∧ ∀ j,0<x.weights.read j := by
  exact GeneralPaperRoundedValueSourceInput.positive valueBits model Wv k B _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb hB reciprocal

theorem source_denominator {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let x := GeneralPaperRoundedValueSourceInput.input valueBits model Wv k B reduced.values b hb hB reciprocal
    x.Qv≤513*reduced.m*2^k ∧ binaryWordWidth x.Qv≤binaryWordWidth reduced.m+k+11 := by
  exact ⟨GeneralPaperRoundedValueSourceInput.denominator valueBits model Wv k B _
      (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb hB reciprocal,
    GeneralPaperRoundedValueSourceInput.denominator_word valueBits model Wv k B _
      (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb hB reciprocal⟩

theorem source_checks {n : ℕ} (bits valueBits sourceBits : Bool) (model : RationalCostModel) (W Wv Ws k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let x := GeneralPaperRoundedValueSourceInput.input valueBits model Wv k B reduced.values b hb hB reciprocal
    (GeneralPaperPhysicalResponseRowsContract.preparedRun sourceBits model Ws x).1.2=true := by
  exact GeneralPaperRoundedValueSourceInput.source_checks sourceBits valueBits model Ws Wv k B _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb hB reciprocal

theorem retained_original_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    (∑ j,|(reduced.firstWeights.read j:ℚ)/reduced.denominator-v.weight j|)≤(1/(2:ℚ)^k)/128 := by
  dsimp only
  rw [(GeneralPaperOriginalValueReduction.retained bits model W k values).1,
    (GeneralPaperOriginalValueReduction.retained bits model W k values).2]
  exact GeneralPaperValueRoundingPaperContract.original_error bits model W k values v hv

theorem source_hard_budget {n : ℕ} (bits valueBits sourceBits : Bool) (model : RationalCostModel) (W Wv Ws k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) (reciprocal : Bool)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare
      (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run bits model W k values).1.m k).lambda k).rows) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let x := GeneralPaperRoundedValueSourceInput.input valueBits model Wv k B reduced.values b hb hB reciprocal
    Feasible (GeneralPaperInitializerPreparedPoint.ownBudget reduced.m k (b:ℝ) reciprocal:ℝ)
      (fun j => (((GeneralPaperPhysicalResponseRowsContract.preparedRun sourceBits model Ws x).1.1.read i).read j:ℝ)) := by
  exact GeneralPaperRoundedValueSourceInput.source_hard_budget sourceBits valueBits model Ws Wv k B _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb hB reciprocal i

theorem run_security {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    let reduced := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k values v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet reduced.m k).lambda k
    ∃ pair,GeneralPaperRoundedValueCanonical.run valueBits model Wv k reduced.values redValues (fun _ => rfl) b=some pair ∧
      Supported 1 (GeneralPaperSourcePairCanonical.richLaw pair hT) ∧
      Supported b (GeneralPaperSourcePairCanonical.poorLaw pair hT b) ∧
      security redValues.values 1 (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
        security redValues.values b (GeneralPaperSourcePairCanonical.richLaw pair hT)<1+(1/(2:ℝ)^k)/16 ∧
      regret redValues.values 1 (GeneralPaperSourcePairCanonical.richLaw pair hT) (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
        regret redValues.values b (GeneralPaperSourcePairCanonical.poorLaw pair hT b) (GeneralPaperSourcePairCanonical.richLaw pair hT)<(1/(2:ℝ)^k)/16 := by
  exact GeneralPaperRoundedValueCanonical.run_security valueBits model Wv k _
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb

end Blotto.GeneralPaperReducedInputContract

import Blotto.GeneralPaperReducedValueArray

/-! Classify once and construct one reduced-value array. The return keeps
the actual first-round integer weights, denominator and original index maps
needed for reconstruction. Positivity/normalization are proved from this
return; they are not executable validation or supplied source assumptions. -/
namespace Blotto.GeneralPaperReducedValuesDriver
open GeneralPaperSourceRowsExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

structure Output (n : ℕ) where
  firstWeights : FixedArrayTable n ℕ
  denominator : ℕ
  classified : GeneralPaperLightFieldScan.State n
  representatives : ℕ
  replaced : Bool
  m : ℕ
  values : FixedArrayTable m ℚ

def Positive {n : ℕ} (o : Output n) : Prop := ∀ j,0<o.values.read j
def Normalized {n : ℕ} (o : Output n) : Prop := (∑ j,o.values.read j)=1

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : Output n × ℕ :=
  let classified := GeneralPaperLightFieldClassification.run bits model W k Q weights
  if classified.1.2<classified.1.1.light.size then
    let built := GeneralPaperReducedValueArray.replaced bits model W Q classified.1.2 classified.1.1.lightWeight weights classified.1.1.heavy
    (⟨weights,Q,classified.1.1,classified.1.2,true,classified.1.1.heavy.size+classified.1.2,built.1⟩,
      classified.2+built.2+128*address bits W (n+classified.1.1.heavy.size+classified.1.2))
  else
    let built := GeneralPaperReducedValueArray.identity bits model W Q weights
    (⟨weights,Q,classified.1.1,classified.1.2,false,n,built.1⟩,
      classified.2+built.2+128*address bits W (n+n))

noncomputable def specification {n : ℕ} (Q : ℕ) (weights : FixedArrayTable n ℕ)
    (state : GeneralPaperLightFieldScan.State n) (R : ℕ) : Output n :=
  if R<state.light.size then
    ⟨weights,Q,state,R,true,state.heavy.size+R,FixedArrayTable.ofFn
      (fun j => if h:j.val<state.heavy.size then (weights.read state.heavy[j.val]:ℚ)/Q else (state.lightWeight:ℚ)/(Q*R:ℕ))⟩
  else ⟨weights,Q,state,R,false,n,FixedArrayTable.ofFn (fun j => (weights.read j:ℚ)/Q)⟩

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run bits model W k Q weights).1=specification Q weights
      (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1
      (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.2 := by
  unfold run specification
  dsimp only
  split_ifs <;> simp only [GeneralPaperReducedValueArray.replaced_data,GeneralPaperReducedValueArray.identity_data]

theorem retained {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run bits model W k Q weights).1.firstWeights=weights ∧ (run bits model W k Q weights).1.denominator=Q ∧
      (run bits model W k Q weights).1.classified=(GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1 ∧
      (run bits model W k Q weights).1.representatives=GeneralPaperLightFieldReduction.representatives k := by
  rw [data]
  unfold specification
  split_ifs <;> exact ⟨rfl,rfl,rfl,congrArg Prod.snd (GeneralPaperLightFieldClassification.data bits model W k Q weights)⟩

theorem count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    let classified := (GeneralPaperLightFieldClassification.run bits model W k Q weights).1
    (run bits model W k Q weights).1.m=classified.1.heavy.size+min classified.1.light.size classified.2 := by
  have hSizes : (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.heavy.size+
      (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.light.size=n := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScan.sizes bits model W _ Q weights n le_rfl
  dsimp only
  rw [data]
  unfold specification
  split_ifs with he
  · rw [Nat.min_eq_right he.le]
  · rw [Nat.min_eq_left (Nat.le_of_not_gt he)]
    exact hSizes.symm

theorem count_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    0<(run bits model W k Q weights).1.m ∧ (run bits model W k Q weights).1.m≤n ∧
      (run bits model W k Q weights).1.m<18*2^k := by
  rw [count]
  exact GeneralPaperLightFieldClassification.reduced_count_bounds bits model W k Q hQ weights hp hs

theorem positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    ∀ j,0<(run bits model W k Q weights).1.values.read j := by
  have hR : 0<(GeneralPaperLightFieldClassification.run bits model W k Q weights).1.2 := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldReduction.representatives_positive k
  change Positive (run bits model W k Q weights).1
  rw [data]
  unfold specification
  split_ifs with he
  · have hL := GeneralPaperLightFieldIntegerBalance.classified_light_positive bits model W k Q hQ weights hp hs (lt_trans hR he)
    simpa only [Positive,GeneralPaperReducedValueArray.replaced_data] using
      GeneralPaperReducedValueArray.replaced_positive bits model W Q _ _ hQ hR hL weights hp
        (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.heavy
  · simpa only [Positive,GeneralPaperReducedValueArray.identity_data] using
      GeneralPaperReducedValueArray.identity_positive bits model W Q hQ weights hp

theorem normalized {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hs : ∑ j,weights.read j=Q) :
    (∑ j,(run bits model W k Q weights).1.values.read j)=1 := by
  have hR : 0<(GeneralPaperLightFieldClassification.run bits model W k Q weights).1.2 := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldReduction.representatives_positive k
  have hBalance := GeneralPaperLightFieldIntegerBalance.classified bits model W k Q weights hs
  change Normalized (run bits model W k Q weights).1
  rw [data]
  unfold specification
  split_ifs
  · simpa only [Normalized,GeneralPaperReducedValueArray.replaced_data] using
      GeneralPaperReducedValueArray.replaced_sum bits model W Q _ _ hQ hR weights
        (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.heavy hBalance
  · simpa only [Normalized,GeneralPaperReducedValueArray.identity_data] using
      GeneralPaperReducedValueArray.identity_sum bits model W Q hQ weights hs

noncomputable def selector {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    RationalFieldSelector (run bits model W k Q weights).1.m where
  weight := (run bits model W k Q weights).1.values.read
  positive := positive bits model W k Q hQ weights hp hs
  sum_one := normalized bits model W k Q hQ weights hs

theorem models_data {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run true model W k Q weights).1=(run false model 1 k Q weights).1 := by
  rw [data,data,GeneralPaperLightFieldClassification.models_data]

end Blotto.GeneralPaperReducedValuesDriver

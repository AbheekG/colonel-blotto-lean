import Blotto.GeneralPaperSourceReferenceScaling

/-! Derive a logarithmic reference word from a proved closed storage profile.
The coefficient is an erased expression in existing source parameters and
literal primitive prices, not an observed runtime memory census. No growth
bound uniform over arbitrary rational-cost majorants is asserted. -/
namespace Blotto.GeneralPaperReferenceCapacity
open GeneralPaperReferenceScaling GeneralPaperCodeAlphabet
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def referenceWord (C : ℕ) : ℕ := 4*binaryWordWidth C

theorem positive (C : ℕ) : 1≤referenceWord C := by
  have h := binaryWordWidth_pos C
  unfold referenceWord
  omega

theorem product_capacity (C : ℕ) : referenceWord C*C<2^referenceWord C := by
  let n := binaryWordWidth C
  have hn : 1≤n := binaryWordWidth_pos C
  have hp : n≤2^n := (show n<2^n from Nat.lt_two_pow_self).le
  have hfour : 4≤2^(2*n) := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 2≤2*n by omega)
    simpa using h
  have hw : referenceWord C≤2^(3*n) := by
    change 4*n≤_
    calc
      4*n≤2^(2*n)*2^n := Nat.mul_le_mul hfour hp
      _=2^(3*n) := by rw [←pow_add]; congr 1; omega
  calc
    referenceWord C*C<referenceWord C*2^n :=
      Nat.mul_lt_mul_of_pos_left (lt_pow_binaryWordWidth C) (by have := positive C; omega)
    _≤2^(3*n)*2^n := Nat.mul_le_mul_right _ hw
    _=2^referenceWord C := by
      rw [←pow_add]
      congr 1
      dsimp only [referenceWord,n]
      omega

theorem profile_capacity (f : ℕ → ℕ) (hf : Scale f) :
    f (referenceWord (f 1))<2^referenceWord (f 1) :=
  (at_one f hf _ (positive _)).trans_lt (product_capacity _)

theorem padded_product_capacity (C extra : ℕ) :
    (referenceWord C+extra)*C<2^(referenceWord C+extra) := by
  have hp : extra+1≤2^extra := Nat.lt_two_pow_self
  have hw := positive C
  have hwidth : referenceWord C+extra≤referenceWord C*2^extra := by
    have h := Nat.mul_le_mul_left (referenceWord C) hp
    nlinarith only [h,hw]
  calc
    (referenceWord C+extra)*C≤(referenceWord C*2^extra)*C := Nat.mul_le_mul_right C hwidth
    _=(referenceWord C*C)*2^extra := by ring
    _<2^referenceWord C*2^extra := Nat.mul_lt_mul_of_pos_right (product_capacity C) (by positivity)
    _=2^(referenceWord C+extra) := (pow_add ..).symm

theorem padded_profile_capacity (f : ℕ → ℕ) (hf : Scale f) (extra : ℕ) :
    f (referenceWord (f 1)+extra)<2^(referenceWord (f 1)+extra) :=
  (at_one f hf _ (by have := positive (f 1); omega)).trans_lt (padded_product_capacity _ extra)

theorem address_word (f : ℕ → ℕ) (hf : Scale f) (address : ℕ)
    (h : address≤f (referenceWord (f 1))) :
    binaryWordWidth address≤referenceWord (f 1) :=
  binaryWordWidth_le_of_lt_pow (positive _) (h.trans_lt (profile_capacity f hf))

def sourceWord {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  referenceWord (GeneralPaperSourceLifetimeStorage.profile model 1 k Qv a weights Bc Br)

theorem source_capacity {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperSourceLifetimeStorage.profile model (sourceWord model k Qv a weights Bc Br) k Qv a weights Bc Br<
      2^sourceWord model k Qv a weights Bc Br :=
  profile_capacity _ (GeneralPaperSourceLifetimeStorage.reference_scale_profile model k Qv a weights Bc Br)

theorem native_source_capacity {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    GeneralPaperSourceLifetimeStorage.window model (sourceWord model k Qv a weights Bc Br) k Qv a c hc weights Bc Br count<
      2^sourceWord model k Qv a weights Bc Br :=
  (GeneralPaperSourceLifetimeStorage.bounded model _ k Qv a c hc weights Bc Br hw count he).trans_lt
    (source_capacity model k Qv a weights Bc Br)

end Blotto.GeneralPaperReferenceCapacity

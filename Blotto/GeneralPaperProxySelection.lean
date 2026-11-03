import Blotto.GeneralPaperProxyCellEndpoints

/-! The seven proxy-selection branches in the paper's displayed order.
The original budget is read only by comparisons with constructed rationals.
This module specifies the actual choices and their finite comparison cost;
root absence/presence and unit/denominator guarantees are joined separately.
-/
namespace Blotto.GeneralPaperProxySelection
open GeneralPaperBucketGeometry
set_option autoImplicit false

inductive Defender where
  | rich
  | poor
  deriving DecidableEq

structure Selected where
  proxy : Farey.Fraction
  modify : Option Defender
  endpoint : ℚ
  work : ℕ

noncomputable def select (Q j : ℕ) (hQ : 0<Q) (b : ℝ) (root : Option Farey.Fraction) : Selected :=
  if b=(lower Q j:ℝ) then ⟨⟨j,Q,hQ⟩,none,0,24⟩ else
  match root with
  | some f =>
      if b=(f.value:ℝ) then ⟨f,none,0,32⟩ else
      if b<(f.value:ℝ) then ⟨⟨j,Q,hQ⟩,some .rich,f.value,40⟩
      else ⟨⟨j+1,Q,hQ⟩,some .poor,f.value,40⟩
  | none =>
      if b=(GeneralPaperBucketGeometry.midpoint Q j:ℝ) then
        ⟨⟨2*j+1,2*Q,by omega⟩,none,0,40⟩ else
      if (GeneralPaperBucketGeometry.midpoint Q j:ℝ)<b then
        ⟨⟨2*j+1,2*Q,by omega⟩,some .rich,upper Q j,48⟩
      else ⟨⟨2*j+1,2*Q,by omega⟩,some .poor,lower Q j,48⟩

theorem selected_work (Q j : ℕ) (hQ : 0<Q) (b : ℝ) (root : Option Farey.Fraction) :
    (select Q j hQ b root).work≤48 := by
  unfold select
  split
  · norm_num
  · cases root <;> dsimp only <;> split_ifs <;> norm_num

theorem denominator_bound (H Q j : ℕ) (hQ : 0<Q) (hCap : H≤2*Q) (b : ℝ)
    (root : Option Farey.Fraction) (hRoot : ∀ f, root=some f → f.den≤H) :
    (select Q j hQ b root).proxy.den≤2*Q := by
  unfold select
  split
  · change Q≤2*Q; omega
  · cases hs : root with
    | none => dsimp only; split_ifs <;> exact le_rfl
    | some f =>
      have hf := (hRoot f hs).trans hCap
      dsimp only
      split_ifs
      · exact hf
      · change Q≤2*Q; omega
      · change Q≤2*Q; omega

theorem lower_value (Q j : ℕ) (hQ : 0<Q) : (⟨j,Q,hQ⟩:Farey.Fraction).value=lower Q j := rfl

theorem upper_value (Q j : ℕ) (hQ : 0<Q) : (⟨j+1,Q,hQ⟩:Farey.Fraction).value=upper Q j := by
  simp only [Farey.Fraction.value,upper,Nat.cast_add,Nat.cast_one]

theorem midpoint_value (Q j : ℕ) (hQ : 0<Q) :
    (⟨2*j+1,2*Q,by omega⟩:Farey.Fraction).value=GeneralPaperBucketGeometry.midpoint Q j := by
  simp only [Farey.Fraction.value,GeneralPaperBucketGeometry.midpoint,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

end Blotto.GeneralPaperProxySelection

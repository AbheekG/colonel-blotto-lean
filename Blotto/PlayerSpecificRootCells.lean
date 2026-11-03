import Blotto.PlayerSpecificRationalRootBound

/-! Every actual bisection leaf is an affine dyadic cell. After mapping
[-M,M] to [0,1], its midpoint is exactly the input of the already verified
continued-fraction bucket query. The cell index is recovered from data. -/
namespace Blotto.PlayerSpecificRootCells
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 5000000

def Cell (M k t : ℕ) (node : Interval) : Prop :=
  t<2^k ∧ node.lo=-(M:ℚ)+(2*(M:ℚ))*(t:ℚ)/(2:ℚ)^k ∧
    node.hi=-(M:ℚ)+(2*(M:ℚ))*((t:ℚ)+1)/(2:ℚ)^k

theorem initial_cell {p : Data} (prepared : Prepared p) (M : ℕ) :
    Cell M 0 0 (initial prepared (-(M:ℚ)) (M:ℚ)) := by
  constructor
  · decide
  · constructor <;> simp only [initial,pow_zero,Nat.cast_zero,mul_zero,div_one,zero_add,mul_one] <;> ring

theorem split_cells {p : Data} (prepared : Prepared p) (M k t : ℕ) (node : Interval) (h : Cell M k t node) :
    Cell M (k+1) (2*t) (split prepared node).1 ∧ Cell M (k+1) (2*t+1) (split prepared node).2 := by
  have ht:=h.1
  have hleft : 2*t<2^(k+1) := by rw [pow_succ]; omega
  have hright : 2*t+1<2^(k+1) := by rw [pow_succ]; omega
  have hpow : (2:ℚ)^k≠0 := pow_ne_zero _ (by norm_num)
  constructor
  · refine ⟨hleft,?_,?_⟩
    · change node.lo=_
      rw [h.2.1,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
    · change node.midpoint=_
      rw [Interval.midpoint,h.2.1,h.2.2,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
      ring
  · refine ⟨hright,?_,?_⟩
    · change node.midpoint=_
      rw [Interval.midpoint,h.2.1,h.2.2,pow_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      field_simp
      ring
    · change node.hi=_
      rw [h.2.2,pow_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      field_simp
      ring

theorem forest_cells {p : Data} (prepared : Prepared p) (M fuel : ℕ) (node : Interval) (k t : ℕ)
    (h : Cell M k t node) : ∀ leaf∈PlayerSpecificIsolationForest.run prepared fuel node,∃ u,Cell M (k+fuel) u leaf := by
  induction fuel generalizing node k t with
  | zero =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hm; cases hm
    · intro leaf hm
      have he:=List.mem_singleton.mp hm
      subst leaf
      exact ⟨t,by simpa only [Nat.add_zero] using h⟩
  | succ fuel ih =>
    rw [PlayerSpecificIsolationForest.run]
    split
    · intro leaf hm; cases hm
    · intro leaf hm
      have hs:=split_cells prepared M k t node h
      rcases List.mem_append.mp hm with hl | hr
      · obtain ⟨u,hu⟩:=ih (split prepared node).1 (k+1) (2*t) hs.1 leaf hl
        exact ⟨u,by simpa only [show k+1+fuel=k+(fuel+1) by omega] using hu⟩
      · obtain ⟨u,hu⟩:=ih (split prepared node).2 (k+1) (2*t+1) hs.2 leaf hr
        exact ⟨u,by simpa only [show k+1+fuel=k+(fuel+1) by omega] using hu⟩

def normalized (M : ℕ) (x : ℚ) : ℚ := (x+(M:ℚ))/(2*(M:ℚ))

theorem normalized_cell (M k t : ℕ) (node : Interval) (hM : 0<M) (h : Cell M k t node) :
    normalized M node.lo=(t:ℚ)/(2:ℚ)^k ∧ normalized M node.hi=((t:ℚ)+1)/(2:ℚ)^k := by
  have hMq : (M:ℚ)≠0 := by exact_mod_cast hM.ne'
  have hpow : (2:ℚ)^k≠0 := pow_ne_zero _ (by norm_num)
  rw [normalized,normalized,h.2.1,h.2.2]
  constructor <;> field_simp <;> ring

def index (M C : ℕ) (node : Interval) : ℕ :=
  let located:ℚ:=(C:ℚ)*normalized M node.lo
  located.num.toNat/located.den

theorem index_value (M k t : ℕ) (node : Interval) (hM : 0<M) (h : Cell M k t node) : index M (2^k) node=t := by
  have hloc : ((2^k:ℕ):ℚ)*normalized M node.lo=(t:ℚ) := by
    rw [(normalized_cell M k t node hM h).1,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  unfold index
  rw [hloc]
  simp only [Rat.num_natCast,Rat.den_natCast,Int.toNat_natCast,Nat.div_one]

end Blotto.PlayerSpecificRootCells

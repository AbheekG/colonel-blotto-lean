import Blotto.GeneralPaperBasisAdvanceSize

/-! Common-lattice magnitude bounds keep rational sums short independently
of the number of additions. These proof-only bounds concern the actual
reduced operands; no lattice conversion is inserted into the program.
-/
namespace Blotto.GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Bounded (D M : ℕ) (q : ℚ) : Prop where
  lattice : OnRationalLattice D q
  magnitude : |q|≤(M:ℚ)

namespace Bounded

theorem zero (D : ℕ) : Bounded D 0 0 := ⟨OnRationalLattice.zero D,by norm_num⟩

theorem mono {D M U : ℕ} {q : ℚ} (h : Bounded D M q) (hM : M≤U) : Bounded D U q :=
  ⟨h.lattice,h.magnitude.trans (by exact_mod_cast hM)⟩

theorem enlarge {D E M : ℕ} {q : ℚ} (h : Bounded D M q) (hD : D∣E) : Bounded E M q :=
  ⟨h.lattice.enlarge hD,h.magnitude⟩

theorem neg {D M : ℕ} {q : ℚ} (h : Bounded D M q) : Bounded D M (-q) :=
  ⟨by simpa only [zero_sub] using (OnRationalLattice.zero D).sub h.lattice,
    by simpa only [abs_neg] using h.magnitude⟩

theorem add {D M U : ℕ} {q r : ℚ} (hq : Bounded D M q) (hr : Bounded D U r) : Bounded D (M+U) (q+r) :=
  ⟨hq.lattice.add hr.lattice,by
    rw [Nat.cast_add]
    exact (abs_add_le q r).trans (add_le_add hq.magnitude hr.magnitude)⟩

theorem sub {D M U : ℕ} {q r : ℚ} (hq : Bounded D M q) (hr : Bounded D U r) : Bounded D (M+U) (q-r) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem int_mul {D M : ℕ} {q : ℚ} (hq : Bounded D M q) (c : ℤ) : Bounded D (c.natAbs*M) ((c:ℚ)*q) := by
  refine ⟨hq.lattice.int_mul c,?_⟩
  have hc : |(c:ℚ)|=(c.natAbs:ℚ) := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [abs_mul,hc,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hq.magnitude (by positivity)

theorem intCast (D : ℕ) (c : ℤ) : Bounded D c.natAbs (c:ℚ) :=
  ⟨OnRationalLattice.intCast D c,by rw [Nat.cast_natAbs,Int.cast_abs]⟩

theorem mul {D E M U : ℕ} {q r : ℚ} (hq : Bounded D M q) (hr : Bounded E U r) : Bounded (D*E) (M*U) (q*r) := by
  refine ⟨hq.lattice.mul hr.lattice,?_⟩
  rw [abs_mul,Nat.cast_mul]
  exact mul_le_mul hq.magnitude hr.magnitude (abs_nonneg r) (by positivity)

theorem list_sum {i : Type*} (D M : ℕ) (f : i → ℚ) (xs : List i)
    (h : ∀ x∈xs,Bounded D M (f x)) : Bounded D (xs.length*M) ((xs.map f).sum) := by
  induction xs with
  | nil => simpa only [List.length_nil,Nat.zero_mul,List.map_nil,List.sum_nil] using zero D
  | cons x rest ih =>
    have hh := (h x List.mem_cons_self).add (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))
    have he : M+rest.length*M=(rest.length+1)*M := by ring
    simpa only [List.length_cons,List.map_cons,List.sum_cons,he] using hh

theorem height {D M : ℕ} {q : ℚ} (hD : 0<D) (h : Bounded D M q) :
    RationalHeight q (binaryWordWidth (M+1)+binaryWordWidth D) := by
  have hn := rationalLattice_abs_numerator_le hD h.lattice h.magnitude
  have hd := rationalLattice_den_le hD h.lattice
  have hn' : q.num.natAbs≤(M+1)*D := hn.trans (Nat.mul_le_mul_right D (by omega))
  have hd' : q.den≤(M+1)*D := hd.trans (by nlinarith)
  have hh : RationalHeight q (binaryWordWidth ((M+1)*D)) :=
    ⟨hn'.trans_lt (lt_pow_binaryWordWidth _),hd'.trans_lt (lt_pow_binaryWordWidth _)⟩
  exact hh.mono (binaryWordWidth_mul _ _)

theorem fin_sum {n : ℕ} (D M : ℕ) (f : Fin n → ℚ) (h : ∀ i,Bounded D M (f i)) :
    Bounded D (n*M) (∑ i,f i) := by
  have hh := list_sum D M f (List.finRange n) (fun i _ => h i)
  simpa only [←List.ofFn_eq_map,List.sum_ofFn,List.length_finRange] using hh

end Bounded

theorem abs_int_fraction (a b : ℤ) (hb : b≠0) (M : ℕ) (ha : a.natAbs≤M) :
    |(a:ℚ)/(b:ℚ)|≤(M:ℚ) := by
  have hbPos : (0:ℚ)<(b.natAbs:ℚ) := by exact_mod_cast Int.natAbs_pos.mpr hb
  have hbOne : (1:ℚ)≤(b.natAbs:ℚ) := by exact_mod_cast Int.natAbs_pos.mpr hb
  have haAbs : |(a:ℚ)|=(a.natAbs:ℚ) := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hbAbs : |(b:ℚ)|=(b.natAbs:ℚ) := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [abs_div,haAbs,hbAbs]
  apply (div_le_iff₀ hbPos).mpr
  have hn : (a.natAbs:ℚ)≤(M:ℚ) := by exact_mod_cast ha
  exact hn.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hbOne (show (0:ℚ)≤M by positivity))

end Blotto.GeneralPaperRayRationalBound

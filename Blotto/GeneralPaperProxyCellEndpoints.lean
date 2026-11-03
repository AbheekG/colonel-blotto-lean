import Blotto.GeneralPaperProxyQuotient

/-! Boundary facts for the proxy classifier. The closed root query includes
zero and one: uniqueness prevents choosing either as a proxy on a branch
that moves toward a different small-denominator root.
-/
namespace Blotto.GeneralPaperProxyCellEndpoints
open GeneralPaperBucketGeometry GeneralPaperProxyCell
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem zero_closed (Q : ℕ) : Closed Q 0 (0:ℚ) := by
  constructor
  · simp only [lower,Nat.cast_zero,zero_div,le_refl]
  · unfold upper
    positivity

theorem one_closed (Q j : ℕ) (hj : j+1=Q) : Closed Q j (1:ℚ) := by
  have hQ : (0:ℚ)<Q := by exact_mod_cast (show 0<Q by omega)
  constructor
  · unfold lower
    apply (div_le_one hQ).mpr
    exact_mod_cast (show j≤Q by omega)
  · unfold upper
    have he : (j:ℚ)+1=(Q:ℚ) := by exact_mod_cast hj
    rw [he,div_self hQ.ne']

theorem lower_positive_from_root (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (f : Farey.Fraction) (hf : f.den≤H) (hc : Closed Q j f.value) (hb : (0:ℚ)<f.value) : 0<j := by
  by_contra hn
  have hj : j=0 := by omega
  subst j
  have he := closed_equal H Q 0 hH hScale f ⟨0,1,by decide⟩ hf (by change 1≤H; omega) hc (by simpa only [Farey.Fraction.value,Nat.cast_zero,zero_div] using zero_closed Q)
  have hz : (⟨0,1,by decide⟩:Farey.Fraction).value=0 := by norm_num [Farey.Fraction.value]
  rw [hz] at he
  linarith

theorem upper_strict_from_root (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q) (hj : j<Q)
    (f : Farey.Fraction) (hf : f.den≤H) (hc : Closed Q j f.value) (hb : f.value<1) : j+1<Q := by
  by_contra hn
  have hjOne : j+1=Q := by omega
  have he := closed_equal H Q j hH hScale f ⟨1,1,by decide⟩ hf (by change 1≤H; omega) hc (by simpa only [Farey.Fraction.value,Nat.cast_one,div_one] using one_closed Q j hjOne)
  have ho : (⟨1,1,by decide⟩:Farey.Fraction).value=1 := by norm_num [Farey.Fraction.value]
  rw [ho] at he
  linarith

theorem no_root_endpoints (H Q j : ℕ) (hH : 0<H) (hj : j<Q)
    (he : ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value) : 0<j ∧ j+1<Q := by
  constructor
  · by_contra hn
    have hz : j=0 := by omega
    subst j
    exact he ⟨0,1,by decide⟩ (by change 1≤H; omega) (by simpa only [Farey.Fraction.value,Nat.cast_zero,zero_div] using zero_closed Q)
  · by_contra hn
    have ho : j+1=Q := by omega
    exact he ⟨1,1,by decide⟩ (by change 1≤H; omega) (by simpa only [Farey.Fraction.value,Nat.cast_one,div_one] using one_closed Q j ho)

end Blotto.GeneralPaperProxyCellEndpoints

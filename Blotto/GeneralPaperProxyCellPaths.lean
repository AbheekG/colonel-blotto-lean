import Blotto.GeneralPaperProxyBranchSpec

/-! Rational root-free intervals inside the closed classifier cell.
Endpoint roots are allowed; the open path contains no small-denominator
rational. Fractions are reduced only for proofs, never by enumeration.
-/
namespace Blotto.GeneralPaperProxyCellPaths
open GeneralPaperBucketGeometry GeneralPaperProxyCell
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Between (a b x : ℚ) : Prop := (a<x ∧ x<b) ∨ (b<x ∧ x<a)

theorem endpoints_closed (Q j : ℕ) (hQ : 0<Q) : Closed Q j (lower Q j) ∧ Closed Q j (upper Q j) := by
  have hw := width Q j hQ
  have hp : (0:ℚ)<1/(Q:ℚ) := by positivity
  exact ⟨⟨le_rfl,by linarith⟩,⟨by linarith,le_rfl⟩⟩

theorem midpoint_closed (Q j : ℕ) (hQ : 0<Q) : Closed Q j (GeneralPaperBucketGeometry.midpoint Q j) := by
  have hl := midpoint_left Q j hQ
  have hr := midpoint_right Q j hQ
  have hp : (0:ℚ)<1/(2*(Q:ℚ)) := by positivity
  exact ⟨by linarith,by linarith⟩

theorem between_closed (Q j : ℕ) (a b x : ℚ) (ha : Closed Q j a) (hb : Closed Q j b)
    (hx : Between a b x) : Closed Q j x := by
  rcases hx with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact ⟨ha.1.trans h1.le,h2.le.trans hb.2⟩
  · exact ⟨hb.1.trans h1.le,h2.le.trans ha.2⟩

theorem rat_unique (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (x : ℚ) (hx : x.den≤H) (hc : Closed Q j x)
    (f : Farey.Fraction) (hf : f.den≤H) (hfc : Closed Q j f.value) : x=f.value := by
  have hn : 0≤x := (by unfold lower; positivity : (0:ℚ)≤lower Q j).trans hc.1
  have he := closed_equal H Q j hH hScale (Farey.fractionOfRat x) f hx hf
    (by rw [Farey.fractionOfRat_value x hn]; exact hc) hfc
  rwa [Farey.fractionOfRat_value x hn] at he

theorem large_if_distinct (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (x : ℚ) (hc : Closed Q j x) (f : Farey.Fraction) (hf : f.den≤H)
    (hfc : Closed Q j f.value) (hne : x≠f.value) : H<x.den := by
  by_contra hn
  exact hne (rat_unique H Q j hH hScale x (by omega) hc f hf hfc)

theorem empty_excludes (H Q j : ℕ)
    (he : ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value)
    (x : ℚ) (hx : x.den≤H) (hc : Closed Q j x) : False := by
  have hn : 0≤x := (by unfold lower; positivity : (0:ℚ)≤lower Q j).trans hc.1
  exact he (Farey.fractionOfRat x) hx (by rw [Farey.fractionOfRat_value x hn]; exact hc)

theorem empty_large (H Q j : ℕ)
    (he : ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value)
    (x : ℚ) (hc : Closed Q j x) : H<x.den := by
  by_contra hn
  exact empty_excludes H Q j he x (by omega) hc

theorem path_to_unique_root (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (a : ℚ) (ha : Closed Q j a) (f : Farey.Fraction) (hf : f.den≤H) (hc : Closed Q j f.value)
    (x : ℚ) (hx : x.den≤H) : ¬Between a f.value x := by
  intro hb
  have he := rat_unique H Q j hH hScale x hx (between_closed Q j a f.value x ha hc hb) f hf hc
  rcases hb with ⟨h1,h2⟩|⟨h1,h2⟩ <;> rw [he] at * <;> exact (lt_irrefl _ (by assumption)).elim

theorem empty_path (H Q j : ℕ)
    (he : ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value)
    (a b : ℚ) (ha : Closed Q j a) (hb : Closed Q j b) (x : ℚ) (hx : x.den≤H) : ¬Between a b x := by
  intro hp
  exact empty_excludes H Q j he x hx (between_closed Q j a b x ha hb hp)

end Blotto.GeneralPaperProxyCellPaths

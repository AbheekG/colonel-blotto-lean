import Blotto.GeneralPaperProxyCell

/-! Actual last-bounded-convergent query with inclusive cell tests for the
proxy classifier. It reuses the executed arithmetic CF loop, not the strict
source-bucket acceptance predicate. Completeness, emptiness and linear
arithmetic work include possible roots at either endpoint.
-/
namespace Blotto.GeneralPaperProxyRootQuery
open GeneralPaperBucketGeometry GeneralPaperProxyCell
open GeneralPaperMidpointQuery GeneralPaperMidpointComplete
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lookup (H Q j lambda : ℕ) : GeneralPaperMidpointQuery.Result :=
  let finished := raw H Q j lambda
  let checked := finished.selected.bind (fun f => if lower Q j≤f.value ∧ f.value≤upper Q j then some f else none)
  ⟨checked,finished.work+32,finished.steps,finished.quotientDepth⟩

theorem sound (H Q j lambda : ℕ) (f : Farey.Fraction) (h : (lookup H Q j lambda).fraction=some f) :
    f.den≤H ∧ Closed Q j f.value := by
  have hb := raw_bounded H Q j lambda
  dsimp only [lookup] at h
  cases hs : (raw H Q j lambda).selected with
  | none => simp only [hs,Option.bind_none,reduceCtorEq] at h
  | some g =>
    simp only [hs,Option.bind_some] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      subst f
      exact ⟨hb g hs,hc⟩
    · cases h

theorem complete (H Q j lambda : ℕ) (hH : 0<H) (hQ : 0<Q) (hj : j<Q)
    (hScale : 4*H*H≤Q) (hPower : 8*Q=2^lambda)
    (f : Farey.Fraction) (hf : f.den≤H) (hc : Closed Q j f.value) :
    ∃ g, (lookup H Q j lambda).fraction=some g ∧ g.value=f.value := by
  obtain ⟨k,hk⟩ := GeneralPaperProxyCell.regular_convergent H Q j hH hScale f hf hc
  have hm : (GeneralPaperBucketGeometry.midpoint Q j:ℝ)=(((2*j+1:ℕ):ℝ)/((2*Q:ℕ):ℝ)) := by
    simp only [GeneralPaperBucketGeometry.midpoint,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,
      Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  rw [hm] at hk
  have hd : (Real.convergent (((2*j+1:ℕ):ℝ)/((2*Q:ℕ):ℝ)) k).den≤H := by
    rw [←hk]
    exact (Farey.value_den_le f).trans hf
  obtain ⟨g,hg,hError⟩ := bounded_convergent_dominance H Q j lambda hH hQ hj hPower k hd
  rw [←hk,midpoint_error,midpoint_error] at hError
  have hgClosed := closed_of_distance Q j hQ g.value (hError.trans (distance_closed Q j hQ f.value hc))
  have hgBound := raw_bounded H Q j lambda g hg
  refine ⟨g,?_,closed_equal H Q j hH hScale g f hgBound hf hgClosed hc⟩
  dsimp only [lookup]
  rw [hg]
  simp only [Option.bind_some]
  exact ite_eq_left hgClosed

theorem none_iff (H Q j lambda : ℕ) (hH : 0<H) (hQ : 0<Q) (hj : j<Q)
    (hScale : 4*H*H≤Q) (hPower : 8*Q=2^lambda) :
    (lookup H Q j lambda).fraction=none ↔ ∀ f : Farey.Fraction, f.den≤H → ¬Closed Q j f.value := by
  constructor
  · intro hn f hf hc
    obtain ⟨g,hg,_⟩ := complete H Q j lambda hH hQ hj hScale hPower f hf hc
    rw [hn] at hg
    cases hg
  · intro he
    cases hs : (lookup H Q j lambda).fraction with
    | none => rfl
    | some f =>
      have hf := sound H Q j lambda f hs
      exact (he f hf.1 hf.2).elim

theorem real_work (H Q j lambda : ℕ) (hH : 0<H) (hQ : 0<Q) (hj : j<Q) (hPower : 8*Q=2^lambda) :
    (lookup H Q j lambda).work≤170*lambda+370 :=
  GeneralPaperMidpointRealWork.lookup_real_work H Q j lambda hH hQ hj hPower

end Blotto.GeneralPaperProxyRootQuery

import Blotto.PlayerSpecificAlgebraicResourceState

/-! A reached pair is computed once and retained in its request frame.
Choosing either branch uses that cached pair and tests only its two
selected coordinates; the untouched active tail is reused. -/
namespace Blotto.PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Frame (N : ℕ) where
  first : Fin N
  second : Fin N
  tail : List (Fin N)
  pair : PlayerSpecificAlgebraicPairStep.Result

def request {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) : Option (Frame N) :=
  match s.active with
  | [] => none
  | [_] => none
  | i::j::tail => some ⟨i,j,tail,PlayerSpecificAlgebraicPairStep.run model p.parameters.root
      (p.rows.read i).length (p.rows.read j).length (s.data.read i) (s.data.read j)⟩

def advance {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (f : Frame N) (upper : Bool) : State N :=
  update model p s f.first f.second f.tail (if upper then f.pair.upperA else f.pair.lowerA)
    (if upper then f.pair.upperB else f.pair.lowerB)

theorem fields {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) :
    s.active=f.first::f.second::f.tail ∧ f.pair=PlayerSpecificAlgebraicPairStep.run model p.parameters.root
      (p.rows.read f.first).length (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) := by
  unfold request at hf
  split at hf
  · cases hf
  · cases hf
  · rename_i i j tail h
    have he:=Option.some.inj hf
    subst f
    exact ⟨h,rfl⟩

theorem none_iff {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) :
    request model p s=none ↔ s.active.length≤1 := by
  unfold request
  split <;> simp_all

theorem distinct {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (x : ℝ) (hs : Valid p x s) : f.first≠f.second :=
  (interpret p x s hs).selected_distinct (fields model p s f hf).1

theorem fractional {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (x : ℝ) (hs : Valid p x s) :
    Fractional (lengths p x) (eval s x) f.first ∧ Fractional (lengths p x) (eval s x) f.second :=
  (interpret p x s hs).selected_fractional (fields model p s f hf).1

theorem advance_eval {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (hij : f.first≠f.second) (upper : Bool)
    (x : ℝ) (hx : realEvaluate p.parameters.root.polynomial x=0) :
    eval (advance model p s f upper) x=Blotto.updatePair (eval s x) f.first f.second
      (realEvaluate (if upper then f.pair.upperA else f.pair.lowerA) x) := by
  have hp:=(fields model p s f hf).2
  have hu:=PlayerSpecificAlgebraicPairValues.upper_other model p.parameters.root (p.rows.read f.first).length
    (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) x hx
  have hl:=PlayerSpecificAlgebraicPairValues.lower_other model p.parameters.root (p.rows.read f.first).length
    (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) x hx
  have hb : realEvaluate (if upper then f.pair.upperB else f.pair.lowerB) x=
      eval s x f.first+eval s x f.second-realEvaluate (if upper then f.pair.upperA else f.pair.lowerA) x := by
    cases upper
    · simpa only [Bool.false_eq_true,ite_false,hp,eval] using hl
    · simpa only [ite_true,hp,eval] using hu
  exact eval_update model p s f.first f.second f.tail _ _ hij x hb

noncomputable def realPair {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (x : ℝ) (hs : Valid p x s) : RoundingPair :=
  resourcePair (lengths p x) (eval s x) f.first f.second (fractional model p s f hf x hs).1 (fractional model p s f hf x hs).2

theorem chosen_endpoint {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x) (hs : Valid p x s) :
    realEvaluate (if upper then f.pair.upperA else f.pair.lowerA) x=(realPair model p s f hf x hs).lower ∨
      realEvaluate (if upper then f.pair.upperA else f.pair.lowerA) x=(realPair model p s f hf x hs).upper := by
  have hp:=(fields model p s f hf).2
  cases upper
  · have hl:=PlayerSpecificAlgebraicPairValues.lower model p.parameters.root (p.rows.read f.first).length
      (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) hm hirr hv x hx
    exact Or.inl (by simpa only [Bool.false_eq_true,ite_false,hp,realPair,resourcePair,RoundingPair.lower,RoundingPair.total,lengths,eval] using hl)
  · have hu:=PlayerSpecificAlgebraicPairValues.upper model p.parameters.root (p.rows.read f.first).length
      (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) hm hirr hv x hx
    exact Or.inr (by simpa only [ite_true,hp,realPair,resourcePair,RoundingPair.upper,RoundingPair.total,lengths,eval] using hu)

theorem probability {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x) (hs : Valid p x s) :
    realEvaluate f.pair.probability x=(realPair model p s f hf x hs).probability := by
  have hp:=(fields model p s f hf).2
  have hfrac:=fractional model p s f hf x hs
  have h:=PlayerSpecificAlgebraicPairContract.refinement model p.parameters.root (p.rows.read f.first).length
    (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) hm hirr hv x hx hfrac.1 hfrac.2
  simpa only [hp,realPair,resourcePair,PlayerSpecificAlgebraicPairContract.point,lengths,eval] using h.2.2.2.2

end Blotto.PlayerSpecificAlgebraicResourceRequest

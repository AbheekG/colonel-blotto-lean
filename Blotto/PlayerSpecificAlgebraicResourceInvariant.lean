import Blotto.PlayerSpecificAlgebraicResourceUpdate

/-! Every reached branch preserves the actual array/list invariants,
the resource box and total. Its active length strictly decreases; no
randomness or height oracle is used in these transition guarantees. -/
namespace Blotto.PlayerSpecificAlgebraicResourceInvariant
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def PairReduced (m : Data) (pair : PlayerSpecificAlgebraicPairStep.Result) : Prop :=
  Reduced m pair.total ∧ Reduced m pair.upperA ∧ Reduced m pair.upperB ∧ Reduced m pair.lowerA ∧
    Reduced m pair.lowerB ∧ Reduced m pair.probability

theorem chosen_reduced {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hL : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length) :
    Reduced p.parameters.root.polynomial (if upper then f.pair.upperA else f.pair.lowerA) ∧
      Reduced p.parameters.root.polynomial (if upper then f.pair.upperB else f.pair.lowerB) := by
  have hp:=(fields model p s f hf).2
  have hraw : PairReduced p.parameters.root.polynomial (PlayerSpecificAlgebraicPairStep.run model p.parameters.root
      (p.rows.read f.first).length (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second)) :=
    PlayerSpecificAlgebraicPairStep.reduced model p.parameters.root _ _ _ _ hm hm0 (hL f.first) (hL f.second)
  have hframe : PairReduced p.parameters.root.polynomial f.pair := hp.symm ▸ hraw
  cases upper
  · exact ⟨hframe.2.2.2.1,hframe.2.2.2.2.1⟩
  · exact ⟨hframe.2.1,hframe.2.2.1⟩

theorem advance_valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x)
    (hs : Valid p x s) (hL : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length) :
    Valid p x (advance model p s f upper) := by
  have hm0 : p.parameters.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hrows:=chosen_reduced model p s f hf upper hm hm0 hL
  exact PlayerSpecificAlgebraicResourceUpdate.valid model p s f.first f.second f.tail _ _ (fields model p s f hf).1
    hm hirr hv x hx hs hrows.1 hrows.2

theorem active_sublist {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool) :
    (advance model p s f upper).active.Sublist s.active := by
  have he:=(fields model p s f hf).1
  change (([f.first,f.second].filter (fun k => PlayerSpecificAlgebraicActive.run model p.parameters.root (p.rows.read k).length
    (((s.data.write f.first (if upper then f.pair.upperA else f.pair.lowerA)).write f.second
      (if upper then f.pair.upperB else f.pair.lowerB)).read k)))++f.tail).Sublist s.active
  rw [he]
  exact List.filter_sublist.append (List.Sublist.refl f.tail)

theorem box_sum {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x)
    (hs : Valid p x s) (hbox : InBox (lengths p x) (eval s x)) :
    InBox (lengths p x) (eval (advance model p s f upper) x) ∧
      (∑ j,eval (advance model p s f upper) x j)=(∑ j,eval s x j) := by
  have hij:=distinct model p s f hf x hs
  have hfrac:=fractional model p s f hf x hs
  have hz:=chosen_endpoint model p s f hf upper hm hirr hv x hx hs
  have he:=advance_eval model p s f hf hij upper x hx.1
  have hb:=updatePair_inBox hij hbox hfrac.1 hfrac.2 hz
  refine ⟨he.symm ▸ hb,?_⟩
  exact (congrArg (fun resource : Allocation N => ∑ j,resource j) he).trans
    (updatePair_sum (eval s x) hij _)

theorem active_decreases {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x)
    (hs : Valid p x s) (hnew : Valid p x (advance model p s f upper)) :
    (advance model p s f upper).active.length<s.active.length := by
  have hij:=distinct model p s f hf x hs
  have hfrac:=fractional model p s f hf x hs
  have hz:=chosen_endpoint model p s f hf upper hm hirr hv x hx hs
  have he:=advance_eval model p s f hf hij upper x hx.1
  have hd:=updatePair_fractional_decreases hij hfrac.1 hfrac.2 hz
  have hc:=(congrArg (fun resource : Allocation N => (fractionalSet (lengths p x) resource).card) he).trans_lt hd
  exact (length_eq_card p x (advance model p s f upper) hnew).trans_lt
    (hc.trans_eq (length_eq_card p x s hs).symm)

end Blotto.PlayerSpecificAlgebraicResourceInvariant

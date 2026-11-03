import Blotto.PlayerSpecificAlgebraicResourceInvariant

/-! A finite path through the actual cached-pair program. The branch list
is explicit finite data. These pathwise guarantees hold for every list;
they do not assert a distribution for the choices. -/
namespace Blotto.PlayerSpecificAlgebraicResourceLoop
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Context {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) : Prop where
  normalized : Normalized p.parameters.root.polynomial
  irreducible : Irreducible (semantics p.parameters.root.polynomial)
  interval : p.parameters.root.interval.lo<p.parameters.root.interval.hi
  root : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x
  lengths : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) :
    ℕ → State N → List Bool → State N × ℕ
  | 0,s,_ => (s,0)
  | fuel+1,s,choices =>
      match request model p s with
      | none => (s,0)
      | some f =>
          let next:=advance model p s f (choices.headD false)
          let result:=run model p fuel next choices.tail
          (result.1,result.2+1)

theorem stop {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (fuel : ℕ) (s : State N) (choices : List Bool) (h : request model p s=none) :
    run model p fuel s choices=(s,0) := by
  cases fuel <;> simp only [run,h]

theorem guarantees {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : Context p x) (fuel : ℕ) (s : State N) (choices : List Bool)
    (hs : Valid p x s) (hb : InBox (lengths p x) (eval s x)) :
    Valid p x (run model p fuel s choices).1 ∧
      InBox (lengths p x) (eval (run model p fuel s choices).1 x) ∧
      (∑ j,eval (run model p fuel s choices).1 x j)=(∑ j,eval s x j) ∧
      (run model p fuel s choices).2≤fuel ∧
      (s.active.length≤fuel+1 → (run model p fuel s choices).1.active.length≤1) := by
  induction fuel generalizing s choices with
  | zero => exact ⟨hs,hb,rfl,Nat.le_refl 0,fun h => h⟩
  | succ fuel ih =>
      cases he : request model p s with
      | none =>
          rw [stop model p (fuel+1) s choices he]
          exact ⟨hs,hb,rfl,Nat.zero_le _,fun _ => (none_iff model p s).mp he⟩
      | some f =>
          let next:=advance model p s f (choices.headD false)
          have hn : Valid p x next := PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s f he _
            hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths
          have hbs:=PlayerSpecificAlgebraicResourceInvariant.box_sum model p s f he (choices.headD false)
            hc.normalized hc.irreducible hc.interval x hc.root hs hb
          have hd : next.active.length<s.active.length := PlayerSpecificAlgebraicResourceInvariant.active_decreases
            model p s f he _ hc.normalized hc.irreducible hc.interval x hc.root hs hn
          have ht:=ih next choices.tail hn hbs.1
          simp only [run,he]
          refine ⟨ht.1,ht.2.1,ht.2.2.1.trans hbs.2,?_,?_⟩
          · exact Nat.add_le_add_right ht.2.2.2.1 1
          · intro h
            exact ht.2.2.2.2 (by omega)

theorem start_length {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (firstPlayer : Bool) : (start model p firstPlayer).active.length≤N := by
  exact (List.length_filter_le _ _).trans (by rw [List.length_finRange])

theorem complete_path {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (x : ℝ) (hc : Context p x) (firstPlayer : Bool) (choices : List Bool)
    (hr : ∀ j,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p firstPlayer j))
    (hb : InBox (lengths p x) (eval (start model p firstPlayer) x)) :
    let result:=run model p (N-1) (start model p firstPlayer) choices
    Valid p x result.1 ∧ InBox (lengths p x) (eval result.1 x) ∧
      (∑ j,eval result.1 x j)=(∑ j,eval (start model p firstPlayer) x j) ∧
      result.2≤N-1 ∧ result.1.active.length≤1 := by
  have hs:=start_valid model p firstPlayer hc.normalized hc.irreducible hc.interval x hc.root hr
  have ht:=guarantees model p x hc (N-1) (start model p firstPlayer) choices hs hb
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2 ?_⟩
  have hl:=start_length model p firstPlayer
  omega

end Blotto.PlayerSpecificAlgebraicResourceLoop

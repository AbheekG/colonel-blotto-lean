import Blotto.PlayerSpecificAlgebraicLoopLineage

/-! Uniform heights of all live and frozen resource rows along every
finite executing path. Probabilities never enter subsequent resource rows. -/
namespace Blotto.PlayerSpecificAlgebraicLoopHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificAlgebraicResourceLoop PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def activeHeight (N H : ℕ) : ℕ := (H+1)*(N+N)+3
def storedHeight (N H : ℕ) : ℕ := PlayerSpecificAlgebraicPairHeights.resourceHeight (activeHeight N H)

theorem leaf_le_active (N H : ℕ) (hN : 0<N) : H≤activeHeight N H := by
  unfold activeHeight
  have h:=Nat.mul_le_mul_left (H+1) (show 1≤N+N by omega)
  omega

theorem advance_heights {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) (x : ℝ) (hc : Context p x) (s : State N) (hs : Valid p x s) (c : Certificate p player s)
    (f : Frame N) (hf : request model p s=some f) (upper : Bool) (H : ℕ)
    (hv : ∀ k,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player k) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player k) H)
    (hL : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length ∧ HasHeight (p.rows.read k).length H)
    (hall : ∀ k,HasHeight (s.data.read k) (storedHeight N H)) :
    ∀ k,HasHeight ((advance model p s f upper).data.read k) (storedHeight N H) := by
  have hij:=distinct model p s f hf x hs
  have he:=(fields model p s f hf).1
  have hi : f.first∈s.active := he ▸ List.mem_cons_self
  have hj : f.second∈s.active := he ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have hm0 : p.parameters.root.polynomial≠[] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have ha:=PlayerSpecificAlgebraicLoopLineage.active_height p player s c hc.normalized hm0 hs.reduced H hv hL f.first hi
  have hb:=PlayerSpecificAlgebraicLoopLineage.active_height p player s c hc.normalized hm0 hs.reduced H hv hL f.second hj
  have hH:=leaf_le_active N H (by have h:=f.first.isLt; omega)
  have hp:=PlayerSpecificAlgebraicPairHeights.resources model p.parameters.root (p.rows.read f.first).length
    (p.rows.read f.second).length (s.data.read f.first) (s.data.read f.second) hc.normalized hm0
    (hL f.first).1 (hL f.second).1 (hs.reduced f.first) (hs.reduced f.second) (activeHeight N H)
    (mono (hL f.first).2 hH) (mono (hL f.second).2 hH) ha hb
  have hpair:=(fields model p s f hf).2
  have hchosen : HasHeight (if upper then f.pair.upperA else f.pair.lowerA) (storedHeight N H) ∧
      HasHeight (if upper then f.pair.upperB else f.pair.lowerB) (storedHeight N H) := by
    cases upper
    · simpa only [Bool.false_eq_true,ite_false,hpair] using ⟨hp.2.2.2.1,hp.2.2.2.2⟩
    · simpa only [ite_true,hpair] using ⟨hp.2.1,hp.2.2.1⟩
  intro k
  by_cases hki : k=f.first
  · subst k
    rw [PlayerSpecificAlgebraicResourceShape.read_first model p s f upper hij]
    exact hchosen.1
  · by_cases hkj : k=f.second
    · subst k
      rw [PlayerSpecificAlgebraicResourceShape.read_second model p s f upper]
      exact hchosen.2
    · rw [PlayerSpecificAlgebraicResourceShape.read_other model p s f upper k hki hkj]
      exact hall k

theorem run_heights {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) (x : ℝ) (hc : Context p x) (fuel : ℕ) (s : State N) (choices : List Bool)
    (hs : Valid p x s) (c : Certificate p player s) (H : ℕ)
    (hv : ∀ k,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player k) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player k) H)
    (hL : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length ∧ HasHeight (p.rows.read k).length H)
    (hall : ∀ k,HasHeight (s.data.read k) (storedHeight N H)) :
    ∀ k,HasHeight ((run model p fuel s choices).1.data.read k) (storedHeight N H) := by
  induction fuel generalizing s choices with
  | zero => exact hall
  | succ fuel ih =>
      cases he : request model p s with
      | none => simpa only [stop model p (fuel+1) s choices he] using hall
      | some f =>
          have hn:=PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s f he (choices.headD false)
            hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths
          obtain ⟨cn⟩:=advance_certificate model p player s f he (choices.headD false) x hc hs hn c
          have hhn:=advance_heights model p player x hc s hs c f he (choices.headD false) H hv hL hall
          simpa only [run,he] using ih (advance model p s f (choices.headD false)) choices.tail hn cn hhn

end Blotto.PlayerSpecificAlgebraicLoopHeights

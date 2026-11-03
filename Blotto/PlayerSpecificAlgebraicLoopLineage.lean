import Blotto.PlayerSpecificAlgebraicResourceLineage

/-! Every finite executing path preserves the ghost lineage forest.
Height bounds depend on original leaves, not iterated arithmetic depth. -/
namespace Blotto.PlayerSpecificAlgebraicLoopLineage
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificAlgebraicResourceLoop PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem invariant {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) (x : ℝ) (hc : Context p x) (fuel : ℕ) (s : State N) (choices : List Bool)
    (hs : Valid p x s) (c : Certificate p player s) :
    Valid p x (run model p fuel s choices).1 ∧ Nonempty (Certificate p player (run model p fuel s choices).1) := by
  induction fuel generalizing s choices with
  | zero => exact ⟨hs,⟨c⟩⟩
  | succ fuel ih =>
      cases he : request model p s with
      | none =>
          rw [stop model p (fuel+1) s choices he]
          exact ⟨hs,⟨c⟩⟩
      | some f =>
          have hn:=PlayerSpecificAlgebraicResourceInvariant.advance_valid model p s f he (choices.headD false)
            hc.normalized hc.irreducible hc.interval x hc.root hs hc.lengths
          obtain ⟨cn⟩:=advance_certificate model p player s f he (choices.headD false) x hc hs hn c
          simpa only [run,he] using ih (advance model p s f (choices.headD false)) choices.tail hn cn

theorem active_height {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool)
    (s : State N) (c : Certificate p player s) (hm : Normalized p.parameters.root.polynomial)
    (hm0 : p.parameters.root.polynomial≠[]) (hs : ∀ k,Reduced p.parameters.root.polynomial (s.data.read k))
    (H : ℕ)
    (hv : ∀ k,Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player k) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player k) H)
    (hL : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length ∧ HasHeight (p.rows.read k).length H)
    (k : Fin N) (hk : k∈s.active) : HasHeight (s.data.read k) ((H+1)*(N+N)+3) :=
  PlayerSpecificSignedLineage.representation_height p.parameters.root.polynomial _ _ _ (c.positive k) (c.negative k)
    hm hm0 (hs k) H hv hL (c.positive_valid.nodup k hk) (c.negative_valid.nodup k hk) (c.represents k hk)

theorem original_active_height {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (player : Bool)
    (s : State N) (c : Certificate (PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r) player s)
    (hs : ∀ k,Reduced r.root.polynomial (s.data.read k)) (k : Fin N) (hk : k∈s.active) :
    HasHeight (s.data.read k) (PlayerSpecificInitialLineageBound.height N (PlayerSpecificInitialPositivePrecision.inputSize i)) :=
  PlayerSpecificInitialLineageBound.actual_height i r hr player _ (hs k) (c.positive k) (c.negative k)
    (c.positive_valid.nodup k hk) (c.negative_valid.nodup k hk) (c.represents k hk)

end Blotto.PlayerSpecificAlgebraicLoopLineage

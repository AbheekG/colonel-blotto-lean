import Blotto.GeneralPaperIntegerResidualRoots

/-! Actual modified endpoints stay in [0,1]. Every point on the open
proxy-to-endpoint path is positive, even when the poor endpoint is zero.
No reciprocal of the endpoint is formed without its separate positivity.
-/
namespace Blotto.GeneralPaperProxyEndpointBounds
open GeneralPaperProxySelection GeneralPaperProxyBranchSpec GeneralPaperProxyParameters
open GeneralPaperProxyCell GeneralPaperProxyCellPaths
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem selected_endpoint_closed (Q j : ℕ) (hQ : 0<Q) (b : ℝ) (root : Option Farey.Fraction)
    (hRoot : ∀ f, root=some f → Closed Q j f.value)
    (hm : (select Q j hQ b root).modify≠none) : Closed Q j (select Q j hQ b root).endpoint := by
  rcases select_spec Q j hQ b root with hu|hr|hp|her|hep
  · exact (hm hu.1).elim
  · obtain ⟨f,hf,hbf,hne,hmod,hv,ht⟩ := hr
    rw [ht]
    exact hRoot f hf
  · obtain ⟨f,hf,hfb,hmod,hv,ht⟩ := hp
    rw [ht]
    exact hRoot f hf
  · rw [her.2.2.2.2]
    exact (endpoints_closed Q j hQ).2
  · rw [hep.2.2.2.2]
    exact (endpoints_closed Q j hQ).1

theorem endpoint_unit (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    0≤(GeneralPaperProxyClassifier.classify m k b).choice.endpoint ∧
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≤1 := by
  have hc := selected_endpoint_closed (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell
    (grid_positive m k) b (GeneralPaperProxyClassifier.classify m k b).root
    (fun f hf => (GeneralPaperProxyClassifier.root_sound m k b f hf).2) hm
  change Closed _ _ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint at hc
  have hj : (GeneralPaperProxyClassifier.classify m k b).cell<(prepare m k).Qg :=
    (GeneralPaperProxyQuotient.locate_spec m k b hb).1
  have hu : GeneralPaperBucketGeometry.upper (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell≤1 := by
    unfold GeneralPaperBucketGeometry.upper
    apply (div_le_one (show (0:ℚ)<(prepare m k).Qg by exact_mod_cast grid_positive m k)).mpr
    exact_mod_cast (show (GeneralPaperProxyClassifier.classify m k b).cell+1≤(prepare m k).Qg by omega)
  have hlo : (0:ℚ)≤GeneralPaperBucketGeometry.lower (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell := by
    unfold GeneralPaperBucketGeometry.lower
    positivity
  exact ⟨hlo.trans hc.1,hc.2.trans hu⟩

theorem open_path_positive (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) (x : ℚ)
    (hx : Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : 0<x := by
  have hp := (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  have he := (endpoint_unit m k b hb hm).1
  rcases hx with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact hp.trans h1
  · exact he.trans_lt h1

end Blotto.GeneralPaperProxyEndpointBounds

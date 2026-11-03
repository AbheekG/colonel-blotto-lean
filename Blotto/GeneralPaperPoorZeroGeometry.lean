import Blotto.GeneralPaperSourceBasisEndpoint

/-! A selected poor endpoint zero forces the proxy into the first grid
cell. Its proxy is at most 1/Qg, which is enough for the all-tuples strict
budget argument; no reciprocal of the zero endpoint is used.
-/
namespace Blotto.GeneralPaperPoorZeroGeometry
open GeneralPaperProxyParameters GeneralPaperProxySelection GeneralPaperProxyBranchSpec
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem first_cell (m k : ℕ) (b : ℝ)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hZero : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    (GeneralPaperProxyClassifier.classify m k b).cell=0 := by
  have hn : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  have hc := GeneralPaperProxyEndpointBounds.selected_endpoint_closed (prepare m k).Qg
    (GeneralPaperProxyClassifier.classify m k b).cell (grid_positive m k) b
    (GeneralPaperProxyClassifier.classify m k b).root (fun f hf => (GeneralPaperProxyClassifier.root_sound m k b f hf).2) hn
  change GeneralPaperProxyCell.Closed _ _ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint at hc
  rw [hZero] at hc
  have hq : (0:ℚ)<(prepare m k).Qg := by exact_mod_cast grid_positive m k
  have hl := (div_le_iff₀ hq).mp hc.1
  simp only [zero_mul] at hl
  have he : ((GeneralPaperProxyClassifier.classify m k b).cell:ℚ)=0 := le_antisymm hl (Nat.cast_nonneg _)
  exact_mod_cast he

theorem proxy_small (m k : ℕ) (b : ℝ)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hZero : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value≤1/((prepare m k).Qg:ℚ) := by
  have hj := first_cell m k b hModify hZero
  have spec := select_spec (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell (grid_positive m k) b
    (GeneralPaperProxyClassifier.classify m k b).root
  change Unchanged b (GeneralPaperProxyClassifier.classify m k b).choice ∨
    RootRich _ _ b _ (GeneralPaperProxyClassifier.classify m k b).choice ∨
      RootPoor _ _ b _ (GeneralPaperProxyClassifier.classify m k b).choice ∨
        EmptyRich _ _ b _ (GeneralPaperProxyClassifier.classify m k b).choice ∨
          EmptyPoor _ _ b _ (GeneralPaperProxyClassifier.classify m k b).choice at spec
  rcases spec with hu|hr|hp|her|hep
  · have he := hu.1
    rw [hModify] at he
    cases he
  · obtain ⟨f,_,_,_,he,_,_⟩ := hr
    cases Option.some.inj (hModify.symm.trans he)
  · obtain ⟨f,_,_,_,hProxy,_⟩ := hp
    rw [hProxy,hj,GeneralPaperBucketGeometry.upper]
    simp only [Nat.cast_zero,zero_add,le_refl]
  · have he := her.2.2.1
    cases Option.some.inj (hModify.symm.trans he)
  · rw [hep.2.2.2.1,hj,GeneralPaperBucketGeometry.midpoint]
    simp only [Nat.cast_zero,mul_zero,zero_add]
    apply one_div_le_one_div_of_le (by exact_mod_cast grid_positive m k)
    have hp : (0:ℚ)≤(prepare m k).Qg := by positivity
    linarith only [hp]

theorem grid_gt_fields (m k : ℕ) : m<(prepare m k).Qg := by
  have hh : m<(prepare m k).H := by
    rw [(data m k).2.2.2.1,pow_succ]
    have hp : 0<(m+3)^((prepare m k).d+1) := by positivity
    nlinarith only [hp]
  have hp := H_positive m k
  have hg := grid_lower m k
  nlinarith only [hh,hp,hg]

theorem opposing_gt_fields (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hZero : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    (m:ℚ)<1/(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value := by
  have hSmall := proxy_small m k b hModify hZero
  have hq : (0:ℚ)<(prepare m k).Qg := by exact_mod_cast grid_positive m k
  have hp := (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  have hRecip := one_div_le_one_div_of_le hp hSmall
  simp only [one_div_one_div] at hRecip
  exact (show (m:ℚ)<(prepare m k).Qg by exact_mod_cast grid_gt_fields m k).trans_le hRecip

end Blotto.GeneralPaperPoorZeroGeometry

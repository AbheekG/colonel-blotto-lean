import Blotto.GeneralPaperRetainedModifiedColumnBits
import Blotto.GeneralPaperRetainedPairSource

/-! A complete bit-priced physical compiler pair: unchanged arrays are
retained and only the selected defender executes strict preparation,
initializer, basis, continuation and endpoint-column materialization. -/
namespace Blotto.GeneralPaperRetainedCompilerPairBits
open GeneralPaperOriginalDrawEquilibrium GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) : Option (Columns T m K)×ℕ :=
  match classified.choice.modify with
  | none => (some columns,64*W)
  | some .rich =>
    let endpoint := GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified
    let rich := GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
      hK columns.rich values 1 proxyValue false endpoint.1 classified.choice.endpoint
    (rich.1.map (fun r => ⟨r,columns.poor⟩),endpoint.2+rich.2+64*W)
  | some .poor =>
    let endpoint := GeneralPaperRetainedEndpointFraction.run model.rat W Q hQ classified
    let poor := GeneralPaperRetainedModifiedColumnBits.run model W depth S H classified.choice.proxy.num classified.choice.proxy.den
      hK columns.poor values proxyValue 1 true endpoint.1 classified.choice.endpoint
    (poor.1.map (fun p => ⟨columns.rich,p⟩),endpoint.2+poor.2+64*W)

theorem unchanged {T m K : ℕ} (model : RationalCostModel) (W depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K)
    (h : classified.choice.modify=none) :
    run model W depth S H Q hQ hK classified proxyValue values columns=(some columns,64*W) := by
  simp only [run,h]

theorem data {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (b : ℝ) (hb : 0<b ∧ b<1)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m (prepare m k).K) :
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
      (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns).1=
      (GeneralPaperRetainedCompilerPair.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
        (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns).1 := by
  let classified := GeneralPaperProxyClassifier.classify m k b
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) classified).1
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hv := GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hr := GeneralPaperRetainedModifiedColumnBits.data model W k classified.choice.proxy.num classified.choice.proxy.den
    columns.rich values 1 classified.choice.proxy.value false endpoint classified.choice.endpoint hv hm hf.1 classified.choice.proxy.den_pos
  have hp := GeneralPaperRetainedModifiedColumnBits.data model W k classified.choice.proxy.num classified.choice.proxy.den
    columns.poor values classified.choice.proxy.value 1 true endpoint classified.choice.endpoint hv hm hf.1 classified.choice.proxy.den_pos
  have he := GeneralPaperRetainedEndpointFraction.data model.rat (fun _ => 1) W 1 (prepare m k).Qg (grid_positive m k) classified
  dsimp only [endpoint] at hr hp
  erw [he] at hr hp
  dsimp only [classified] at hr hp he
  cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => simp only [run,GeneralPaperRetainedCompilerPair.run,hc]
  | some side =>
    cases side with
    | rich =>
      simp only [run,GeneralPaperRetainedCompilerPair.run,hc,he]
      exact congrArg (Option.map (fun r => (⟨r,columns.poor⟩ : Columns T m (prepare m k).K))) hr
    | poor =>
      simp only [run,GeneralPaperRetainedCompilerPair.run,hc,he]
      exact congrArg (Option.map (fun p => (⟨columns.rich,p⟩ : Columns T m (prepare m k).K))) hp

end Blotto.GeneralPaperRetainedCompilerPairBits

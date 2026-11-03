import Blotto.GeneralPaperPhysicalColumnPair

/-! Select the sole modified defender from the retained classifier. Both
unchanged column arrays are passed by reference; only the selected side
builds its full strict-score preparation and endpoint anchors. Endpoint
metadata is read once on the reached modified branch. -/
namespace Blotto.GeneralPaperRetainedCompilerPair
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {T m K : ℕ} (model : RationalCostModel) (depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) : Option (Columns T m K)×ℕ :=
  match classified.choice.modify with
  | none => (some columns,64)
  | some .rich =>
    let endpoint := GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 Q hQ classified
    let rich := GeneralPaperRetainedModifiedColumns.run model depth S H classified.choice.proxy.num classified.choice.proxy.den
      hK columns.rich values 1 proxyValue false endpoint.1 classified.choice.endpoint
    (rich.1.map (fun r => ⟨r,columns.poor⟩),endpoint.2+rich.2+64)
  | some .poor =>
    let endpoint := GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 Q hQ classified
    let poor := GeneralPaperRetainedModifiedColumns.run model depth S H classified.choice.proxy.num classified.choice.proxy.den
      hK columns.poor values proxyValue 1 true endpoint.1 classified.choice.endpoint
    (poor.1.map (fun p => ⟨columns.rich,p⟩),endpoint.2+poor.2+64)

theorem unchanged {T m K : ℕ} (model : RationalCostModel) (depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K)
    (h : classified.choice.modify=none) :
    run model depth S H Q hQ hK classified proxyValue values columns=(some columns,64) := by
  simp only [run,h]

theorem arithmetic_work {T m K : ℕ} (model : RationalCostModel) (depth S H Q : ℕ) (hQ : 0<Q) (hK : 0<K)
    (classified : GeneralPaperProxyClassifier.Result) (proxyValue : ℚ)
    (values : GeneralPaperRetainedFieldValues.Values m) (columns : Columns T m K) :
    (run model depth S H Q hQ hK classified proxyValue values columns).2≤
      (match classified.choice.modify with
      | none => 0
      | some .rich => (GeneralPaperRetainedModifiedColumns.run model depth S H classified.choice.proxy.num classified.choice.proxy.den
          hK columns.rich values 1 proxyValue false
          (GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 Q hQ classified).1 classified.choice.endpoint).2
      | some .poor => (GeneralPaperRetainedModifiedColumns.run model depth S H classified.choice.proxy.num classified.choice.proxy.den
          hK columns.poor values proxyValue 1 true
          (GeneralPaperRetainedEndpointFraction.run (fun _ => 1) 1 Q hQ classified).1 classified.choice.endpoint).2)+130 := by
  have he := GeneralPaperRetainedEndpointFraction.arithmetic_work Q hQ classified
  cases hr : classified.choice.modify with
  | none => simp only [run,hr];omega
  | some side => cases side <;> simp only [run,hr] <;> omega

end Blotto.GeneralPaperRetainedCompilerPair

import Blotto.GeneralPaperEndpointContractSecurity

/-! The actual prepared strict-score contract and decoded dictionary
feed continuous security against the source law. Quantization contributes
1/K and this single modified defender contributes m/S.
-/
namespace Blotto.GeneralPaperDecodedPreparedSecurity
open RationalOrderCell GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperTransferPreparation
open GeneralPaperSourceEndpointBranch GeneralPaperEndpointDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (own opposing : ℚ) (hOwn : 0<own) (hOpposing : 0<opposing)
    (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hRows : ∀ i,Blotto.Feasible (own:ℝ) (fun j => ((rows.read i).read j:ℝ))) (budget : ℝ) (hBudget : 0≤budget)
    (result : Result T m K)
    (hc : Contract (prepare hT hK hDiv rows own opposing v S).dictionary v S
      (prepare hT hK hDiv rows own opposing v S).threshold budget result) :
    UnitDictionary (dictionary result) hT hK ∧
      security v.values budget (law (dictionary result) hT).law≤
        security v.values (opposing:ℝ) (law (GeneralPaperRowQuantizer.original rows) hT).law+1/(K:ℝ)+(m:ℝ)/(S:ℝ) := by
  have hu := prepared_unit hT hK hDiv rows own opposing hOwn v S hRows
  have hd := GeneralPaperEndpointContractSecurity.bound _ hT hK hu v S hS (opposing/own) (div_pos hOpposing hOwn)
    _ (reference_threshold hT hK hDiv rows own opposing v S) budget hBudget result hc
  have hs := source_security hT hK hDiv rows own opposing hOwn hOpposing.le v S hRows
  exact ⟨GeneralPaperEndpointDictionaryUnit.contract_unit _ v S _ budget result hT hK hc hu.balanced,
    by linarith only [hd,hs]⟩

end Blotto.GeneralPaperDecodedPreparedSecurity

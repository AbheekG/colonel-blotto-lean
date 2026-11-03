import Blotto.GeneralPaperSourceEndpointLayerRates

/-! Actual parametric return ownership: complete affine table/witnesses,
both bracket endpoints and optional output record. Native processed-field
and bracket-height invariants derive the bound for every returned prefix. -/
namespace Blotto.GeneralPaperParametricOutputStorage
open RationalOrderCell GeneralPaperRayParametricDP GeneralPaperRayAffineScoreStep
open GeneralPaperRayUniformSize GeneralPaperAffineWitnessStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000

def outputFoot {S K : ℕ} (W : ℕ) : Option (Output S K) → ℕ
  | none => 32*W
  | some out => tableFoot W out.table+rationalWordWidth out.bracket.lower+rationalWordWidth out.bracket.upper+96*W

def outputProfile (W m K S R : ℕ) : ℕ := tableProfile W S K m R+2*(1+2*R)+128*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ)
    (fields : List (Field K)) (hLen : fields.length≤m) (hf : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X V f)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    outputFoot W (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1≤
      outputProfile W m K S (width D E m X V P) := by
  cases hp : (GeneralPaperParametricRunBits.run model W matrix x w S h beta fields lo hi).1 with
  | none => simp only [outputFoot,outputProfile]; omega
  | some out =>
    let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
    have hr : GeneralPaperRayParametricDP.run query S fields lo hi=some out :=
      (GeneralPaperParametricRunBits.data model W matrix x w S h beta fields lo hi).symm.trans hp
    have hBracket := GeneralPaperRayParametricRunSize.bracket hD hE query fields lo hi hLen hf hl hh out hr
    have hTable := table_bound W D E X V fields.length m P hD hE hLen out.table
      (GeneralPaperRayAffineDPSize.run D E X V S query fields lo hi hf out hr)
    have hLo := rationalWordWidth_of_height hBracket.1
    have hHi := rationalWordWidth_of_height hBracket.2
    unfold outputFoot outputProfile
    dsimp only
    omega

end Blotto.GeneralPaperParametricOutputStorage

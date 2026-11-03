import Blotto.GeneralPaperCheckedAffineEndpoint

/-! One affine cache construction, followed by the two original-polytope
checks and native endpoint decoding. This is a component arithmetic
ledger; it does not price the preceding basis/source or claim bit/space
completion.
-/
namespace Blotto.GeneralPaperEndpointRecheckWork
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (state : GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) : GeneralPaperCheckedAffineEndpoint.Result (m*(K-1)) :=
  let data := GeneralPaperBasisAffineData.prepare state
  let checked := GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma data
  ⟨checked.point,data.work+checked.work+8⟩

theorem point {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (state : GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) :
    (run labels matrix S h auxiliary gamma state).point=
      (GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma (GeneralPaperBasisAffineData.prepare state)).point := rfl

theorem work {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (state : GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) :
    (run labels matrix S h auxiliary gamma state).work≤
      512*(m*(K-1)+1)^2+192*(m*(K-1)+1)+1024*(m*(K-1)+m*T+m+1)+2048*(m+1)*(K+1)*(S+1)+56 := by
  have ha := GeneralPaperBasisAffineData.work state
  have hc := GeneralPaperCheckedAffineEndpoint.work hm labels matrix S h auxiliary gamma (GeneralPaperBasisAffineData.prepare state)
  change (GeneralPaperBasisAffineData.prepare state).work+
    (GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma (GeneralPaperBasisAffineData.prepare state)).work+8≤_
  omega

end Blotto.GeneralPaperEndpointRecheckWork

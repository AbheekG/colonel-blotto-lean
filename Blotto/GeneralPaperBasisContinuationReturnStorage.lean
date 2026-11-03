import Blotto.GeneralPaperRawEndpointReturnStorage

/-! Literal final continuation ownership: the full incoming basis, the
returned affine cache, optional point and all five parent work fields.
Child construction/evaluation/check windows remain in caller reserves. -/
namespace Blotto.GeneralPaperBasisContinuationReturnStorage
open RationalOrderCell GeneralPaperBasisAffineData GeneralPaperBasisState
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def metadataCap (model : RationalCostModel) (W T m K S R F : ℕ) : ℕ :=
  F+GeneralPaperRawEndpointReturnStorage.price model W T m K S R+16*W
def controls {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (state : State (m*(K-1)) (m*(K-1))) : List ℕ :=
  let affine := GeneralPaperBasisAffineBits.prepare model.rat W state
  let checked := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen affine
  let result := GeneralPaperRetainedBasisEndpointBits.continueRun model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state
  [affine.work,checked.work,result.2,16*W,affine.work+checked.work]
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (state : State (m*(K-1)) (m*(K-1))) : ℕ :=
  let affine := GeneralPaperBasisAffineBits.prepare model.rat W state
  let result := GeneralPaperRetainedBasisEndpointBits.continueRun model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state
  GeneralPaperEncodedBasisStorage.footprint W state+GeneralPaperBasisAffineStorage.footprint W affine+
    GeneralPaperRawEndpointReturnStorage.optionFoot W result.1+
    fields W (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state)+128*W
def profile (model : RationalCostModel) (W T m K S R F Bstate : ℕ) : ℕ :=
  Bstate+GeneralPaperRawEndpointReturnStorage.cacheProfile W (m*(K-1)) R F+
    GeneralPaperRawEndpointReturnStorage.optionProfile W (m*(K-1)) R+
    5*(natBits (metadataCap model W T m K S R F)+W)+160*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W H B N R F Bstate : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ)
    (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen) (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (state : State (m*(K-1)) (m*(K-1)))
    (hState : GeneralPaperEncodedBasisStorage.footprint W state≤Bstate)
    (hNonzero : (GeneralPaperBasisAffineBits.prepare model.rat W state).determinant≠0)
    (hd : (GeneralPaperBasisAffineBits.prepare model.rat W state).determinant.natAbs≤H)
    (hc : ∀ i,((GeneralPaperBasisAffineBits.prepare model.rat W state).constant.read i).natAbs≤H)
    (hs : ∀ i,((GeneralPaperBasisAffineBits.prepare model.rat W state).slope.read i).natAbs≤H)
    (hF : (GeneralPaperBasisAffineBits.prepare model.rat W state).work≤F)
    (haN : auxNum.natAbs≤B) (haD : auxDen≤N) (heN : endNum.natAbs≤B) (heD : endDen≤N)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (hRoot : GeneralPaperRayUniformSize.width (N*H) 1 m ((N+B)*H) 0 B+1≤R)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    window model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state≤profile model W T m K S R F Bstate := by
  let affine := GeneralPaperBasisAffineBits.prepare model.rat W state
  let checked := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen affine
  let result := GeneralPaperRetainedBasisEndpointBits.continueRun model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state
  change affine.work≤F at hF
  have hH : 1+binaryWordWidth H≤R := by
    have hw := binaryWordWidth_mono (show H≤GeneralPaperRawAffineBits.cap H B N by unfold GeneralPaperRawAffineBits.cap; omega)
    unfold GeneralPaperRawAffineBits.width at hR
    omega
  have hCache := GeneralPaperRawEndpointReturnStorage.cache_bound W H R F affine hd hc hs hH hF
  have hPoint := GeneralPaperRawEndpointReturnStorage.option_bound model W H B N R labels matrix S h auxiliary gamma
    auxNum endNum auxDen endDen affine heN heD hd hc hs hR
  have hChecked := GeneralPaperRawEndpointReturnStorage.work model W H B N R hm labels matrix S h auxiliary gamma
    auxNum endNum auxDen endDen hAuxDen hEndDen hAux hEnd affine hNonzero hd hc hs haN haD heN heD hR hRoot hW hD hK hM hIndex
  change checked.work≤GeneralPaperRawEndpointReturnStorage.price model W T m K S R at hChecked
  have hTotal : result.2≤metadataCap model W T m K S R F := by
    change affine.work+checked.work+16*W≤F+GeneralPaperRawEndpointReturnStorage.price model W T m K S R+16*W
    omega
  dsimp only [metadataCap] at hTotal
  have hf := fields_bound W (natBits (metadataCap model W T m K S R F))
    (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      change z∈[affine.work,checked.work,result.2,16*W,affine.work+checked.work] at hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  have hFields : fields W (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state)≤
      5*(natBits (metadataCap model W T m K S R F)+W)+32*W := by
    simpa only [controls,List.length_cons,List.length_nil] using hf
  change GeneralPaperRawEndpointReturnStorage.optionFoot W result.1≤_ at hPoint
  unfold window profile
  dsimp only
  dsimp only [affine,result] at hCache hPoint
  omega

end Blotto.GeneralPaperBasisContinuationReturnStorage

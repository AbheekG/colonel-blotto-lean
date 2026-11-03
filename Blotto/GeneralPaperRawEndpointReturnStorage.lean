import Blotto.GeneralPaperSourceFinalCheckStorageReachedRates

/-! Literal raw endpoint parent ownership and return counters. Actual
cache/fractions/thresholds, auxiliary and reached endpoint arrays, optional
returned vector and conditional branch partial fields coexist. Child raw
evaluation and static/DP scratch remain in their existing caller reserves. -/
namespace Blotto.GeneralPaperRawEndpointReturnStorage
open RationalOrderCell GeneralPaperBasisAffineData GeneralPaperBasisOriginalDirection GeneralPaperRayRationalBound
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def evaluationPrice (model : RationalCostModel) (W T m K S R : ℕ) : ℕ :=
  256*(m*(K-1)+1)*(W+model.rat R)+GeneralPaperFinalPolytopeStorage.price model W T m K S R
def price (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := 2*evaluationPrice model W T m K S R+16*W
def metadataCap (model : RationalCostModel) (W T m K S R : ℕ) : ℕ := S+m*(K-1)+2+3*price model W T m K S R
def cacheProfile (W d R F : ℕ) : ℕ := 2*arrayProfile W d R+R+natBits F+32*W
def optionFoot {d : ℕ} (W : ℕ) : Option (GeneralPaperBasisRationalSolve.RatVector d) → ℕ
  | none => 1
  | some p => 1+arrayFootprint W rationalWordWidth p+32*W
def optionProfile (W d R : ℕ) : ℕ := 1+arrayProfile W d R+32*W

theorem fraction_word (H B N R : ℕ) (numerator : ℤ) (denominator : ℕ) (hb : numerator.natAbs≤B) (hn : denominator≤N)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) : rationalWordWidth ((numerator:ℚ)/(denominator:ℚ))≤R := by
  let M := GeneralPaperRawAffineBits.cap H B N
  have hB : B≤M := by unfold M GeneralPaperRawAffineBits.cap; omega
  have hN : denominator≤M := by unfold M GeneralPaperRawAffineBits.cap; omega
  have hwB := binaryWordWidth_mono hB
  have hwN := binaryWordWidth_mono hN
  have h := rationalWordWidth_of_height ((GeneralPaperBasisStageSize.int_height numerator B hb).div (GeneralPaperBasisDivideBits.nat_height denominator))
  unfold GeneralPaperRawAffineBits.width at hR
  dsimp only [M] at hwB hwN
  omega

theorem array_bound {d : ℕ} (model : RationalCostModel) (W H B N R : ℕ) (cache : Data d) (num : ℤ) (den : ℕ)
    (hb : num.natAbs≤B) (hn : den≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) :
    arrayFootprint W rationalWordWidth (GeneralPaperRawAffineEvaluate.run true model W cache num den).1≤arrayProfile W d R := by
  apply GeneralPaperEncodedBasisStorage.array_bound
  intro i
  change rationalWordWidth ((PaperIndexedArrayConstruction.run (fun w => w) W (GeneralPaperRawAffineEvaluate.entry model.rat W cache num den)).1.read i)≤R
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperRawAffineStorage.entry_word model W H B N R cache num den hb hn hd hc hs hR i

theorem point_form {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (auxNum endNum : ℤ) (auxDen endDen : ℕ) (cache : Data (m*(K-1))) :
    (GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point=none ∨
      (GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point=
        some (GeneralPaperRawAffineEvaluate.run true model W cache endNum endDen).1 := by
  unfold GeneralPaperRawEndpointBits.run
  dsimp only
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem evaluation_work {T m K : ℕ} (model : RationalCostModel) (W H B N R : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ)
    (beta : ℚ) (num : ℤ) (den : ℕ) (hDen : 0<den) (hBeta : (num:ℚ)/(den:ℚ)=beta)
    (cache : Data (m*(K-1))) (hNonzero : cache.determinant≠0) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H)
    (hb : num.natAbs≤B) (hn : den≤N) (hR : GeneralPaperRawAffineBits.width H B N≤R)
    (hRoot : GeneralPaperRayUniformSize.width (N*H) 1 m ((N+B)*H) 0 B+1≤R)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperRawAffineEvaluate.run true model W cache num den).2+
      (GeneralPaperFinalPolytopeBits.run model W labels matrix S h beta (reader (GeneralPaperRawAffineEvaluate.run true model W cache num den).1)).work≤
        evaluationPrice model W T m K S R := by
  have he := GeneralPaperRawEndpointBits.evaluation_work model W H B N hm labels matrix S h beta num den hDen hBeta cache
    hNonzero hd hc hs hb hn hW hD hK hM hIndex
  have hmD := GeneralPaperRawEndpointBits.evaluationProfile_den_mono model W T m K S H B N (den*cache.determinant.natAbs) (N*H) (Nat.mul_le_mul hn hd)
  apply (he.trans hmD).trans
  unfold GeneralPaperRawEndpointBits.evaluationProfile evaluationPrice GeneralPaperFinalPolytopeStorage.price
    GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile
  gcongr <;> apply model.monotone <;> omega

theorem work {T m K : ℕ} (model : RationalCostModel) (W H B N R : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ)
    (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen) (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (cache : Data (m*(K-1))) (hNonzero : cache.determinant≠0) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H)
    (haN : auxNum.natAbs≤B) (haD : auxDen≤N) (heN : endNum.natAbs≤B) (heD : endDen≤N)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (hRoot : GeneralPaperRayUniformSize.width (N*H) 1 m ((N+B)*H) 0 B+1≤R)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).work≤price model W T m K S R := by
  have ha := evaluation_work model W H B N R hm labels matrix S h auxiliary auxNum auxDen hAuxDen hAux cache hNonzero hd hc hs haN haD hR hRoot hW hD hK hM hIndex
  have he := evaluation_work model W H B N R hm labels matrix S h gamma endNum endDen hEndDen hEnd cache hNonzero hd hc hs heN heD hR hRoot hW hD hK hM hIndex
  unfold GeneralPaperRawEndpointBits.run price
  dsimp only
  split <;> dsimp only <;> omega

def controls {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (auxNum endNum : ℤ) (auxDen endDen : ℕ) (cache : Data (m*(K-1))) : List ℕ :=
  let a := GeneralPaperRawAffineEvaluate.run true model W cache auxNum auxDen
  let ca := GeneralPaperFinalPolytopeBits.run model W labels matrix S h auxiliary (reader a.1)
  let e := GeneralPaperRawAffineEvaluate.run true model W cache endNum endDen
  let ce := GeneralPaperFinalPolytopeBits.run model W labels matrix S h gamma (reader e.1)
  let result := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache
  [S,h,a.2,ca.work,result.work,8*W,a.2+ca.work,GeneralPaperFinalStaticLoopStorage.bit ca.accepted,
    GeneralPaperFinalStaticLoopStorage.bit result.point.isSome]++
      if ca.accepted then [e.2,ce.work,16*W,a.2+ca.work+e.2,a.2+ca.work+e.2+ce.work,GeneralPaperFinalStaticLoopStorage.bit ce.accepted] else []

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (auxNum endNum : ℤ) (auxDen endDen : ℕ) (cache : Data (m*(K-1))) : ℕ :=
  let a := GeneralPaperRawAffineEvaluate.run true model W cache auxNum auxDen
  let ca := GeneralPaperFinalPolytopeBits.run model W labels matrix S h auxiliary (reader a.1)
  let e := GeneralPaperRawAffineEvaluate.run true model W cache endNum endDen
  let result := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache
  GeneralPaperBasisAffineStorage.footprint W cache+arrayFootprint W rationalWordWidth a.1+
    (if ca.accepted then arrayFootprint W rationalWordWidth e.1 else 0)+rationalWordWidth auxiliary+rationalWordWidth gamma+
    integerBits auxNum+integerBits endNum+natBits auxDen+natBits endDen+optionFoot W result.point+
    fields W (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache)+256*W
def profile (model : RationalCostModel) (W T m K S R F : ℕ) : ℕ :=
  cacheProfile W (m*(K-1)) R F+2*arrayProfile W (m*(K-1)) R+6*R+optionProfile W (m*(K-1)) R+
    15*(natBits (metadataCap model W T m K S R)+W)+288*W

theorem cache_bound {d : ℕ} (W H R F : ℕ) (cache : Data d) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H)
    (hH : 1+binaryWordWidth H≤R) (hF : cache.work≤F) : GeneralPaperBasisAffineStorage.footprint W cache≤cacheProfile W d R F := by
  have hC := GeneralPaperEncodedBasisStorage.array_bound W R integerBits cache.constant
    (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hc i)) 1).trans hH)
  have hS := GeneralPaperEncodedBasisStorage.array_bound W R integerBits cache.slope
    (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hs i)) 1).trans hH)
  have hD : integerBits cache.determinant≤R := (Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans hH
  have hW : natBits cache.work≤natBits F := Nat.add_le_add_left (binaryWordWidth_mono hF) 1
  unfold GeneralPaperBasisAffineStorage.footprint cacheProfile
  omega

theorem option_bound {T m K : ℕ} (model : RationalCostModel) (W H B N R : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ)
    (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ) (cache : Data (m*(K-1)))
    (hb : endNum.natAbs≤B) (hn : endDen≤N) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) :
    optionFoot W (GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point≤
      optionProfile W (m*(K-1)) R := by
  have hPoint := array_bound model W H B N R cache endNum endDen hb hn hd hc hs hR
  rcases point_form model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache with h|h
  · rw [h]; simp only [optionFoot,optionProfile]; omega
  · rw [h]; simp only [optionFoot,optionProfile]; omega

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W H B N R F : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (hh : h≤S)
    (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen) (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (cache : Data (m*(K-1))) (hNonzero : cache.determinant≠0) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ i,(cache.constant.read i).natAbs≤H) (hs : ∀ i,(cache.slope.read i).natAbs≤H) (hF : cache.work≤F)
    (haN : auxNum.natAbs≤B) (haD : auxDen≤N) (heN : endNum.natAbs≤B) (heD : endDen≤N)
    (hR : GeneralPaperRawAffineBits.width H B N≤R) (hRoot : GeneralPaperRayUniformSize.width (N*H) 1 m ((N+B)*H) 0 B+1≤R)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    window model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache≤profile model W T m K S R F := by
  let a := GeneralPaperRawAffineEvaluate.run true model W cache auxNum auxDen
  let ca := GeneralPaperFinalPolytopeBits.run model W labels matrix S h auxiliary (reader a.1)
  let e := GeneralPaperRawAffineEvaluate.run true model W cache endNum endDen
  let ce := GeneralPaperFinalPolytopeBits.run model W labels matrix S h gamma (reader e.1)
  let result := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache
  let E := evaluationPrice model W T m K S R
  let M := GeneralPaperRawAffineBits.cap H B N
  have hSmall : 1+binaryWordWidth M≤R := by dsimp only [M]; unfold GeneralPaperRawAffineBits.width at hR; omega
  have hH : 1+binaryWordWidth H≤R := (Nat.add_le_add_left (binaryWordWidth_mono (show H≤M by unfold M GeneralPaperRawAffineBits.cap; omega)) 1).trans hSmall
  have hCache := cache_bound W H R F cache hd hc hs hH hF
  have hA := array_bound model W H B N R cache auxNum auxDen haN haD hd hc hs hR
  have hE := array_bound model W H B N R cache endNum endDen heN heD hd hc hs hR
  have hGuarded : (if ca.accepted then arrayFootprint W rationalWordWidth e.1 else 0)≤arrayProfile W (m*(K-1)) R := by
    split
    · exact hE
    · omega
  have hAuxWord : rationalWordWidth auxiliary≤R := by rw [←hAux]; exact fraction_word H B N R auxNum auxDen haN haD hR
  have hEndWord : rationalWordWidth gamma≤R := by rw [←hEnd]; exact fraction_word H B N R endNum endDen heN heD hR
  have rawInt (z : ℤ) (hz : z.natAbs≤B) : integerBits z≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show z.natAbs≤M by unfold M GeneralPaperRawAffineBits.cap; omega)) 1).trans hSmall
  have rawNat (n : ℕ) (hn : n≤N) : natBits n≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show n≤M by unfold M GeneralPaperRawAffineBits.cap; omega)) 1).trans hSmall
  have hAN := rawInt auxNum haN
  have hEN := rawInt endNum heN
  have hAD := rawNat auxDen haD
  have hED := rawNat endDen heD
  have hOption := option_bound model W H B N R labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache heN heD hd hc hs hR
  have hPairA := evaluation_work model W H B N R hm labels matrix S h auxiliary auxNum auxDen hAuxDen hAux cache hNonzero hd hc hs haN haD hR hRoot hW hD hK hM hIndex
  have hPairE := evaluation_work model W H B N R hm labels matrix S h gamma endNum endDen hEndDen hEnd cache hNonzero hd hc hs heN heD hR hRoot hW hD hK hM hIndex
  change a.2+ca.work≤E at hPairA
  change e.2+ce.work≤E at hPairE
  have hWork := work model W H B N R hm labels matrix S h auxiliary gamma auxNum endNum auxDen endDen hAuxDen hEndDen hAux hEnd
    cache hNonzero hd hc hs haN haD heN heD hR hRoot hW hD hK hM hIndex
  change result.work≤2*E+16*W at hWork
  have hbA := GeneralPaperFinalStaticLoopStorage.bit_bound ca.accepted
  have hbE := GeneralPaperFinalStaticLoopStorage.bit_bound ce.accepted
  have hbR := GeneralPaperFinalStaticLoopStorage.bit_bound result.point.isSome
  have hCount : (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).length≤15 := by
    unfold controls
    dsimp only
    split <;> norm_num only [List.length_append,List.length_cons,List.length_nil]
  have hf := fields_bound W (natBits (metadataCap model W T m K S R))
    (controls model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache) (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      change z∈[S,h,a.2,ca.work,result.work,8*W,a.2+ca.work,GeneralPaperFinalStaticLoopStorage.bit ca.accepted,
        GeneralPaperFinalStaticLoopStorage.bit result.point.isSome]++
        (if ca.accepted then [e.2,ce.work,16*W,a.2+ca.work+e.2,a.2+ca.work+e.2+ce.work,GeneralPaperFinalStaticLoopStorage.bit ce.accepted] else []) at hz
      change z≤S+m*(K-1)+2+3*(2*E+16*W)
      rcases List.mem_append.mp hz with hz|hz
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      · split at hz
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
        · simp only [List.not_mem_nil] at hz)
  have hFields := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) _)
  unfold window profile
  dsimp only
  dsimp only [a,ca,e,result] at hGuarded hOption hFields
  omega

end Blotto.GeneralPaperRawEndpointReturnStorage

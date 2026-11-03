import Blotto.GeneralPaperSelectedSearchStorage

/-! Actual crossing-array reads joined to selected-search caller storage.
Each read retains the current rational and native return/index metadata.
Batch/array owners and the enclosing refinement return are separate joins.
The arbitrary space observer may describe any local phase of a query. -/
namespace Blotto.GeneralPaperCrossingSearchStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def readWindow {n : ℕ} (query : ℚ → Bool×ℕ) (space : ℚ → ℕ) (W : ℕ)
    (values : FixedArrayTable n ℚ) (i : Fin n) : ℕ :=
  let t := values.read i
  let current := query t
  let result := GeneralPaperPricedCrossingRefinement.readQuery query W values i
  space t+rationalWordWidth t+
    fields W [i.val,current.2,result.2,8*W,if result.1=true then 1 else 0]+128*W

def readCap (W n E : ℕ) : ℕ := n+E+8*W+2
def readProfile (W n R E Q : ℕ) : ℕ := Q+(1+2*R)+5*(natBits (readCap W n E)+W)+160*W

theorem read_bounded {n : ℕ} (query : ℚ → Bool×ℕ) (space : ℚ → ℕ) (W N R E Q : ℕ)
    (values : FixedArrayTable n ℚ) (i : Fin n) (hn : n≤N) (hR : RationalHeight (values.read i) R)
    (hE : (query (values.read i)).2≤E) (hQ : space (values.read i)≤Q) :
    readWindow query space W values i≤readProfile W N R E Q := by
  let t := values.read i
  let current := query t
  let result := GeneralPaperPricedCrossingRefinement.readQuery query W values i
  have hWord := rationalWordWidth_of_height hR
  have hShape : result.2=current.2+8*W := rfl
  have hBool : (if result.1=true then 1 else 0)≤1 := by split_ifs <;> omega
  have hFields := fields_bound W (natBits (readCap W N E))
    [i.val,current.2,result.2,8*W,if result.1=true then 1 else 0] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold readCap; have hi := i.isLt; change current.2≤E at hE; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (readCap W N E)+W)+32*W at hFields
  change space t+rationalWordWidth t+GeneralPaperEncodedScalarStorage.fields W
    [i.val,current.2,result.2,8*W,if result.1=true then 1 else 0]+128*W≤_
  change rationalWordWidth t≤1+2*R at hWord
  change space t≤Q at hQ
  unfold readProfile
  omega

def window (model : RationalCostModel) (W : ℕ) (query : ℚ → Bool×ℕ) (space : ℚ → ℕ)
    (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let values := (GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points).1
  GeneralPaperSelectedSearchStorage.window model (GeneralPaperPricedCrossingRefinement.readQuery query W values)
    (readWindow query space W values) W

def profile (model : RationalCostModel) (W n R E Q : ℕ) : ℕ :=
  GeneralPaperSelectedSearchStorage.profile model W (E+8*W) (readProfile W (n+2) R E Q) (n+2)

theorem resources_mono (model : RationalCostModel) (W n N R H E F Q U : ℕ)
    (hn : n≤N) (hr : R≤H) (he : E≤F) (hq : Q≤U) :
    profile model W n R E Q≤profile model W N H F U := by
  unfold profile readProfile readCap GeneralPaperSelectedSearchStorage.profile
    GeneralPaperSelectedSearchStorage.metadataCap GeneralPaperSelectedSearchStorage.workCap GeneralPaperSelectedSearchStorage.depth
    GeneralPaperCeilingConstructionStorage.word GeneralPaperRaySearchStorage.coefficient
    GeneralPaperRaySearchStorage.frameProfile GeneralPaperRaySearchStorage.metadataCap GeneralPaperRaySearchStorage.workCap
    GeneralPaperRankMidpointStorage.profile GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap GeneralPaperBoundedQuotient.heightBudget natBits
  dsimp only
  gcongr <;> (apply model.monotone; gcongr)

theorem ordered_height (lo hi : ℚ) (points : List ℚ) (R : ℕ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R)
    (t : ℚ) (ht : t∈GeneralPaperRaySortedCrossings.ordered lo hi points) : RationalHeight t R := by
  rcases (GeneralPaperRaySortedCrossings.ordered_mem lo hi points t).mp ht with rfl|rfl|⟨ht,_,_⟩
  · exact hl
  · exact hh
  · exact hp t ht

theorem bounded (model : RationalCostModel) (W n R E Q : ℕ) (query : ℚ → Bool×ℕ) (space : ℚ → ℕ)
    (lo hi : ℚ) (points : List ℚ) (hn : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ q∈points,RationalHeight q R)
    (hE : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query q).2≤E)
    (hQ : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,space q≤Q) :
    window model W query space lo hi points≤profile model W n R E Q := by
  let values := (GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points).1
  have hLen : (GeneralPaperRaySortedCrossings.ordered lo hi points).length≤n+2 :=
    (GeneralPaperRaySortedCrossings.ordered_length lo hi points).trans (Nat.add_le_add_right hn 2)
  have hMem (i) : values.read i∈GeneralPaperRaySortedCrossings.ordered lo hi points := by
    simp only [values,GeneralPaperPricedCrossingArray.data]
    exact GeneralPaperRaySortedCrossings.read_mem lo hi points i
  apply GeneralPaperSelectedSearchStorage.bounded model (GeneralPaperPricedCrossingRefinement.readQuery query W values)
    (readWindow query space W values) W (E+8*W) (readProfile W (n+2) R E Q) (n+2) hLen
  · intro i
    exact Nat.add_le_add_right (hE _ (hMem i)) _
  · intro i
    apply read_bounded query space W (n+2) R E Q values i hLen _ (hE _ (hMem i)) (hQ _ (hMem i))
    dsimp only [values]
    rw [GeneralPaperPricedCrossingArray.data]
    exact GeneralPaperRayBracketSize.read_height lo hi points R hl hh hp i

def nativePrice (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  4096*(m+1)*(K+1)*(S+1)*(W+model.rat (1+4*R))

theorem native {m K : ℕ} (model : RationalCostModel) (W D E X V P S h n H : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hScores : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : RationalOrderCell.Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (lo hi : ℚ) (points : List ℚ) (hn : points.length≤n)
    (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (GeneralPaperRayUniformSize.width D E m X V P))
    (hh : RationalHeight hi (GeneralPaperRayUniformSize.width D E m X V P))
    (hp : ∀ q∈points,RationalHeight q (GeneralPaperRayUniformSize.width D E m X V P))
    (hCommon : ∀ t∈GeneralPaperRaySortedCrossings.ordered lo hi points,
      GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m≤H)
    (hCompare : 2*GeneralPaperRayUniformSize.width D E m X V P≤H) (hThreshold : h≤S)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W matrix x w t S) :
    window model W (GeneralPaperRayPredicateBits.run model W matrix x w S h beta)
      (fun t => GeneralPaperRayPredicateStorage.window model W matrix x w S h beta t (phase t)) lo hi points≤
      profile model W n (GeneralPaperRayUniformSize.width D E m X V P)
        (nativePrice model W m K S (GeneralPaperRayUniformSize.width D E m X V P))
        (GeneralPaperRayPredicateStorage.profile model W m K S H) := by
  let R := GeneralPaperRayUniformSize.width D E m X V P
  apply bounded model W n R (nativePrice model W m K S R) (GeneralPaperRayPredicateStorage.profile model W m K S H)
    (GeneralPaperRayPredicateBits.run model W matrix x w S h beta)
    (fun t => GeneralPaperRayPredicateStorage.window model W matrix x w S h beta t (phase t)) lo hi points hn hl hh hp
  · intro t ht
    have hInterval := GeneralPaperRaySortedCrossings.ordered_bound lo hi ho points t ht
    have hHeight := ordered_height lo hi points R hl hh hp t ht
    have hCost := GeneralPaperRayPredicateBits.work model W D E X V P R hD hED matrix x w hx hw beta hb t
      ⟨hLo.trans hInterval.1,hInterval.2.trans hHi⟩ hHeight S h hW hK hM hIndex
    change _≤4096*(m+1)*(K+1)*(S+1)*(W+model.rat (1+2*(R+R))) at hCost
    simpa only [nativePrice,show 1+2*(R+R)=1+4*R by ring] using hCost
  · intro t ht
    have hInterval := GeneralPaperRaySortedCrossings.ordered_bound lo hi ho points t ht
    have hHeight := ordered_height lo hi points R hl hh hp t ht
    apply GeneralPaperRayPredicateStorage.bounded model W D E X V P R S h H hD hED matrix hScores x w hx hw beta hb t
      ⟨hLo.trans hInterval.1,hInterval.2.trans hHi⟩ hHeight (hCommon t ht) _ hThreshold hW hK hM hIndex (phase t)
    change R+R≤H
    omega

end Blotto.GeneralPaperCrossingSearchStorage

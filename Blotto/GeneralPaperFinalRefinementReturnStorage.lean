import Blotto.GeneralPaperHighBlockerStorage

/-! Native final-budget wrapper returns. The complete optional bracket,
batch length, batch/refinement/native parent work and every partial sum
are encoded. Existing checked phases own all batch/table/query buffers. -/
namespace Blotto.GeneralPaperFinalRefinementReturnStorage
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W m K S R : ℕ) : ℕ := GeneralPaperFinalRefinementPrice.profile m S K W (model.rat (6*R+9))
def metadataCap (model : RationalCostModel) (W m K S R : ℕ) : ℕ := S+2+3*price model W m K S R+8*W

def window {m S K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) : ℕ :=
  let points := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  let result := GeneralPaperFinalRefinementPrice.bits model W matrix table x w h beta lo hi
  GeneralPaperCrossingRefinementStorage.bracketFoot W result.1+
    fields W [S,h,points.1.length,points.2,refined.work,result.2,points.2+refined.work,points.2+refined.work+8*W,8*W]+256*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  2*(1+2*R)+64*W+9*(natBits (metadataCap model W m K S R)+W)+288*W

theorem bounded {m S K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V m table)
    (x w : Variable m K → ℚ) (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (h : ℕ) (hhS : h≤S) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ) (hLo : 0≤lo) (ho : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hFinalIndex : binaryWordWidth (S+4)≤W) :
    window model W matrix table x w h beta lo hi≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let points := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  let result := GeneralPaperFinalRefinementPrice.bits model W matrix table x w h beta lo hi
  have hRoots : ∀ t∈points.1,RationalHeight t R := by
    intro t ht
    rw [GeneralPaperBudgetCrossingPrice.data] at ht
    exact GeneralPaperRayUniformSize.budget_roots hD hE le_rfl table hp h beta hb t ht
  have hBracket := GeneralPaperCrossingRefinementStorage.bracket_bound model W R
    (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) lo hi points.1 hl hh hRoots
  change GeneralPaperCrossingRefinementStorage.bracketFoot W result.1≤2*(1+2*R)+64*W at hBracket
  have hWork := GeneralPaperFinalRefinementPrice.bits_work model W D E X V P m hD hE hED le_rfl matrix table hp x w hx hw h beta hb
    lo hi hLo ho hHi hl hh hW hK hM hIndex hFinalIndex
  change result.2≤price model W m K S R at hWork
  have hShape : result.2=points.2+refined.work+8*W := rfl
  have hLength : points.1.length≤S+1 := by rw [GeneralPaperBudgetCrossingPrice.data]; exact GeneralPaperRayBudgetCrossings.batch_length _ _ _
  have hf := fields_bound W (natBits (metadataCap model W m K S R))
    [S,h,points.1.length,points.2,refined.work,result.2,points.2+refined.work,points.2+refined.work+8*W,8*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (metadataCap model W m K S R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [R,points,refined,result] at hBracket hf
  omega

end Blotto.GeneralPaperFinalRefinementReturnStorage

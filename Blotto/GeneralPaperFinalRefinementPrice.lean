import Blotto.GeneralPaperAffineInputPrice

/-! Complete final budget-batch refinement with actual native queries, in
unit and bit models. Its batch cap is S+1, independently of K or tuples.
-/
namespace Blotto.GeneralPaperFinalRefinementPrice
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def envelope (n W P C : ℕ) : ℕ :=
  512*(n+3)*(binaryWordWidth (n+3)+2)^2*(P+W)+(binaryWordWidth (n+3)+1)*C

theorem envelope_mono {n q P Q C F : ℕ} (hn : n≤q) (hp : P≤Q) (hc : C≤F) (W : ℕ) :
    envelope n W P C≤envelope q W Q F := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right hn 3)
  unfold envelope
  gcongr

def profile (m S K W P : ℕ) : ℕ :=
  128*(S+2)*(W+P)+envelope (S+1) W P (4096*(m+1)*(K+1)*(S+1)*(W+P))+8*W

def bits {m S K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) : Option GeneralPaperRayCrossingRefinement.Bracket × ℕ :=
  let points := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  (refined.bracket,points.2+refined.work+8*W)

theorem bits_data {m S K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) :
    (bits model W matrix table x w h beta lo hi).1=GeneralPaperRayFinalBudget.finish matrix table x w h beta lo hi := by
  simp only [bits,GeneralPaperBudgetCrossingPrice.data,GeneralPaperRayBitRefinement.data,GeneralPaperRayFinalBudget.finish]

theorem bits_work {m S K : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (hn : n≤m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (hp : TableBounded D E X V n table) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hLo : 0≤lo) (hOrder : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth (S+4)≤W) :
    (bits model W matrix table x w h beta lo hi).2≤profile m S K W (model.rat (6*width D E m X V P+9)) := by
  let R := width D E m X V P
  let Q := model.rat (6*R+9)
  let points := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  have hSmall := model.monotone (show 1+2*R≤6*R+9 by omega)
  have hLarge := model.monotone (show 1+4*R≤6*R+9 by omega)
  have hGen := (GeneralPaperBudgetCrossingPrice.work model.rat model.monotone W D E m X V P n hD hE hn
    table hp h beta hb).trans (GeneralPaperBudgetCrossingPrice.profile_bound S W (model.rat (1+2*R)))
  have hGen' : points.2≤128*(S+2)*(W+Q) := hGen.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hSmall W))
  have hRoots : ∀ q∈points.1,RationalHeight q R := by
    intro q hq
    rw [GeneralPaperBudgetCrossingPrice.data] at hq
    exact GeneralPaperRayUniformSize.budget_roots hD hE hn table hp h beta hb q hq
  have hLen : points.1.length≤S+1 := by rw [GeneralPaperBudgetCrossingPrice.data]; exact GeneralPaperRayBudgetCrossings.batch_length _ _ _
  have hIndex' := (binaryWordWidth_mono (Nat.add_le_add_right hLen 3)).trans hBatch
  have hRef := GeneralPaperRayBitRefinement.work model W D E X V P hD hED matrix x w hx hw beta hb S h lo hi points.1
    hLo hOrder hHi hl hh hRoots hW hK hM hIndex hIndex'
  have hRef' : refined.work≤envelope (S+1) W Q (4096*(m+1)*(K+1)*(S+1)*(W+Q)) := by
    exact hRef.trans (envelope_mono hLen hSmall
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left hLarge W)) W)
  change points.2+refined.work+8*W≤profile m S K W Q
  unfold profile
  omega

def arithmetic {m S K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) : Option GeneralPaperRayCrossingRefinement.Bracket × ℕ :=
  let points := GeneralPaperBudgetCrossingPrice.run (fun _ => 1) 1 table h beta
  let refined := GeneralPaperPricedCrossingRefinement.run (fun _ => 1) (fun _ => 1) 1
    (GeneralPaperRayPricedPredicate.query matrix x w S h beta) lo hi points.1
  (refined.bracket,points.2+refined.work+8)

theorem arithmetic_data {m S K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) :
    (arithmetic matrix table x w h beta lo hi).1=GeneralPaperRayFinalBudget.finish matrix table x w h beta lo hi := by
  simp only [arithmetic,GeneralPaperBudgetCrossingPrice.data,GeneralPaperPricedCrossingRefinement.data,GeneralPaperRayFinalBudget.finish]

theorem arithmetic_work {m S K : ℕ} (D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (hp : TableBounded D E X V n table) (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    (arithmetic matrix table x w h beta lo hi).2≤profile m S K 1 1 := by
  let R := width D E m X V P
  let Q := 4096*(m+1)*(K+1)*(S+1)*(1+1)
  let points := GeneralPaperBudgetCrossingPrice.run (fun _ => 1) 1 table h beta
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let refined := GeneralPaperPricedCrossingRefinement.run (fun _ => 1) (fun _ => 1) 1 query lo hi points.1
  have hGen := (GeneralPaperBudgetCrossingPrice.work (fun _ => 1) (fun _ _ _ => le_rfl) 1 D E m X V P n hD hE hn
    table hp h beta hb).trans (GeneralPaperBudgetCrossingPrice.profile_bound S 1 1)
  change points.2≤128*(S+2)*(1+1) at hGen
  have hRoots : ∀ q∈points.1,RationalHeight q R := by
    intro q hq
    rw [GeneralPaperBudgetCrossingPrice.data] at hq
    exact GeneralPaperRayUniformSize.budget_roots hD hE hn table hp h beta hb q hq
  have hLen : points.1.length≤S+1 := by rw [GeneralPaperBudgetCrossingPrice.data]; exact GeneralPaperRayBudgetCrossings.batch_length _ _ _
  have hQueries : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points.1,(query q).2≤Q := by
    intro q _
    have hq := GeneralPaperRayPricedPredicate.query_work matrix x w S h beta q
    have hA : 1≤(m+1)*(K+1)*(S+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    dsimp only [Q]
    change (query q).2≤1024*(m+1)*(K+1)*(S+1)+8 at hq
    nlinarith only [hq,hA]
  have hRef := (GeneralPaperPricedCrossingRefinement.arithmetic_work R Q query lo hi points.1 hl hh hRoots hQueries).trans
    (GeneralPaperCrossingPriceEnvelope.refinement_profile points.1.length 1 1 Q)
  have hRef' : refined.work≤envelope (S+1) 1 1 Q := hRef.trans (envelope_mono hLen le_rfl le_rfl 1)
  change points.2+refined.work+8≤_
  unfold profile
  change _≤128*(S+2)*(1+1)+envelope (S+1) 1 1 Q+8
  omega

end Blotto.GeneralPaperFinalRefinementPrice

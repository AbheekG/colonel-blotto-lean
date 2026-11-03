import Blotto.GeneralPaperCrossingGenerationStorage

/-! Complete native final-budget batch generation. The affine table and
budget remain owned through score-iterator construction, all filterMap
frames, one active full candidate and the outer return counters. -/
namespace Blotto.GeneralPaperBudgetGenerationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def candidatePrice (model : RationalCostModel) (W R : ℕ) : ℕ := 80*W+9*model.rat (1+2*R)
def body {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) : List ℚ×ℕ :=
  GeneralPaperPricedListStream.filterMap W (GeneralPaperBudgetCrossingPrice.candidateRun model.rat W table h beta) (List.finRange (S+1))
def bodyWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) (active : Option (Fin (S+1))) : ℕ :=
  GeneralPaperPricedListStreamStorage.filterWindow W (GeneralPaperBudgetCrossingPrice.candidateRun model.rat W table h beta)
    (fun s => GeneralPaperBudgetCandidateStorage.window model W table h beta s) active (List.finRange (S+1))
def bodyProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperPricedListStreamStorage.filterProfile W R (candidatePrice model W R) (S+1) (GeneralPaperBudgetCandidateStorage.profile model W m K S R)

theorem body_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) (h : ℕ) (hh : h≤S)
    (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (active : Option (Fin (S+1))) :
    bodyWindow model W table h beta active≤bodyProfile model W m K S (width D E m X V P) := by
  apply GeneralPaperPricedListStreamStorage.filter_bounded W _ _ (S+1) _ _ _ active (List.finRange (S+1)) (by rw [List.length_finRange])
  · intro s _; exact GeneralPaperBudgetCandidateStorage.candidate_work model W D E m X V P n hD hE hn table hp h beta hb s
  · intro s _ t ht
    rw [GeneralPaperBudgetCrossingPrice.candidate_data] at ht
    exact budget_roots hD hE hn table hp h beta hb t (List.mem_filterMap.mpr ⟨s,List.mem_finRange s,ht⟩)
  · intro s _; exact GeneralPaperBudgetCandidateStorage.bounded model W D E m X V P n hD hE hn table hp h hh beta hb s
  · intro s _; exact List.mem_finRange s

def callerCap (model : RationalCostModel) (W S R : ℕ) : ℕ := S+1+GeneralPaperBudgetCrossingPrice.profile S W (model.rat (1+2*R))
def caller {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) : ℕ :=
  let result := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let current := body model W table h beta
  fields W [S,h,result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W]+256*W
def callerProfile (model : RationalCostModel) (W S R : ℕ) : ℕ := 7*(natBits (callerCap model W S R)+W)+288*W

theorem caller_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) (h : ℕ) (hh : h≤S)
    (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) : caller model W table h beta≤callerProfile model W S (width D E m X V P) := by
  let R := width D E m X V P
  let result := GeneralPaperBudgetCrossingPrice.run model.rat W table h beta
  let current := body model W table h beta
  have hWork := GeneralPaperBudgetCrossingPrice.work model.rat model.monotone W D E m X V P n hD hE hn table hp h beta hb
  change result.2≤GeneralPaperBudgetCrossingPrice.profile S W (model.rat (1+2*R)) at hWork
  have hLen : result.1.length≤S+1 := by dsimp only [result]; rw [GeneralPaperBudgetCrossingPrice.data]; exact GeneralPaperRayBudgetCrossings.batch_length table h beta
  have hShape : result.2=current.2+16*(S+2)*W := rfl
  have hFields := fields_bound W (natBits (callerCap model W S R))
    [S,h,result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (callerCap model W S R)+W)+32*W at hFields
  change GeneralPaperEncodedScalarStorage.fields W [S,h,result.1.length,current.2,result.2,16*(S+2)*W,current.2+16*(S+2)*W]+256*W≤callerProfile model W S R
  unfold callerProfile
  omega

def window {S K : ℕ} (model : RationalCostModel) (W copied : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) (active : Option (Fin (S+1))) : ℕ :=
  GeneralPaperAffineWitnessStorage.tableFoot W table+rationalWordWidth beta+GeneralPaperFinRangeStorage.window W (S+1) copied+
    bodyWindow model W table h beta active+caller model W table h beta
def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperAffineWitnessStorage.tableProfile W S K m R+(1+2*R)+GeneralPaperFinRangeStorage.profile W (S+1)+
    bodyProfile model W m K S R+callerProfile model W S R

theorem bounded {S K : ℕ} (model : RationalCostModel) (W copied D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) (h : ℕ) (hh : h≤S)
    (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (active : Option (Fin (S+1))) :
    window model W copied table h beta active≤profile model W m K S (width D E m X V P) := by
  have hTable := GeneralPaperAffineWitnessStorage.table_bound W D E X V n m P hD hE hn table hp
  have hBeta := rationalWordWidth_of_height (GeneralPaperRayOperandStorageHeight.budget (E:=E) (m:=m) (X:=X) (V:=V) hD hb)
  have hRange := GeneralPaperFinRangeStorage.bounded W (S+1) copied
  have hBody := body_bounded model W D E m X V P n hD hE hn table hp h hh beta hb active
  have hCaller := caller_bounded model W D E m X V P n hD hE hn table hp h hh beta hb
  unfold window profile
  omega

end Blotto.GeneralPaperBudgetGenerationStorage

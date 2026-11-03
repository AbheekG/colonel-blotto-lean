import Blotto.GeneralPaperFixedTupleDecodeStorage

/-! Actual fixed-table violation candidate. Complete loaded/returned
witnesses, affine evaluation/comparison scratch and encoded native guard/
return fields are counted. Only a high-score present cell evaluates. -/
namespace Blotto.GeneralPaperFixedViolationCandidateStorage
open RationalOrderCell GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperRayFixedViolation GeneralPaperAffineWitnessStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def Good {S K : ℕ} (m R : ℕ) (table : Table S K) : Prop :=
  ∀ s c,table.read s=some c → c.labels.length≤m ∧ RationalHeight c.expression.intercept R ∧ RationalHeight c.expression.slope R

theorem processed_good {S K : ℕ} (D E X V n m P : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) :
    Good m (GeneralPaperRayUniformSize.width D E m X V P) table := by
  let A := GeneralPaperRayUniformSize.interceptCap m X P
  let B := GeneralPaperRayUniformSize.slopeCap m V
  have hCaps := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
  have hR : GeneralPaperRayAffineBound.rootWidth D E A B≤GeneralPaperRayUniformSize.width D E m X V P :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  intro s c hc
  have h := GeneralPaperAffineValuePrice.coefficients hD hE c.expression (hCaps s c hc)
  exact ⟨(hp s c hc).2.le.trans hn,h.1.mono hR,h.2.mono hR⟩

def entryFoot {S K : ℕ} (W : ℕ) : Option (Entry S K) → ℕ
  | none => 1
  | some e => 1+natBits e.1.val+choiceFoot W e.2+32*W

def entryProfile (W m K S R : ℕ) : ℕ := 1+natBits S+choiceProfile W K m R+32*W

theorem entry_bound {S K : ℕ} (W m R : ℕ) (table : Table S K) (hp : Good m R table)
    (a : Option (Entry S K)) (ha : ∀ e,a=some e → table.read e.1=some e.2) :
    entryFoot W a≤entryProfile W m K S R := by
  cases a with
  | none => dsimp only [entryFoot,entryProfile]; omega
  | some e =>
    have h := hp e.1 e.2 (ha e rfl)
    have hChoice := choice_bound W m R e.2 h.1 h.2.1 h.2.2
    have hs := Nat.add_le_add_left (binaryWordWidth_mono (show e.1.val≤S by have h := e.1.isLt; omega)) 1
    change natBits e.1.val≤natBits S at hs
    dsimp only [entryFoot,entryProfile]
    omega

def price (model : RationalCostModel) (R u : ℕ) : ℕ := GeneralPaperAffineValueStorage.price model R u
def cap (model : RationalCostModel) (W R u : ℕ) : ℕ := 48*W+5*price model R u

def compare {K : ℕ} (model : RationalCostModel) (W : ℕ) (c : Choice K) (beta t : ℚ) : ℕ :=
  model.rat (RationalExpression.pairWidth (GeneralPaperAffineValuePrice.run model.rat W c.expression t).1 beta)

theorem compare_bound {K : ℕ} (model : RationalCostModel) (W R u : ℕ) (c : Choice K) (beta t : ℚ)
    (hi : RationalHeight c.expression.intercept R) (hs : RationalHeight c.expression.slope R)
    (hb : RationalHeight beta R) (ht : RationalHeight t u) : compare model W c beta t≤price model R u :=
  model.monotone (max_le (rationalWordWidth_of_height (GeneralPaperAffineValueStorage.operands R u c.expression t hi hs ht).2.2)
    (rationalWordWidth_of_height (hb.mono (show R≤GeneralPaperAffineValueStorage.height R u by unfold GeneralPaperAffineValueStorage.height; omega))))

theorem work {S K : ℕ} (model : RationalCostModel) (W m R u : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u) (s : Fin (S+1)) :
    (GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s).2≤cap model W R u := by
  unfold GeneralPaperFixedViolationPrice.candidateRun
  split
  · cases he : table.read s with
    | none => dsimp only; unfold cap; omega
    | some c =>
      have hc := hp s c he
      have hv := GeneralPaperAffineValueStorage.work model W R u c.expression t hc.2.1 hc.2.2 ht
      have hCompare := compare_bound model W R u c beta t hc.2.1 hc.2.2 hb ht
      change (GeneralPaperAffineValuePrice.run model.rat W c.expression t).2+32*W+compare model W c beta t≤_
      unfold cap price GeneralPaperAffineValueStorage.workCap at *
      omega
  · dsimp only; unfold cap; omega

def evaluationWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) (s : Fin (S+1)) : ℕ :=
  if h<s.val then match table.read s with
    | none => 0
    | some c =>
      let value := GeneralPaperAffineValuePrice.run model.rat W c.expression t
      let comparison := compare model W c beta t
      GeneralPaperAffineValueStorage.window model W c.expression t+comparison+
        fields W [value.2,comparison,value.2+32*W,value.2+32*W+comparison]+128*W
  else 0

def evaluationProfile (model : RationalCostModel) (W R u : ℕ) : ℕ :=
  GeneralPaperAffineValueStorage.profile model W R u+price model R u+4*(natBits (1+cap model W R u)+W)+160*W

theorem evaluation_bound {S K : ℕ} (model : RationalCostModel) (W m R u : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u) (s : Fin (S+1)) :
    evaluationWindow model W table h beta t s≤evaluationProfile model W R u := by
  unfold evaluationWindow
  split
  · cases he : table.read s with
    | none => dsimp only; omega
    | some c =>
      let value := GeneralPaperAffineValuePrice.run model.rat W c.expression t
      let comparison := compare model W c beta t
      have hc := hp s c he
      have hv := GeneralPaperAffineValueStorage.bounded model W R u c.expression t hc.2.1 hc.2.2 ht
      have hWork := GeneralPaperAffineValueStorage.work model W R u c.expression t hc.2.1 hc.2.2 ht
      change value.2≤GeneralPaperAffineValueStorage.workCap model W R u at hWork
      have hCompare := compare_bound model W R u c beta t hc.2.1 hc.2.2 hb ht
      change comparison≤price model R u at hCompare
      have hf := fields_bound W (natBits (1+cap model W R u)) [value.2,comparison,value.2+32*W,value.2+32*W+comparison] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl
        all_goals unfold cap price GeneralPaperAffineValueStorage.workCap at *; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (1+cap model W R u)+W)+32*W at hf
      change GeneralPaperAffineValueStorage.window model W c.expression t+comparison+
        GeneralPaperEncodedScalarStorage.fields W [value.2,comparison,value.2+32*W,value.2+32*W+comparison]+128*W≤_
      unfold evaluationProfile
      omega
  · omega

def metadataCap (model : RationalCostModel) (W S R u : ℕ) : ℕ := S+1+cap model W R u+32*W

def window {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta t : ℚ) (s : Fin (S+1)) : ℕ :=
  let result := GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s
  optionChoiceFoot W (table.read s)+entryFoot W result.1+rationalWordWidth beta+rationalWordWidth t+
    fields W [S,h,s.val,32*W,result.2]+128*W+evaluationWindow model W table h beta t s

def profile (model : RationalCostModel) (W m K S R u : ℕ) : ℕ :=
  optionChoiceProfile W K m R+entryProfile W m K S R+(1+2*R)+(1+2*u)+
    5*(natBits (metadataCap model W S R u)+W)+160*W+evaluationProfile model W R u

theorem bounded {S K : ℕ} (model : RationalCostModel) (W m R u : ℕ) (table : Table S K) (hp : Good m R table)
    (h : ℕ) (hhS : h≤S) (beta t : ℚ) (hb : RationalHeight beta R) (ht : RationalHeight t u) (s : Fin (S+1)) :
    window model W table h beta t s≤profile model W m K S R u := by
  let result := GeneralPaperFixedViolationPrice.candidateRun model.rat W table h beta t s
  have hLoaded := option_choice_bound W m R (table.read s) (hp s)
  have hEntry := entry_bound W m R table hp result.1 (by
    intro e he
    rw [GeneralPaperFixedViolationPrice.candidate_data] at he
    exact (GeneralPaperRayFixedViolation.candidate_valid table h beta t s e he).2.1)
  have hBeta := rationalWordWidth_of_height hb
  have hSample := rationalWordWidth_of_height ht
  have hWork := work model W m R u table hp h beta t hb ht s
  change result.2≤cap model W R u at hWork
  have hs := s.isLt
  have hf := fields_bound W (natBits (metadataCap model W S R u)) [S,h,s.val,32*W,result.2] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W S R u)+W)+32*W at hf
  have hEval := evaluation_bound model W m R u table hp h beta t hb ht s
  change optionChoiceFoot W (table.read s)+entryFoot W result.1+rationalWordWidth beta+rationalWordWidth t+
    GeneralPaperEncodedScalarStorage.fields W [S,h,s.val,32*W,result.2]+128*W+evaluationWindow model W table h beta t s≤_
  unfold profile
  omega

end Blotto.GeneralPaperFixedViolationCandidateStorage

import Blotto.GeneralPaperAffineCandidatePairStorage

/-! One actual final-budget crossing candidate, including score guard,
loaded whole affine witness, constant budget expression, guarded crossing,
returned root and both caller/primitive work counters. The affine table is
borrowed and is counted by its enclosing generation scope. -/
namespace Blotto.GeneralPaperBudgetCandidateStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage GeneralPaperRayAffine
open GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def stored {S K : ℕ} (table : Table S K) (h : ℕ) (s : Fin (S+1)) : Option (Choice K) := if h<s.val then table.read s else none

def metadataCap (model : RationalCostModel) (W S R : ℕ) : ℕ := S+1+80*W+9*model.rat (1+2*R)

def window {S K : ℕ} (model : RationalCostModel) (W : ℕ) (table : Table S K) (h : ℕ) (beta : ℚ) (s : Fin (S+1)) : ℕ :=
  let constant := GeneralPaperRayBudgetCrossings.constant beta
  let result := GeneralPaperBudgetCrossingPrice.candidateRun model.rat W table h beta s
  optionChoiceFoot W (stored table h s)+affineFoot W constant+GeneralPaperAffineArithmeticStorage.rootFoot W result.1+
    fields W [h,s.val,result.2,16*W]+256*W+
    match stored table h s with
    | none => 0
    | some c =>
      let root := GeneralPaperAffineCrossingPrice.run model.rat W constant c.expression
      GeneralPaperAffineArithmeticStorage.crossingWindow model W constant c.expression+
        fields W [root.2,root.2+16*W]+128*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  optionChoiceProfile W K m R+affineProfile W R+GeneralPaperAffineArithmeticStorage.rootProfile W R+
    GeneralPaperAffineArithmeticStorage.crossingProfile model W R+6*(natBits (metadataCap model W S R)+W)+448*W

theorem candidate_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (s : Fin (S+1)) :
    (GeneralPaperBudgetCrossingPrice.candidateRun model.rat W table h beta s).2≤80*W+9*model.rat (1+2*width D E m X V P) := by
  let A := interceptCap m X P
  let B := slopeCap m V
  have hP : P≤A := by dsimp only [A]; unfold interceptCap; nlinarith
  have hConst : GeneralPaperRayAffineBound.Bounded D E A B (GeneralPaperRayBudgetCrossings.constant beta) :=
    ⟨hb.mono hP,(GeneralPaperRayRationalBound.Bounded.zero E).mono (Nat.zero_le _)⟩
  have hTable := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
  unfold GeneralPaperBudgetCrossingPrice.candidateRun
  split
  · cases he : table.read s with
    | none => dsimp only; omega
    | some c =>
      have hr := GeneralPaperAffineCrossingPrice.work model.rat model.monotone W D E A B (width D E m X V P)
        hD hE le_rfl (GeneralPaperRayBudgetCrossings.constant beta) c.expression hConst (hTable s c he)
      change (GeneralPaperAffineCrossingPrice.run model.rat W (GeneralPaperRayBudgetCrossings.constant beta) c.expression).2+16*W≤_
      omega
  · dsimp only; omega

theorem bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) (h : ℕ) (hh : h≤S) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (s : Fin (S+1)) :
    window model W table h beta s≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let A := interceptCap m X P
  let B := slopeCap m V
  let constant := GeneralPaperRayBudgetCrossings.constant beta
  let result := GeneralPaperBudgetCrossingPrice.candidateRun model.rat W table h beta s
  have hP : P≤A := by dsimp only [A]; unfold interceptCap; nlinarith
  have hConst : GeneralPaperRayAffineBound.Bounded D E A B constant :=
    ⟨hb.mono hP,(GeneralPaperRayRationalBound.Bounded.zero E).mono (Nat.zero_le _)⟩
  have hBase : GeneralPaperRayAffineBound.rootWidth D E A B≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hConstHeight := GeneralPaperAffineValuePrice.coefficients hD hE constant hConst
  have hConstant := affine_bound W R constant (hConstHeight.1.mono hBase) (hConstHeight.2.mono hBase)
  have hStored := processed_option_bound W D E X V n m P hD hE hn (stored table h s) (by
    intro c hc
    unfold stored at hc
    split at hc
    · exact hp s c hc
    · contradiction)
  change optionChoiceFoot W (stored table h s)≤optionChoiceProfile W K m R at hStored
  have hRoot := GeneralPaperAffineArithmeticStorage.root_bound W R result.1 (by
    intro t ht
    rw [GeneralPaperBudgetCrossingPrice.candidate_data] at ht
    have hm : t∈GeneralPaperRayBudgetCrossings.batch table h beta := by
      exact List.mem_filterMap.mpr ⟨s,List.mem_finRange s,ht⟩
    exact budget_roots hD hE hn table hp h beta hb t hm)
  have hWork := candidate_work model W D E m X V P n hD hE hn table hp h beta hb s
  change result.2≤80*W+9*model.rat (1+2*R) at hWork
  have hFields := fields_bound W (natBits (metadataCap model W S R)) [h,s.val,result.2,16*W] (by
    intro t ht
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; have hs := s.isLt; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap model W S R)+W)+32*W at hFields
  have hInner : (match stored table h s with
      | none => 0
      | some c => let root := GeneralPaperAffineCrossingPrice.run model.rat W constant c.expression
        GeneralPaperAffineArithmeticStorage.crossingWindow model W constant c.expression+fields W [root.2,root.2+16*W]+128*W)≤
      GeneralPaperAffineArithmeticStorage.crossingProfile model W R+2*(natBits (metadataCap model W S R)+W)+160*W := by
    cases ht : stored table h s with
    | none => simp only; omega
    | some c =>
      have hCell : table.read s=some c := by
        unfold stored at ht
        split at ht
        · exact ht
        · contradiction
      have hTable := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
      have hCross := GeneralPaperAffineArithmeticStorage.crossing_bounded model W D E A B R hD hE le_rfl constant c.expression hConst (hTable s c hCell)
      let root := GeneralPaperAffineCrossingPrice.run model.rat W constant c.expression
      have hr := GeneralPaperAffineCrossingPrice.work model.rat model.monotone W D E A B R hD hE le_rfl constant c.expression hConst (hTable s c hCell)
      change root.2≤64*W+9*model.rat (1+2*R) at hr
      have hf := fields_bound W (natBits (metadataCap model W S R)) [root.2,root.2+16*W] (by
        intro t hmem
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with rfl|rfl <;> unfold metadataCap <;> omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (metadataCap model W S R)+W)+32*W at hf
      change GeneralPaperAffineArithmeticStorage.crossingWindow model W constant c.expression+GeneralPaperEncodedScalarStorage.fields W [root.2,root.2+16*W]+128*W≤_
      omega
  have hPrefix : optionChoiceFoot W (stored table h s)+affineFoot W constant+GeneralPaperAffineArithmeticStorage.rootFoot W result.1+
      GeneralPaperEncodedScalarStorage.fields W [h,s.val,result.2,16*W]+256*W≤
      optionChoiceProfile W K m R+affineProfile W R+GeneralPaperAffineArithmeticStorage.rootProfile W R+
        4*(natBits (metadataCap model W S R)+W)+288*W := by omega
  exact (Nat.add_le_add hPrefix hInner).trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperBudgetCandidateStorage

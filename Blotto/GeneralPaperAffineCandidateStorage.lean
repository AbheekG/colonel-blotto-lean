import Blotto.GeneralPaperAffineArithmeticStorage

/-! Actual affine predecessor construction and its expression-only wrapper.
The full loaded/returned witnesses and native add scratch are counted before
the expression map discards labels. Field/table owners remain caller-owned.
All lengths and heights follow from the processed-field invariant. -/
namespace Blotto.GeneralPaperAffineCandidateStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage GeneralPaperRayAffine
open GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def stored {S K : ℕ} (field : Field K) (previous : Table S K) (s : Fin (S+1)) (l : Fin K) : Option (Choice K) :=
  if h : (field.read l).1≤s.val then previous.read ⟨s.val-(field.read l).1,by omega⟩ else none

theorem stored_bounded {S K : ℕ} (D E X V n : ℕ) (field : Field K) (previous : Table S K)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (l : Fin K)
    (c : Choice K) (hc : stored field previous s l=some c) : GeneralPaperRayAffineDPSize.ChoiceBounded D E X V n c := by
  unfold stored at hc
  split at hc
  · exact hp _ c hc
  · contradiction

def additionWork {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) (l : Fin K) : ℕ :=
  match stored field previous s l with
  | none => 0
  | some c => (GeneralPaperAffineValuePrice.addRun model.rat W (field.read l).2 c.expression).2

def additionWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) (l : Fin K) : ℕ :=
  match stored field previous s l with
  | none => 0
  | some c => GeneralPaperAffineArithmeticStorage.addWindow model W (field.read l).2 c.expression

def metadataCap (model : RationalCostModel) (W m K S R : ℕ) : ℕ := m+K+S+1+104*W+4*model.rat (1+2*R)

def window {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) (l : Fin K) : ℕ :=
  let result := GeneralPaperAffineCandidatePrice.run model.rat W field previous s l
  let tail := stored field previous s l
  let add := additionWork model W field previous s l
  optionChoiceFoot W result.1+optionChoiceFoot W tail+natBits (field.read l).1+affineFoot W (field.read l).2+32*W+
    additionWindow model W field previous s l+
    fields W [s.val,l.val,(field.read l).1,s.val-(field.read l).1,result.2,add,64*W,64*W+add]+256*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  2*optionChoiceProfile W K m R+natBits S+affineProfile W R+32*W+GeneralPaperAffineArithmeticStorage.addProfile model W R+
    8*(natBits (metadataCap model W m K S R)+W)+288*W

theorem bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (l : Fin K) : window model W field previous s l≤profile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let A := interceptCap m X P
  let B := slopeCap m V
  let result := GeneralPaperAffineCandidatePrice.run model.rat W field previous s l
  let tail := stored field previous s l
  let add := additionWork model W field previous s l
  have hField := GeneralPaperNativeAffinePrices.field_cap D E m X V P (by omega) field hf
  have hPrevious := GeneralPaperNativeAffinePrices.table_cap D E m X V P n (by omega) previous hp
  have hBase : GeneralPaperRayAffineBound.rootWidth D E A B≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hResult := processed_option_bound W D E X V (n+1) m P hD hE hn result.1 (by
    intro c hc
    rw [GeneralPaperAffineCandidatePrice.data] at hc
    exact GeneralPaperRayAffineDPSize.candidate D E X V n field previous hf hp s l c hc)
  have hTail := processed_option_bound W D E X V n m P hD hE (by omega) tail
    (fun c hc => stored_bounded D E X V n field previous hp s l c hc)
  change optionChoiceFoot W result.1≤optionChoiceProfile W K m R at hResult
  change optionChoiceFoot W tail≤optionChoiceProfile W K m R at hTail
  have hFieldHeight := GeneralPaperAffineValuePrice.coefficients hD hE (field.read l).2 (hField l)
  have hFieldFoot := affine_bound W R (field.read l).2 (hFieldHeight.1.mono hBase) (hFieldHeight.2.mono hBase)
  have hAdd : additionWindow model W field previous s l≤GeneralPaperAffineArithmeticStorage.addProfile model W R := by
    cases ht : stored field previous s l with
    | none => simp only [additionWindow,ht]; omega
    | some c =>
      have hStored := stored_bounded D E X V n field previous hp s l c ht
      have hCap := scale_caps m X V P n (by omega)
      have hCB := GeneralPaperRayAffineBound.mono hStored.1 hCap.1 hCap.2
      have hCH := GeneralPaperAffineValuePrice.coefficients hD hE c.expression hCB
      have hSum := GeneralPaperAffineValuePrice.coefficients hD hE _ (GeneralPaperRayAffineBound.add (hField l) hCB)
      simp only [additionWindow,ht]
      exact GeneralPaperAffineArithmeticStorage.add_bounded model W R _ _
        ⟨hFieldHeight.1.mono hBase,hFieldHeight.2.mono hBase⟩ ⟨hCH.1.mono hBase,hCH.2.mono hBase⟩ hSum
  have hWork := GeneralPaperAffineCandidatePrice.work model.rat model.monotone W D E A B R hD hE le_rfl field previous hField hPrevious s l
  change result.2≤96*W+4*model.rat (1+2*R) at hWork
  have hShape : result.2=64*W+add := by
    dsimp only [result,add,additionWork,stored,GeneralPaperAffineCandidatePrice.run]
    split
    · cases previous.read ⟨s.val-(field.read l).1,by omega⟩ <;> rfl
    · rfl
  have hSub : s.val-(field.read l).1≤S := (Nat.sub_le _ _).trans (by omega)
  have hScore := Nat.add_le_add_left (binaryWordWidth_mono (hScores l)) 1
  have hFields := fields_bound W (natBits (metadataCap model W m K S R))
    [s.val,l.val,(field.read l).1,s.val-(field.read l).1,result.2,add,64*W,64*W+add] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; have hs := s.isLt; have hl := l.isLt; have hscore := hScores l; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap model W m K S R)+W)+32*W at hFields
  change optionChoiceFoot W result.1+optionChoiceFoot W tail+natBits (field.read l).1+affineFoot W (field.read l).2+32*W+
    additionWindow model W field previous s l+GeneralPaperEncodedScalarStorage.fields W
      [s.val,l.val,(field.read l).1,s.val-(field.read l).1,result.2,add,64*W,64*W+add]+256*W≤profile model W m K S R
  unfold profile
  change natBits (field.read l).1≤natBits S at hScore
  omega

def expressionWindow {S K : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (previous : Table S K) (s : Fin (S+1)) (l : Fin K) : ℕ :=
  let candidate := GeneralPaperAffineCandidatePrice.run model.rat W field previous s l
  let result := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s l
  window model W field previous s l+optionAffineFoot W result.1+fields W [candidate.2,result.2,8*W]+128*W

def expressionProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  profile model W m K S R+optionAffineProfile W R+3*(natBits (metadataCap model W m K S R)+W)+160*W

theorem expression_bounded {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (hScores : ∀ l,(field.read l).1≤S)
    (s : Fin (S+1)) (l : Fin K) :
    expressionWindow model W field previous s l≤expressionProfile model W m K S (width D E m X V P) := by
  let R := width D E m X V P
  let candidate := GeneralPaperAffineCandidatePrice.run model.rat W field previous s l
  let result := GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s l
  have hCandidate := bounded model W D E m X V P n hD hE hn field previous hf hp hScores s l
  change window model W field previous s l≤profile model W m K S R at hCandidate
  have hOutput := option_affine_bound W R result.1 (by
    intro f hc
    rw [GeneralPaperNativeAffinePrices.expression_data] at hc
    obtain ⟨c,hc,he⟩ := Option.map_eq_some_iff.mp hc
    rw [←he]
    have hb := GeneralPaperRayAffineDPSize.candidate D E X V n field previous hf hp s l c hc
    have hCap := scale_caps m X V P (n+1) hn
    have hHeight := GeneralPaperAffineValuePrice.coefficients hD hE c.expression (GeneralPaperRayAffineBound.mono hb.1 hCap.1 hCap.2)
    have hBase : GeneralPaperRayAffineBound.rootWidth D E (interceptCap m X P) (slopeCap m V)≤R :=
      GeneralPaperRayAffineBound.rootWidth_mono D E _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact ⟨hHeight.1.mono hBase,hHeight.2.mono hBase⟩)
  have hWork := GeneralPaperAffineCandidatePrice.work model.rat model.monotone W D E (interceptCap m X P) (slopeCap m V) R
    hD hE le_rfl field previous (GeneralPaperNativeAffinePrices.field_cap D E m X V P (by omega) field hf)
    (GeneralPaperNativeAffinePrices.table_cap D E m X V P n (by omega) previous hp) s l
  change candidate.2≤96*W+4*model.rat (1+2*R) at hWork
  have hShape : result.2=candidate.2+8*W := rfl
  have hFields := fields_bound W (natBits (metadataCap model W m K S R)) [candidate.2,result.2,8*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> unfold metadataCap <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (metadataCap model W m K S R)+W)+32*W at hFields
  change window model W field previous s l+optionAffineFoot W result.1+GeneralPaperEncodedScalarStorage.fields W [candidate.2,result.2,8*W]+128*W≤expressionProfile model W m K S R
  unfold expressionProfile
  omega

theorem expression_caps {S K : ℕ} (primitive : ℕ → ℕ) (W D E m X V P n : ℕ) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (l : Fin K) (f : Affine)
    (hc : (GeneralPaperNativeAffinePrices.expressionRun primitive W field previous s l).1=some f) :
    GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V) f := by
  rw [GeneralPaperNativeAffinePrices.expression_data] at hc
  obtain ⟨c,hc,he⟩ := Option.map_eq_some_iff.mp hc
  rw [←he]
  have hb := GeneralPaperRayAffineDPSize.candidate D E X V n field previous hf hp s l c hc
  have hCap := scale_caps m X V P (n+1) hn
  exact GeneralPaperRayAffineBound.mono hb.1 hCap.1 hCap.2

theorem expression_work {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : Field K) (previous : Table S K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous) (s : Fin (S+1)) (l : Fin K) :
    (GeneralPaperNativeAffinePrices.expressionRun model.rat W field previous s l).2≤104*W+4*model.rat (1+2*width D E m X V P) := by
  have h := GeneralPaperAffineCandidatePrice.work model.rat model.monotone W D E (interceptCap m X P) (slopeCap m V) (width D E m X V P)
    hD hE le_rfl field previous (GeneralPaperNativeAffinePrices.field_cap D E m X V P (by omega) field hf)
    (GeneralPaperNativeAffinePrices.table_cap D E m X V P n (by omega) previous hp) s l
  change (GeneralPaperAffineCandidatePrice.run model.rat W field previous s l).2+8*W≤_
  omega

end Blotto.GeneralPaperAffineCandidateStorage

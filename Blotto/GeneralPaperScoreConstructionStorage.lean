import Blotto.GeneralPaperScoreScanStorage

/-! A native exact-score layer retains one previous table, reserves one
new table, and invokes one recursive label scan at a time. Constructor
frames include actual prefix-work counters; rational scratch is the scan's
separate primitive maximum. No complete DP time is used as working space. -/
namespace Blotto.GeneralPaperScoreConstructionStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreSelectionStorage GeneralPaperScoreTableStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem fill_work_mono {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (callback : Fin n → α×ℕ)
    (a b : ℕ) (ha : a≤n) (hb : b≤n) (hab : a≤b) :
    (PaperIndexedArrayConstruction.fill primitive A callback a ha).2≤
      (PaperIndexedArrayConstruction.fill primitive A callback b hb).2 := by
  induction b generalizing a with
  | zero =>
    have he : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases he : a=b+1
    · subst a; exact Nat.le_refl _
    · have hPrev := ih a ha (by omega) (by omega)
      apply hPrev.trans
      rw [PaperIndexedArrayConstruction.fill]
      dsimp only
      omega

def constructorFrames {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A W : ℕ)
    (callback : Fin n → α×ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  ∑ i : Fin (count+1), (fields W [i.val,(PaperIndexedArrayConstruction.fill primitive A callback i.val (by omega)).2]+128*W)

def constructorProfile (W n C : ℕ) : ℕ := (n+1)*(2*(natBits (n+C)+W)+160*W)

theorem two_fields_bound (W C a b : ℕ) (ha : a≤C) (hb : b≤C) :
    fields W [a,b]≤2*(natBits C+W)+32*W := by
  have hA := binaryWordWidth_mono ha
  have hB := binaryWordWidth_mono hb
  simp only [GeneralPaperEncodedScalarStorage.fields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,natBits]
  omega

theorem constructor_bound {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A W C : ℕ)
    (callback : Fin n → α×ℕ) (hw : (PaperIndexedArrayConstruction.run primitive A callback).2≤C)
    (count : ℕ) (hc : count≤n) : constructorFrames primitive A W callback count hc≤constructorProfile W n C := by
  have he (i : Fin (count+1)) :
      fields W [i.val,(PaperIndexedArrayConstruction.fill primitive A callback i.val (Nat.le_trans (Nat.le_of_lt_succ i.isLt) hc)).2]+128*W≤
        2*(natBits (n+C)+W)+160*W := by
    have hi : i.val≤n := (Nat.le_of_lt_succ i.isLt).trans hc
    have hp : (PaperIndexedArrayConstruction.fill primitive A callback i.val hi).2≤C :=
      (fill_work_mono primitive A callback i.val n hi le_rfl hi).trans hw
    have hf := two_fields_bound W (n+C) i.val (PaperIndexedArrayConstruction.fill primitive A callback i.val hi).2
      (by omega) (hp.trans (Nat.le_add_left _ _))
    exact (Nat.add_le_add_right hf (128*W)).trans_eq (by ring)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  exact hs.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))

def stepWindow {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (rest : List (Field K))
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (xs : List (Fin K)) : ℕ :=
  let previous := GeneralPaperScoreDPBits.runWithBits model W S rest
  let evaluate := GeneralPaperScoreBitPrimitive.candidateRun model W field previous.1 s
  let callback := fun t => GeneralPaperScoreBitPrimitive.scanRun model W
    (GeneralPaperScoreBitPrimitive.candidateRun model W field previous.1 t) (List.finRange K)
  tableFootprint W previous.1+
    reservedFootprint W (S+1) (optionFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W callback count hc).1+
    GeneralPaperScoreScanStorage.trace model W evaluate xs+GeneralPaperScoreScanStorage.primitivePeak model W evaluate xs+
    constructorFrames (fun w => w) W W callback count hc+
    listFootprint W labelBits (List.finRange K)+fields W [S,K,count,s.val]+128*W

def stepProfile (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  let P := GeneralPaperScoreBitPrimitive.resourceWidth A r
  let Q := model.rat P
  2*tableProfile W K S r P+GeneralPaperScoreScanStorage.profile W K r P (64*W+2*Q) Q+
    constructorProfile W (S+1) (GeneralPaperScoreDPBits.stepProfile K S W Q)+
    K*(1+binaryWordWidth K+2*W)+32*W+4*(natBits (S+K+1)+W)+32*W+128*W

theorem step_bound {K S : ℕ} (model : RationalCostModel) (W A r : ℕ)
    (field : Field K) (rest : List (Field K)) (hFields : CostHeight (field::rest) A)
    (hLen : rest.length+1≤r) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (xs : List (Fin K)) (hXs : xs.length≤K) :
    stepWindow model W field rest count hc s xs≤stepProfile model W K S A r := by
  have hRest : CostHeight rest A := fun f hf => hFields f (List.mem_cons_of_mem _ hf)
  have hPrevious := native_return model W S A r rest hRest (by omega)
  have hPrefix := GeneralPaperScoreTableStorage.step_prefix model W A r field rest hFields hLen count hc
  have hScan := GeneralPaperScoreScanStorage.native_bound model W A r field rest hFields hLen s xs hXs
  have hStep := (GeneralPaperScoreDPBits.step_work model W A field rest hFields hW hIndex).trans
    (GeneralPaperScoreDPBits.stepProfile_mono K S W (model.monotone
      (GeneralPaperScoreBitPrimitive.resourceWidth_mono A hLen)))
  have hFrames := constructor_bound (fun w => w) W W
    (GeneralPaperScoreDPBits.stepProfile K S W (model.rat (GeneralPaperScoreBitPrimitive.resourceWidth A r)))
    (fun t => GeneralPaperScoreBitPrimitive.scanRun model W
      (GeneralPaperScoreBitPrimitive.candidateRun model W field (run S rest) t) (List.finRange K)) hStep count hc
  have hLabels := list_bound W (1+binaryWordWidth K) labelBits (List.finRange K) (fun l _ => label_bound l)
  simp only [List.length_finRange] at hLabels
  have hControls := fields_bound W (natBits (S+K+1)) [S,K,count,s.val] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals have hs := s.isLt; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (S+K+1)+W)+32*W at hControls
  unfold stepWindow
  simp only [GeneralPaperScoreDPBits.run_data] at hPrevious ⊢
  dsimp only at hScan
  dsimp only [stepProfile]
  omega

@[fun_prop]
theorem constructor_profile_scale (n C : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => constructorProfile W n C) := by
  unfold constructorProfile
  fun_prop

end Blotto.GeneralPaperScoreConstructionStorage

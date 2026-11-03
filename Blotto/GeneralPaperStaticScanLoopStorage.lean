import Blotto.GeneralPaperStaticChoiceStorage

/-! Actual static minimum loop frames, current/returned blockers, literal
candidate/pick windows and native accumulated-work fields. One active row
residual is reserved separately. Structural recursion is conservatively
counted without relying on generated-runtime tail-call or release behavior. -/
namespace Blotto.GeneralPaperStaticScanLoopStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayMinimum GeneralPaperStaticChoiceStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

theorem spent_le {i : Type*} (model : RationalCostModel) (W : ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (current : Option (Choice i)) (spent : ℕ) :
    spent≤(GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent).work := by
  induction rows generalizing current spent with
  | nil => simp only [GeneralPaperStaticMinimumScanPrice.loop]; omega
  | cons j rest ih => exact (by omega : spent≤spent+(evaluate j).2+
      (GeneralPaperStaticMinimumPrice.candidate model.rat W j (evaluate j).1).2+
      (GeneralPaperStaticMinimumPrice.pick model.rat W current (GeneralPaperStaticMinimumPrice.candidate model.rat W j (evaluate j).1).1).2+16*W).trans (ih _ _)

theorem good {i : Type*} (model : RationalCostModel) (W D E A B R I : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (hIndex : ∀ j∈rows,encode j≤I)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1)
    (current : Option (Choice i)) (hCurrent : Good encode I R current) (spent : ℕ) :
    Good encode I R (GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent).choice := by
  induction rows generalizing current spent with
  | nil => exact hCurrent
  | cons j rest ih =>
    have hFresh := candidate_good model W D E A B R I hD hE hR encode j (hIndex j List.mem_cons_self) (evaluate j).1 (hBound j List.mem_cons_self)
    have hSelected := pick_good model W I R encode current _ hCurrent hFresh
    exact ih (fun k hk => hIndex k (List.mem_cons_of_mem _ hk)) (fun k hk => hBound k (List.mem_cons_of_mem _ hk)) _ hSelected _

def metadataCap (model : RationalCostModel) (W R N C B : ℕ) : ℕ := N+1+B+C+64*W+6*model.rat (1+2*R)

def frame {i : Type*} (model : RationalCostModel) (W : ℕ) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (current : Option (Choice i)) (spent : ℕ) : ℕ :=
  let result := GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent
  choiceFoot W encode current+choiceFoot W encode result.choice+
    match rows with
    | [] => fields W [0,spent,result.work,2*W]+128*W
    | j::_ =>
      let a := evaluate j
      let fresh := GeneralPaperStaticMinimumPrice.candidate model.rat W j a.1
      let selected := GeneralPaperStaticMinimumPrice.pick model.rat W current fresh.1
      candidateWindow model W encode j a.1+pickWindow model W encode current fresh.1+
        fields W [rows.length,spent,result.work,a.2,fresh.2,selected.2,spent+a.2+fresh.2+selected.2+16*W]+128*W

def frameProfile (model : RationalCostModel) (W I R N C B : ℕ) : ℕ :=
  2*choiceProfile W I R+candidateProfile model W I R+pickProfile model W I R+
    7*(natBits (metadataCap model W R N C B)+W)+160*W

theorem frame_bound {i : Type*} (model : RationalCostModel) (W D E A B R I N C F : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (hLen : rows.length≤N) (hIndex : ∀ j∈rows,encode j≤I)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1) (hWork : ∀ j∈rows,(evaluate j).2≤C)
    (current : Option (Choice i)) (hCurrent : Good encode I R current) (spent : ℕ)
    (hF : (GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent).work≤F) :
    frame model W encode evaluate rows current spent≤frameProfile model W I R N C F := by
  let result := GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent
  have hCurrentFoot := choice_bound W I R encode current hCurrent
  have hReturn := choice_bound W I R encode result.choice (good model W D E A B R I hD hE hR encode evaluate rows hIndex hBound current hCurrent spent)
  have hSpent := (spent_le model W evaluate rows current spent).trans hF
  change result.work≤F at hF
  cases rows with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap model W R N C F)) [0,spent,result.work,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap model W R N C F)+W)+32*W at hf
    change choiceFoot W encode current+choiceFoot W encode result.choice+(GeneralPaperEncodedScalarStorage.fields W [0,spent,result.work,2*W]+128*W)≤_
    unfold frameProfile
    omega
  | cons j rest =>
    let a := evaluate j
    let fresh := GeneralPaperStaticMinimumPrice.candidate model.rat W j a.1
    let selected := GeneralPaperStaticMinimumPrice.pick model.rat W current fresh.1
    have hFresh := candidate_good model W D E A B R I hD hE hR encode j (hIndex j List.mem_cons_self) a.1 (hBound j List.mem_cons_self)
    have hFreshWork := GeneralPaperStaticMinimumPrice.candidate_work model.rat model.monotone W D E A B R hD hE hR j a.1 (hBound j List.mem_cons_self)
    change fresh.2≤32*W+5*model.rat (1+2*R) at hFreshWork
    have hSelectedWork := GeneralPaperStaticMinimumPrice.pick_work model.rat model.monotone W R current fresh.1
      (fun c hc => (hCurrent c hc).2) (fun c hc => (hFresh c hc).2)
    change selected.2≤8*W+model.rat (1+2*R) at hSelectedWork
    have hA : a.2≤C := hWork j List.mem_cons_self
    have hNext : spent+a.2+fresh.2+selected.2+16*W≤F :=
      (spent_le model W evaluate rest selected.1 (spent+a.2+fresh.2+selected.2+16*W)).trans hF
    have hCandidate := candidate_bound model W D E A B R I hD hE hR encode j (hIndex j List.mem_cons_self) a.1 (hBound j List.mem_cons_self)
    have hPick := pick_bound model W I R encode current fresh.1 hCurrent hFresh
    have hf := fields_bound W (natBits (metadataCap model W R N C F)) [(j::rest).length,spent,result.work,a.2,fresh.2,selected.2,spent+a.2+fresh.2+selected.2+16*W] (by
      intro b hb
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap model W R N C F)+W)+32*W at hf
    change choiceFoot W encode current+choiceFoot W encode result.choice+(candidateWindow model W encode j a.1+pickWindow model W encode current fresh.1+
      GeneralPaperEncodedScalarStorage.fields W [(j::rest).length,spent,result.work,a.2,fresh.2,selected.2,spent+a.2+fresh.2+selected.2+16*W]+128*W)≤_
    unfold frameProfile
    omega

def frames {i : Type*} (model : RationalCostModel) (W : ℕ) (encode : i → ℕ) (evaluate : i → Affine×ℕ) : List i → Option (Choice i) → ℕ → ℕ
  | [],current,spent => frame model W encode evaluate [] current spent
  | j::rest,current,spent =>
    let a := evaluate j
    let fresh := GeneralPaperStaticMinimumPrice.candidate model.rat W j a.1
    let selected := GeneralPaperStaticMinimumPrice.pick model.rat W current fresh.1
    frame model W encode evaluate (j::rest) current spent+frames model W encode evaluate rest selected.1 (spent+a.2+fresh.2+selected.2+16*W)

theorem frames_bound {i : Type*} (model : RationalCostModel) (W D E A B R I N C F : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (hLen : rows.length≤N) (hIndex : ∀ j∈rows,encode j≤I)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1) (hWork : ∀ j∈rows,(evaluate j).2≤C)
    (current : Option (Choice i)) (hCurrent : Good encode I R current) (spent : ℕ)
    (hF : (GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows current spent).work≤F) :
    frames model W encode evaluate rows current spent≤(rows.length+1)*frameProfile model W I R N C F := by
  induction rows generalizing current spent with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using
      frame_bound model W D E A B R I N C F hD hE hR encode evaluate [] hLen hIndex hBound hWork current hCurrent spent hF
  | cons j rest ih =>
    have hFrame := frame_bound model W D E A B R I N C F hD hE hR encode evaluate (j::rest) hLen hIndex hBound hWork current hCurrent spent hF
    have hFresh := candidate_good model W D E A B R I hD hE hR encode j (hIndex j List.mem_cons_self) (evaluate j).1 (hBound j List.mem_cons_self)
    have hSelected := pick_good model W I R encode current _ hCurrent hFresh
    have hRest := ih (by simp only [List.length_cons] at hLen; omega)
      (fun k hk => hIndex k (List.mem_cons_of_mem _ hk)) (fun k hk => hBound k (List.mem_cons_of_mem _ hk))
      (fun k hk => hWork k (List.mem_cons_of_mem _ hk)) _ hSelected _ hF
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def workCap (model : RationalCostModel) (W R N C : ℕ) : ℕ := N*(C+56*W+6*model.rat (1+2*R))+2*W

def window {i : Type*} (model : RationalCostModel) (W : ℕ) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (space : i → ℕ) (rows : List i) (active : Option i) : ℕ :=
  listFootprint W encode rows+frames model W encode evaluate rows none 0+GeneralPaperPricedListStreamStorage.activeSpace space active

def profile (model : RationalCostModel) (W I R N C Q : ℕ) : ℕ :=
  N*(I+2*W)+32*W+(N+1)*frameProfile model W I R N C (workCap model W R N C)+Q

theorem bounded {i : Type*} (model : RationalCostModel) (W D E A B R I N C Q : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (encode : i → ℕ) (evaluate : i → Affine×ℕ)
    (rows : List i) (hLen : rows.length≤N) (hIndex : ∀ j∈rows,encode j≤I)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1) (hWork : ∀ j∈rows,(evaluate j).2≤C)
    (space : i → ℕ) (hSpace : ∀ j∈rows,space j≤Q) (active : Option i) (hActive : ∀ j,active=some j → j∈rows) :
    window model W encode evaluate space rows active≤profile model W I R N C Q := by
  have hWorkSum := GeneralPaperStaticMinimumScanPrice.work model.rat model.monotone W D E A B R hD hE hR evaluate rows hBound
  have hSum := GeneralPaperEncodedScalarStorage.sum_bound (fun j => (evaluate j).2+56*W+6*model.rat (1+2*R))
    (C+56*W+6*model.rat (1+2*R)) rows (fun j hj => by have h := hWork j hj; omega)
  have hF : (GeneralPaperStaticMinimumScanPrice.loop model.rat W evaluate rows none 0).work≤workCap model W R N C :=
    hWorkSum.trans (by unfold workCap; nlinarith only [hSum,Nat.mul_le_mul_right (C+56*W+6*model.rat (1+2*R)) hLen])
  have hFrames := (frames_bound model W D E A B R I N C _ hD hE hR encode evaluate rows hLen hIndex hBound hWork none
    (by intro c hc; cases hc) 0 hF).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1))
  have hList := (list_bound W I encode rows hIndex).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hScratch := GeneralPaperPricedListStreamStorage.active_bound Q space active rows hSpace hActive
  unfold window profile
  omega

end Blotto.GeneralPaperStaticScanLoopStorage

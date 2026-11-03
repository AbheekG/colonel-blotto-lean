import Blotto.GeneralPaperAffinePickStorage

/-! Native recursive affine minimum scan. Retained current witnesses,
actual pick windows and encoded child/return metadata are reserved along
the structural stack. Only one candidate-construction callback is active. -/
namespace Blotto.GeneralPaperAffineScanStorage
open RationalOrderCell GeneralPaperRayAffineMinimum GeneralPaperAffinePickStorage
open GeneralPaperAffineWitnessStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

theorem good {i : Type*} {K : ℕ} (model : RationalCostModel) (W n R : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K)×ℕ) (xs : List i) (h : ∀ a∈xs,Good n R (evaluate a).1) :
    Good n R (GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate xs).1 := by
  intro c hc
  rw [GeneralPaperAffineMinimumPrice.scan_data] at hc
  obtain ⟨a,ha,he⟩ := scan_origin t (fun a => (evaluate a).1) xs c hc
  exact h a ha c he

def workCap (model : RationalCostModel) (W R s C N : ℕ) : ℕ :=
  (C+GeneralPaperAffinePickStorage.workCap model W R s+4*W)*N+2*W

theorem work {i : Type*} {K : ℕ} (model : RationalCostModel) (W n R s C : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (evaluate : i → Option (Choice K)×ℕ) (xs : List i)
    (hGood : ∀ a∈xs,Good n R (evaluate a).1) (hWork : ∀ a∈xs,(evaluate a).2≤C) :
    (GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate xs).2≤workCap model W R s C xs.length := by
  induction xs with
  | nil => simp only [GeneralPaperAffineMinimumPrice.scanRun,List.length_nil,workCap,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => hGood b (List.mem_cons_of_mem _ hb)) (fun b hb => hWork b (List.mem_cons_of_mem _ hb))
    have hp := GeneralPaperAffinePickStorage.work model W n R s t ht (evaluate a).1
      (GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate rest).1 (hGood a List.mem_cons_self)
      (good model W n R t evaluate rest (fun b hb => hGood b (List.mem_cons_of_mem _ hb)))
    have ha := hWork a List.mem_cons_self
    change (evaluate a).2+(GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate rest).2+
      (GeneralPaperAffineMinimumPrice.pickRun model.rat W t (evaluate a).1 (GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate rest).1).2+4*W≤_
    simp only [List.length_cons,workCap] at hr ⊢
    nlinarith only [hr,hp,ha]

def metadataCap (model : RationalCostModel) (W R s C N : ℕ) : ℕ :=
  N+1+C+3*workCap model W R s C N+GeneralPaperAffinePickStorage.workCap model W R s+4*W

def frame {i : Type*} {K : ℕ} (model : RationalCostModel) (W : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K)×ℕ) : List i → ℕ
  | [] => fields W [0,2*W]+128*W
  | a::rest =>
    let current := evaluate a
    let child := GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate rest
    let selected := GeneralPaperAffineMinimumPrice.pickRun model.rat W t current.1 child.1
    let result := GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate (a::rest)
    GeneralPaperAffinePickStorage.window model W t current.1 child.1+
      fields W [(a::rest).length,current.2,child.2,selected.2,result.2,current.2+child.2,
        current.2+child.2+selected.2,current.2+child.2+selected.2+4*W]+128*W

def frameProfile (model : RationalCostModel) (W K n R s C N : ℕ) : ℕ :=
  GeneralPaperAffinePickStorage.profile model W K n R s+8*(natBits (metadataCap model W R s C N)+W)+160*W

theorem frame_bound {i : Type*} {K : ℕ} (model : RationalCostModel) (W n R s C N : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (evaluate : i → Option (Choice K)×ℕ) (xs : List i) (hn : xs.length≤N)
    (hGood : ∀ a∈xs,Good n R (evaluate a).1) (hWork : ∀ a∈xs,(evaluate a).2≤C) :
    frame model W t evaluate xs≤frameProfile model W K n R s C N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap model W R s C N)) [0,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl
      all_goals unfold metadataCap workCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (metadataCap model W R s C N)+W)+32*W at hf
    unfold frame frameProfile
    dsimp only
    omega
  | cons a rest =>
    let current := evaluate a
    let child := GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate rest
    let selected := GeneralPaperAffineMinimumPrice.pickRun model.rat W t current.1 child.1
    let result := GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate (a::rest)
    have hRest : ∀ b∈rest,Good n R (evaluate b).1 := fun b hb => hGood b (List.mem_cons_of_mem _ hb)
    have hRestWork : ∀ b∈rest,(evaluate b).2≤C := fun b hb => hWork b (List.mem_cons_of_mem _ hb)
    have hChild := (work model W n R s C t ht evaluate rest hRest hRestWork).trans
      (show workCap model W R s C rest.length≤workCap model W R s C N by unfold workCap; gcongr; simp only [List.length_cons] at hn; omega)
    change child.2≤workCap model W R s C N at hChild
    have hResult := (work model W n R s C t ht evaluate (a::rest) hGood hWork).trans
      (show workCap model W R s C (a::rest).length≤workCap model W R s C N by unfold workCap; gcongr)
    change result.2≤workCap model W R s C N at hResult
    have hCurrent : current.2≤C := hWork a List.mem_cons_self
    have hChildGood := good model W n R t evaluate rest hRest
    have hPick := GeneralPaperAffinePickStorage.work model W n R s t ht current.1 child.1 (hGood a List.mem_cons_self) hChildGood
    change selected.2≤GeneralPaperAffinePickStorage.workCap model W R s at hPick
    have hShape : result.2=current.2+child.2+selected.2+4*W := rfl
    have hWindow := GeneralPaperAffinePickStorage.bounded model W n R s t ht current.1 child.1 (hGood a List.mem_cons_self) hChildGood
    have hf := fields_bound W (natBits (metadataCap model W R s C N))
      [(a::rest).length,current.2,child.2,selected.2,result.2,current.2+child.2,current.2+child.2+selected.2,current.2+child.2+selected.2+4*W] (by
        intro v hv
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap model W R s C N)+W)+32*W at hf
    change GeneralPaperAffinePickStorage.window model W t current.1 child.1+
      GeneralPaperEncodedScalarStorage.fields W [(a::rest).length,current.2,child.2,selected.2,result.2,current.2+child.2,current.2+child.2+selected.2,current.2+child.2+selected.2+4*W]+128*W≤_
    unfold frameProfile
    omega

def frames {i : Type*} {K : ℕ} (model : RationalCostModel) (W : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K)×ℕ) : List i → ℕ
  | [] => frame model W t evaluate []
  | a::rest => frame model W t evaluate (a::rest)+frames model W t evaluate rest

theorem frames_bound {i : Type*} {K : ℕ} (model : RationalCostModel) (W n R s C N : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (evaluate : i → Option (Choice K)×ℕ) (xs : List i) (hn : xs.length≤N)
    (hGood : ∀ a∈xs,Good n R (evaluate a).1) (hWork : ∀ a∈xs,(evaluate a).2≤C) :
    frames model W t evaluate xs≤(xs.length+1)*frameProfile model W K n R s C N := by
  induction xs with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W n R s C N t ht evaluate [] hn hGood hWork
  | cons a rest ih =>
    have hFrame := frame_bound model W n R s C N t ht evaluate (a::rest) hn hGood hWork
    have hRest := ih (by simp only [List.length_cons] at hn; omega)
      (fun b hb => hGood b (List.mem_cons_of_mem _ hb)) (fun b hb => hWork b (List.mem_cons_of_mem _ hb))
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def window {i : Type*} {K : ℕ} (model : RationalCostModel) (W : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K)×ℕ) (space : i → ℕ) (xs : List i) (active : Option i) : ℕ :=
  frames model W t evaluate xs+optionChoiceFoot W (GeneralPaperAffineMinimumPrice.scanRun model.rat W t evaluate xs).1+
    GeneralPaperPricedListStreamStorage.activeSpace space active

def profile (model : RationalCostModel) (W K n R s C N Q : ℕ) : ℕ :=
  (N+1)*frameProfile model W K n R s C N+optionChoiceProfile W K n R+Q

theorem bounded {i : Type*} {K : ℕ} (model : RationalCostModel) (W n R s C N Q : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (evaluate : i → Option (Choice K)×ℕ) (space : i → ℕ) (xs : List i) (hn : xs.length≤N)
    (hGood : ∀ a∈xs,Good n R (evaluate a).1) (hWork : ∀ a∈xs,(evaluate a).2≤C)
    (hSpace : ∀ a∈xs,space a≤Q) (active : Option i) (hActive : ∀ a,active=some a → a∈xs) :
    window model W t evaluate space xs active≤profile model W K n R s C N Q := by
  have hFrames := (frames_bound model W n R s C N t ht evaluate xs hn hGood hWork).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hResult := option_choice_bound W n R _ (good model W n R t evaluate xs hGood)
  have hScratch := GeneralPaperPricedListStreamStorage.active_bound Q space active xs hSpace hActive
  unfold window profile
  omega

end Blotto.GeneralPaperAffineScanStorage

import Blotto.GeneralPaperSourceRawAffineStorageReachedRates

/-! Literal final Boolean static-scan recursion. Every visited index,
evaluated residual, comparison scratch, input/output acceptance bit and
native spent/partial/return field is counted. One active row evaluator
remains separate from the conservative complete recursive-frame count. -/
namespace Blotto.GeneralPaperFinalStaticLoopStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayAffine
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def bit (b : Bool) : ℕ := if b then 1 else 0
theorem bit_bound (b : Bool) : bit b≤1 := by cases b <;> decide
def comparison (model : RationalCostModel) (a : Affine) : ℕ := model.rat (RationalExpression.pairWidth a.intercept 0)

theorem spent_le {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (rows : List (StaticIndex T m K)) (accepted : Bool) (spent : ℕ) :
    spent≤(GeneralPaperFinalStaticBits.loop model.rat W labels x rows accepted spent).work := by
  induction rows generalizing accepted spent with
  | nil => simp only [GeneralPaperFinalStaticBits.loop]; omega
  | cons j rest ih => exact (by omega : spent≤spent+(GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2+
      comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1+8*W).trans (ih _ _)

def metadataCap (model : RationalCostModel) (W R N C F : ℕ) : ℕ := N+2+F+C+32*W+model.rat (1+2*R)
def frame {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) (rows : List (StaticIndex T m K)) (accepted : Bool) (spent : ℕ) : ℕ :=
  let result := GeneralPaperFinalStaticBits.loop model.rat W labels x rows accepted spent
  match rows with
  | [] => fields W [0,spent,result.work,2*W,bit accepted,bit result.accepted]+128*W
  | j::_ =>
    let a := GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j
    let c := comparison model a.1
    GeneralPaperNativeStaticScanStorage.indexFoot W j+affineFoot W a.1+rationalWordWidth 0+c+
      fields W [rows.length,spent,result.work,a.2,c,8*W,spent+a.2,spent+a.2+c,spent+a.2+c+8*W,
        bit accepted,bit result.accepted]+192*W
def frameProfile (model : RationalCostModel) (W I R N C F : ℕ) : ℕ :=
  I+affineProfile W R+(1+2*R)+model.rat (1+2*R)+11*(natBits (metadataCap model W R N C F)+W)+224*W

theorem frame_bound {T m K : ℕ} (model : RationalCostModel) (W I R N C F : ℕ) (hR : 1≤R)
    (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) (rows : List (StaticIndex T m K))
    (hLen : rows.length≤N) (hIndex : ∀ j∈rows,GeneralPaperNativeStaticScanStorage.indexFoot W j≤I)
    (hBound : ∀ j∈rows,RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.intercept R ∧
      RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.slope R)
    (hWork : ∀ j∈rows,(GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2≤C)
    (hCompare : ∀ j∈rows,comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1≤model.rat (1+2*R))
    (accepted : Bool) (spent : ℕ) (hF : (GeneralPaperFinalStaticBits.loop model.rat W labels x rows accepted spent).work≤F) :
    frame model W labels x rows accepted spent≤frameProfile model W I R N C F := by
  let result := GeneralPaperFinalStaticBits.loop model.rat W labels x rows accepted spent
  have hSpent := (spent_le model W labels x rows accepted spent).trans hF
  change result.work≤F at hF
  have hb := bit_bound accepted
  have hb' := bit_bound result.accepted
  cases rows with
  | nil =>
    have hShape : result.work=spent+2*W := rfl
    have hf := fields_bound W (natBits (metadataCap model W R N C F)) [0,spent,result.work,2*W,bit accepted,bit result.accepted] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      unfold metadataCap
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W R N C F)+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W [0,spent,result.work,2*W,bit accepted,bit result.accepted]+128*W≤_
    unfold frameProfile
    omega
  | cons j rest =>
    let a := GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j
    let c := comparison model a.1
    have hI := hIndex j List.mem_cons_self
    have hA := affine_bound W R a.1 (hBound j List.mem_cons_self).1 (hBound j List.mem_cons_self).2
    have hZero := rationalWordWidth_of_height (GeneralPaperQuantizedHeight.zero_height R (by omega))
    have hC : c≤model.rat (1+2*R) := hCompare j List.mem_cons_self
    have hW : a.2≤C := hWork j List.mem_cons_self
    have hNext : spent+a.2+c+8*W≤F := (spent_le model W labels x rest
      (accepted && decide (a.1.intercept≤0)) (spent+a.2+c+8*W)).trans hF
    have hf := fields_bound W (natBits (metadataCap model W R N C F))
      [(j::rest).length,spent,result.work,a.2,c,8*W,spent+a.2,spent+a.2+c,spent+a.2+c+8*W,bit accepted,bit result.accepted] (by
        intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold metadataCap
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (metadataCap model W R N C F)+W)+32*W at hf
    change GeneralPaperNativeStaticScanStorage.indexFoot W j+affineFoot W a.1+rationalWordWidth 0+c+
      GeneralPaperEncodedScalarStorage.fields W [(j::rest).length,spent,result.work,a.2,c,8*W,spent+a.2,spent+a.2+c,
        spent+a.2+c+8*W,bit accepted,bit result.accepted]+192*W≤_
    unfold frameProfile
    omega

def frames {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x : Variable m K → ℚ) : List (StaticIndex T m K) → Bool → ℕ → ℕ
  | [],accepted,spent => frame model W labels x [] accepted spent
  | j::rest,accepted,spent =>
    let a := GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j
    let c := comparison model a.1
    frame model W labels x (j::rest) accepted spent+
      frames model W labels x rest (accepted && decide (a.1.intercept≤0)) (spent+a.2+c+8*W)

theorem frames_bound {T m K : ℕ} (model : RationalCostModel) (W I R N C F : ℕ) (hR : 1≤R)
    (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) (rows : List (StaticIndex T m K))
    (hLen : rows.length≤N) (hIndex : ∀ j∈rows,GeneralPaperNativeStaticScanStorage.indexFoot W j≤I)
    (hBound : ∀ j∈rows,RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.intercept R ∧
      RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.slope R)
    (hWork : ∀ j∈rows,(GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2≤C)
    (hCompare : ∀ j∈rows,comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1≤model.rat (1+2*R))
    (accepted : Bool) (spent : ℕ) (hF : (GeneralPaperFinalStaticBits.loop model.rat W labels x rows accepted spent).work≤F) :
    frames model W labels x rows accepted spent≤(rows.length+1)*frameProfile model W I R N C F := by
  induction rows generalizing accepted spent with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using
      frame_bound model W I R N C F hR labels x [] hLen hIndex hBound hWork hCompare accepted spent hF
  | cons j rest ih =>
    have hFrame := frame_bound model W I R N C F hR labels x (j::rest) hLen hIndex hBound hWork hCompare accepted spent hF
    have hRest := ih (by simp only [List.length_cons] at hLen; omega)
      (fun k hk => hIndex k (List.mem_cons_of_mem _ hk)) (fun k hk => hBound k (List.mem_cons_of_mem _ hk))
      (fun k hk => hWork k (List.mem_cons_of_mem _ hk)) (fun k hk => hCompare k (List.mem_cons_of_mem _ hk)) _ _ hF
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def workCap (model : RationalCostModel) (W R N C : ℕ) : ℕ := N*(C+model.rat (1+2*R)+8*W)+2*W
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ)
    (rows : List (StaticIndex T m K)) (space : StaticIndex T m K → ℕ) (active : Option (StaticIndex T m K)) : ℕ :=
  listFootprint W (GeneralPaperNativeStaticScanStorage.indexFoot W) rows+frames model W labels x rows true 0+
    GeneralPaperPricedListStreamStorage.activeSpace space active
def profile (model : RationalCostModel) (W I R N C Q : ℕ) : ℕ :=
  N*(I+2*W)+32*W+(N+1)*frameProfile model W I R N C (workCap model W R N C)+Q

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W I R N C Q : ℕ) (hR : 1≤R)
    (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) (rows : List (StaticIndex T m K))
    (hLen : rows.length≤N) (hIndex : ∀ j∈rows,GeneralPaperNativeStaticScanStorage.indexFoot W j≤I)
    (hBound : ∀ j∈rows,RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.intercept R ∧
      RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.slope R)
    (hWork : ∀ j∈rows,(GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2≤C)
    (hCompare : ∀ j∈rows,comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1≤model.rat (1+2*R))
    (space : StaticIndex T m K → ℕ) (hSpace : ∀ j∈rows,space j≤Q)
    (active : Option (StaticIndex T m K)) (hActive : ∀ j,active=some j → j∈rows) :
    window model W labels x rows space active≤profile model W I R N C Q := by
  have hLoop := GeneralPaperFinalStaticBits.loop_work model.rat W labels x rows true 0
  have hSum := sum_bound (fun j => (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2+
    comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1+8*W)
    (C+model.rat (1+2*R)+8*W) rows (fun j hj => by have h:=hWork j hj; have hc:=hCompare j hj; omega)
  have hF : (GeneralPaperFinalStaticBits.loop model.rat W labels x rows true 0).work≤workCap model W R N C := by
    rw [hLoop]
    unfold workCap comparison at *
    have h := Nat.mul_le_mul_right (C+model.rat (1+2*R)+8*W) hLen
    omega
  have hFrames := (frames_bound model W I R N C _ hR labels x rows hLen hIndex hBound hWork hCompare true 0 hF).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1))
  have hList := (list_bound W I (GeneralPaperNativeStaticScanStorage.indexFoot W) rows hIndex).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hScratch := GeneralPaperPricedListStreamStorage.active_bound Q space active rows hSpace hActive
  unfold window profile
  omega

end Blotto.GeneralPaperFinalStaticLoopStorage

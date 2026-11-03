import Blotto.GeneralPaperStaticVariableConstructionStorage

/-! Actual native box/order/budget index constructors and their streaming
wrappers. Variable-list materialization stays retained; current constructor
records and encoded native child/outer work are counted independently. -/
namespace Blotto.GeneralPaperStaticFamilyConstructionStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperEncodedScalarStorage
open GeneralPaperPricedPayloadStreamStorage GeneralPaperNativeStaticScanStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def callbackCap (W T m K : ℕ) : ℕ := T+m+K+1+32*W

def callbackWindow {T m K : ℕ} (W : ℕ) (out : List (StaticIndex T m K)) (scalars : List ℕ) : ℕ :=
  listFootprint W (indexFoot W) out+fields W scalars+128*W

def callbackProfile (W T m K : ℕ) : ℕ :=
  2*(indexProfile W T m K+2*W)+32*W+3*(natBits (callbackCap W T m K)+W)+160*W

theorem callback_bound {T m K : ℕ} (W : ℕ) (out : List (StaticIndex T m K)) (scalars : List ℕ)
    (hOut : out.length≤2) (hLength : scalars.length≤3) (hs : ∀ a∈scalars,a≤callbackCap W T m K) :
    callbackWindow W out scalars≤callbackProfile W T m K := by
  have hList := (list_bound W (indexProfile W T m K) (indexFoot W) out (fun i _ => index_bound W i)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hOut) _)
  have hf := (fields_bound W (natBits (callbackCap W T m K)) scalars
    (fun a ha => Nat.add_le_add_left (binaryWordWidth_mono (hs a ha)) 1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLength) _)
  unfold callbackWindow callbackProfile
  omega

def boxCallback {T m K : ℕ} (W : ℕ) (v : Variable m K) : ℕ :=
  callbackWindow W ([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)) [v.1.val,v.2.val,32*W]
def orderCallback {T m K : ℕ} (W : ℕ) (v : Variable m K) : ℕ :=
  callbackWindow W ([.inr (.inl v)] : List (StaticIndex T m K)) [v.1.val,v.2.val,8*W]
def budgetCallback {T m K : ℕ} (W : ℕ) (i : Fin T) : ℕ :=
  callbackWindow W ([.inr (.inr i)] : List (StaticIndex T m K)) [i.val,8*W]

theorem box_callback {T m K : ℕ} (W : ℕ) (v : Variable m K) : boxCallback (T:=T) W v≤callbackProfile W T m K := by
  have hm := v.1.isLt
  have hK := v.2.isLt
  apply callback_bound W _ _ (by simp) (by simp)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  all_goals unfold callbackCap; omega

theorem order_callback {T m K : ℕ} (W : ℕ) (v : Variable m K) : orderCallback (T:=T) W v≤callbackProfile W T m K := by
  have hm := v.1.isLt
  have hK := v.2.isLt
  apply callback_bound W _ _ (by simp) (by simp)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  all_goals unfold callbackCap; omega

theorem budget_callback {T m K : ℕ} (W : ℕ) (i : Fin T) : budgetCallback (m:=m) (K:=K) W i≤callbackProfile W T m K := by
  have hi := i.isLt
  apply callback_bound W _ _ (by simp) (by simp)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  all_goals unfold callbackCap; omega

def familyPrice (W m K : ℕ) : ℕ := 256*(m*(K-1)+m+1)*W
def familyCap (W m K : ℕ) : ℕ := 1+3*familyPrice W m K

def boxesWindow (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) : ℕ :=
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let body := GeneralPaperPricedListStream.flatMap W (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W)) vars.1
  let result := GeneralPaperStaticEnumerationPrice.boxesRun W T m K
  GeneralPaperStaticVariableConstructionStorage.window W m K copied activeField activeLabel+
    flatWindow W copied (indexFoot W) (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W))
      (boxCallback (T:=T) W) activeVariable vars.1+fields W [vars.2,body.2,result.2]+128*W

def boxesProfile (W T m K : ℕ) : ℕ := GeneralPaperStaticVariableConstructionStorage.profile W m K+
  flatProfile W (indexProfile W T m K) 2 (32*W) (m*(K-1)) (callbackProfile W T m K)+3*(natBits (familyCap W m K)+W)+160*W

theorem boxes_bound (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) : boxesWindow W T m K copied activeField activeLabel activeVariable≤boxesProfile W T m K := by
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let body := GeneralPaperPricedListStream.flatMap W (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W)) vars.1
  let result := GeneralPaperStaticEnumerationPrice.boxesRun W T m K
  have hLength : vars.1.length=m*(K-1) := by rw [GeneralPaperStaticEnumerationPrice.variable_data,variableList_length]
  have hVars := GeneralPaperStaticVariableConstructionStorage.bounded W m K copied activeField activeLabel
  have hFlat := flat_bounded W (indexProfile W T m K) 2 (32*W) (m*(K-1)) (callbackProfile W T m K) copied
    (indexFoot W) (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W)) (boxCallback (T:=T) W) activeVariable vars.1 hLength.le
    (by intro _ _; simp) (fun _ _ => le_rfl) (fun _ _ i _ => index_bound W i) (fun v _ => box_callback W v)
    (by intro v _; rw [GeneralPaperStaticEnumerationPrice.variable_data]; exact variableList_mem m K v)
  have hWork := GeneralPaperStaticEnumerationPrice.boxes_work W T m K
  change result.2≤familyPrice W m K at hWork
  have hShape : result.2=vars.2+body.2 := rfl
  have hf := fields_bound W (natBits (familyCap W m K)) [vars.2,body.2,result.2] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold familyCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (familyCap W m K)+W)+32*W at hf
  unfold boxesWindow boxesProfile
  dsimp only
  dsimp only [vars,body,result] at hf hFlat
  omega

def ordersWindow (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) : ℕ :=
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let body := GeneralPaperPricedListMap.run W (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) vars.1
  let result := GeneralPaperStaticEnumerationPrice.ordersRun W T m K
  GeneralPaperStaticVariableConstructionStorage.window W m K copied activeField activeLabel+
    mapWindow W (indexFoot W) (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) (orderCallback (T:=T) W) activeVariable vars.1+
      fields W [vars.2,body.2,result.2]+128*W

def ordersProfile (W T m K : ℕ) : ℕ := GeneralPaperStaticVariableConstructionStorage.profile W m K+
  filterProfile W (indexProfile W T m K) (8*W) (m*(K-1)) (callbackProfile W T m K)+3*(natBits (familyCap W m K)+W)+160*W

theorem orders_bound (W T m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1)))
    (activeVariable : Option (Variable m K)) : ordersWindow W T m K copied activeField activeLabel activeVariable≤ordersProfile W T m K := by
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let body := GeneralPaperPricedListMap.run W (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) vars.1
  let result := GeneralPaperStaticEnumerationPrice.ordersRun W T m K
  have hLength : vars.1.length=m*(K-1) := by rw [GeneralPaperStaticEnumerationPrice.variable_data,variableList_length]
  have hVars := GeneralPaperStaticVariableConstructionStorage.bounded W m K copied activeField activeLabel
  have hMap := map_bounded W (indexProfile W T m K) (8*W) (m*(K-1)) (callbackProfile W T m K)
    (indexFoot W) (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) (orderCallback (T:=T) W) activeVariable vars.1 hLength.le
    (fun _ _ => le_rfl) (fun v _ => index_bound W (.inr (.inl v))) (fun v _ => order_callback W v)
    (by intro v _; rw [GeneralPaperStaticEnumerationPrice.variable_data]; exact variableList_mem m K v)
  have hWork := GeneralPaperStaticEnumerationPrice.orders_work W T m K
  change result.2≤familyPrice W m K at hWork
  have hShape : result.2=vars.2+body.2 := rfl
  have hf := fields_bound W (natBits (familyCap W m K)) [vars.2,body.2,result.2] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold familyCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (familyCap W m K)+W)+32*W at hf
  unfold ordersWindow ordersProfile
  dsimp only
  dsimp only [vars,body,result] at hf hMap
  omega

def budgetPrice (W T : ℕ) : ℕ := 64*(T+1)*W
def budgetCap (W T : ℕ) : ℕ := T+1+3*budgetPrice W T+16*(T+1)*W

def budgetsWindow (W T m K copied : ℕ) (active : Option (Fin T)) : ℕ :=
  let body := GeneralPaperPricedListMap.run W (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (List.finRange T)
  let result := GeneralPaperStaticEnumerationPrice.budgetsRun W T m K
  GeneralPaperFinRangeStorage.window W T copied+
    mapWindow W (indexFoot W) (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (budgetCallback (m:=m) (K:=K) W) active (List.finRange T)+
      fields W [T,body.2,result.2,16*(T+1)*W]+128*W

def budgetsProfile (W T m K : ℕ) : ℕ := GeneralPaperFinRangeStorage.profile W T+
  filterProfile W (indexProfile W T m K) (8*W) T (callbackProfile W T m K)+4*(natBits (budgetCap W T)+W)+160*W

theorem budgets_bound (W T m K copied : ℕ) (active : Option (Fin T)) : budgetsWindow W T m K copied active≤budgetsProfile W T m K := by
  let body := GeneralPaperPricedListMap.run W (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (List.finRange T)
  let result := GeneralPaperStaticEnumerationPrice.budgetsRun W T m K
  have hRange := GeneralPaperFinRangeStorage.bounded W T copied
  have hMap := map_bounded W (indexProfile W T m K) (8*W) T (callbackProfile W T m K)
    (indexFoot W) (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (budgetCallback (m:=m) (K:=K) W) active (List.finRange T)
    (by simp only [List.length_finRange,le_refl]) (fun _ _ => le_rfl) (fun i _ => index_bound W (.inr (.inr i)))
    (fun i _ => budget_callback W i) (fun i _ => List.mem_finRange i)
  have hWork := GeneralPaperStaticEnumerationPrice.budgets_work W T m K
  change result.2≤budgetPrice W T at hWork
  have hShape : result.2=body.2+16*(T+1)*W := rfl
  have hf := fields_bound W (natBits (budgetCap W T)) [T,body.2,result.2,16*(T+1)*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl
    all_goals unfold budgetCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (budgetCap W T)+W)+32*W at hf
  unfold budgetsWindow budgetsProfile
  dsimp only
  dsimp only [body,result] at hf hMap
  omega

end Blotto.GeneralPaperStaticFamilyConstructionStorage

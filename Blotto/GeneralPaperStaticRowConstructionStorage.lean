import Blotto.GeneralPaperStockListPayloadStorage

/-! Literal sparse static-row construction. Reference tags and omitted
zero/one anchors, per-field list-of-lists, complete flatten intermediates,
order negation maps, append copies and constructor indices are counted. -/
namespace Blotto.GeneralPaperStaticRowConstructionStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperAffineConstraintRows
open GeneralPaperStaticRowResidualStorage GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

theorem reference_length {m K : ℕ} (r : Reference m K) : (refTerms r).length≤1 := by
  cases r with
  | none => simp only [refTerms,List.length_nil]; omega
  | some r => cases r <;> simp only [refTerms,List.length_nil,List.length_cons] <;> omega

theorem reference_unit {m K : ℕ} (r : Reference m K) : ∀ t∈refTerms r,t.2.natAbs≤1 := by
  cases r with
  | none => intro t ht; cases ht
  | some r =>
    cases r with
    | none => intro t ht; cases ht
    | some v => intro t ht; simp only [refTerms,List.mem_singleton] at ht; subst t; norm_num

def referenceWindow {m K : ℕ} (W : ℕ) (r : Reference m K) : ℕ :=
  listFootprint W (termFoot W) (refTerms r)+
    match (generalizing := false) r with
    | none => fields W [0,0,0]+64*W
    | some none => fields W [1,0,0]+64*W
    | some (some v) => fields W [2,v.1.val,v.2.val]+64*W

def referenceProfile (W m K : ℕ) : ℕ :=
  (termProfile W m K+2*W)+32*W+3*(natBits (m+K+2)+W)+96*W

theorem reference_bound {m K : ℕ} (W : ℕ) (r : Reference m K) : referenceWindow W r≤referenceProfile W m K := by
  have hList := (list_bound W (termProfile W m K) (termFoot W) (refTerms r)
    (fun t ht => term_bound W t (reference_unit r t ht))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (reference_length r)) _)
  have hList' : listFootprint W (termFoot W) (refTerms r)≤termProfile W m K+2*W+32*W := by simpa only [Nat.one_mul] using hList
  have hBranch : (match (generalizing := false) r with
      | none => fields W [0,0,0]+64*W
      | some none => fields W [1,0,0]+64*W
      | some (some v) => fields W [2,v.1.val,v.2.val]+64*W)≤3*(natBits (m+K+2)+W)+96*W := by
    clear hList hList'
    cases r with
    | none =>
      have hf := fields_bound W (natBits (m+K+2)) [0,0,0] (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; rcases ha with rfl|rfl|rfl <;> exact Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le _)) 1)
      change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (m+K+2)+W)+32*W at hf
      exact (Nat.add_le_add_right hf (64*W)).trans_eq (by ring)
    | some r =>
      cases r with
      | none =>
        have hf := fields_bound W (natBits (m+K+2)) [1,0,0] (by
          intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl <;> omega)
        change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (m+K+2)+W)+32*W at hf
        exact (Nat.add_le_add_right hf (64*W)).trans_eq (by ring)
      | some v =>
        have hm := v.1.isLt
        have hk := v.2.isLt
        have hf := fields_bound W (natBits (m+K+2)) [2,v.1.val,v.2.val] (by
          intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl <;> omega)
        change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (m+K+2)+W)+32*W at hf
        exact (Nat.add_le_add_right hf (64*W)).trans_eq (by ring)
  unfold referenceWindow
  exact (Nat.add_le_add hList' hBranch).trans_eq (show _=referenceProfile W m K by unfold referenceProfile; ring)

def controlCap (W m K : ℕ) : ℕ := m+K+2+(16*m+32)*W

def budgetFrames {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) : ℕ :=
  ∑ j : Fin m, (referenceWindow W (tupleReference j (labels j))+
    fields W [j.val,(labels j).val,(labels j).val-1,m,K]+128*W)

def budgetFrameProfile (W m K : ℕ) : ℕ :=
  m*(referenceProfile W m K+5*(natBits (controlCap W m K)+W)+160*W)

theorem budget_frames {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) : budgetFrames W labels≤budgetFrameProfile W m K := by
  have he (j : Fin m) : referenceWindow W (tupleReference j (labels j))+
      fields W [j.val,(labels j).val,(labels j).val-1,m,K]+128*W≤referenceProfile W m K+5*(natBits (controlCap W m K)+W)+160*W := by
    have hR := reference_bound W (tupleReference j (labels j))
    have hj := j.isLt
    have hl := (labels j).isLt
    have hf := fields_bound W (natBits (controlCap W m K)) [j.val,(labels j).val,(labels j).val-1,m,K] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold controlCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (controlCap W m K)+W)+32*W at hf
    omega
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => he j)
  simpa only [budgetFrames,budgetFrameProfile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

def budgetWindow {m K : ℕ} (W copied : ℕ) (labels : Fin m → Fin K) : ℕ :=
  let f := fun j => refTerms (tupleReference j (labels j))
  GeneralPaperStockListPayloadStorage.ofFnWindow W copied (listFootprint W (termFoot W)) f+
    GeneralPaperStockListPayloadStorage.flattenWindow W copied (termFoot W) (List.ofFn f)+budgetFrames W labels

def budgetProfile (W m K : ℕ) : ℕ :=
  GeneralPaperStockListPayloadStorage.ofFnProfile W (termProfile W m K+2*W+32*W) m+
    GeneralPaperStockListPayloadStorage.flattenProfile W (termProfile W m K) 1 m+budgetFrameProfile W m K

theorem budget_bound {m K : ℕ} (W copied : ℕ) (labels : Fin m → Fin K) : budgetWindow W copied labels≤budgetProfile W m K := by
  let f := fun j => refTerms (tupleReference j (labels j))
  have hO := GeneralPaperStockListPayloadStorage.ofFn_bound W (termProfile W m K+2*W+32*W) copied (listFootprint W (termFoot W)) f (by
    intro j
    exact (list_bound W (termProfile W m K) (termFoot W) (f j) (fun t ht => term_bound W t (reference_unit _ t ht))).trans
      (by have h := reference_length (tupleReference j (labels j)); nlinarith only [h]))
  have hF := GeneralPaperStockListPayloadStorage.flatten_bound W (termProfile W m K) 1 m copied (termFoot W) (List.ofFn f)
    (by simp only [List.length_ofFn,le_refl]) (by
      intro xs hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx; exact reference_length _)
    (by intro xs hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx; exact fun t ht => term_bound W t (reference_unit _ t ht))
  have hFrames := budget_frames W labels
  unfold budgetWindow budgetProfile
  dsimp only
  dsimp only [f] at hO hF
  omega

def orderWindow {m K : ℕ} (W copied : ℕ) (j : Fin m) (l : Fin (K-1)) : ℕ :=
  let left := refTerms (reference j (orderLeft l))
  let right := refTerms (reference j (orderRight l))
  referenceWindow W (reference j (orderLeft l))+referenceWindow W (reference j (orderRight l))+
    GeneralPaperStockListPayloadStorage.mapWindow W copied (termFoot W) (termFoot W) (fun t => (t.1,-t.2)) right+
    GeneralPaperPayloadAppendStorage.window W copied (termFoot W) left (right.map (fun t => (t.1,-t.2)))+
    fields W [j.val,l.val,l.val+1,m,K,32*W]+128*W

def orderProfile (W m K : ℕ) : ℕ := 2*referenceProfile W m K+
  GeneralPaperStockListPayloadStorage.mapProfile W (termProfile W m K) (termProfile W m K) 1+
    GeneralPaperPayloadAppendStorage.profile W (termProfile W m K) 2+6*(natBits (controlCap W m K)+W)+160*W

theorem order_bound {m K : ℕ} (W copied : ℕ) (j : Fin m) (l : Fin (K-1)) : orderWindow W copied j l≤orderProfile W m K := by
  let left := refTerms (reference j (orderLeft l))
  let right := refTerms (reference j (orderRight l))
  have hLeft := reference_bound W (reference j (orderLeft l))
  have hRight := reference_bound W (reference j (orderRight l))
  have hNeg : ∀ t∈right,termFoot W (t.1,-t.2)≤termProfile W m K := fun t ht => term_bound W _
    (by simpa only [Int.natAbs_neg] using reference_unit (reference j (orderRight l)) t ht)
  have hMap := GeneralPaperStockListPayloadStorage.map_bound W (termProfile W m K) (termProfile W m K) 1 copied
    (termFoot W) (termFoot W) (fun t => (t.1,-t.2)) right (reference_length _) (fun t ht => term_bound W t (reference_unit _ t ht)) hNeg
  have hAppend := GeneralPaperPayloadAppendStorage.bounded W (termProfile W m K) 2 copied (termFoot W) left (right.map (fun t => (t.1,-t.2)))
    (by rw [List.length_map]; have hl := reference_length (reference j (orderLeft l)); have hr := reference_length (reference j (orderRight l)); dsimp only [left,right]; omega)
    (fun t ht => term_bound W t (reference_unit _ t ht)) (by intro t ht; obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht; exact hNeg u hu)
  have hj := j.isLt
  have hl := l.isLt
  have hPay : 32*W≤(16*m+32)*W := by nlinarith only [Nat.zero_le (m*W)]
  have hf := fields_bound W (natBits (controlCap W m K)) [j.val,l.val,l.val+1,m,K,32*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold controlCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (controlCap W m K)+W)+32*W at hf
  unfold orderWindow orderProfile
  dsimp only
  dsimp only [left,right] at hMap hAppend
  omega

def window {T m K : ℕ} (W copied : ℕ) (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) : ℕ :=
  rowFoot W (termFoot W) (row labels i)+match i with
    | .inl (v,b) => fields W [v.1.val,v.2.val,if b then 1 else 0,16*W]+128*W
    | .inr (.inl (j,l)) => orderWindow W copied j l
    | .inr (.inr i) => budgetWindow W copied (labels i)

def profile (W m K : ℕ) : ℕ := rowProfile W m K+orderProfile W m K+budgetProfile W m K+
  4*(natBits (controlCap W m K)+W)+160*W

theorem bounded {T m K : ℕ} (W copied : ℕ) (hm : 0<m) (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    window W copied labels i≤profile W m K := by
  have hRow := row_bound W hm labels i
  cases i with
  | inl v =>
    have hj := v.1.1.isLt
    have hl := v.1.2.isLt
    have hPay : 16*W≤(16*m+32)*W := by nlinarith only [Nat.zero_le (m*W)]
    have hf := fields_bound W (natBits (controlCap W m K)) [v.1.1.val,v.1.2.val,if v.2 then 1 else 0,16*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl
      · unfold controlCap; omega
      · unfold controlCap; omega
      · split <;> unfold controlCap <;> omega
      · unfold controlCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (controlCap W m K)+W)+32*W at hf
    unfold window profile
    dsimp only
    omega
  | inr v =>
    cases v with
    | inl v =>
      have h := order_bound W copied v.1 v.2
      unfold window profile
      dsimp only
      omega
    | inr i =>
      have h := budget_bound W copied (labels i)
      unfold window profile
      dsimp only
      omega

end Blotto.GeneralPaperStaticRowConstructionStorage

import Blotto.GeneralPaperStoredEndpointRows

/-! Interpolation consumes the two actually returned endpoint rows in one
pass. Each scalar is computed once, and the resulting group values are
materialized once for indexed route emission. -/
namespace Blotto.GeneralPaperStoredInterpolation
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def loop (model : RationalCostModel) (A : ℕ) (budget midpoint : ℚ) : List ℚ → List ℚ → Option (List ℚ) × ℕ
  | [],[] => (some [],64 * (A + 1))
  | p :: left,q :: right =>
    let value := GeneralPaperEqualBitGroups.coordinate model A budget midpoint p q
    let later := loop model A budget midpoint left right
    (later.1.map (List.cons value.1),value.2 + later.2 + rationalWordWidth value.1 + 128 * (A + 1))
  | _,_ => (none,64 * (A + 1))

def price (model : RationalCostModel) (A : ℕ) (budget midpoint : ℚ) : List ℚ → List ℚ → ℕ
  | p :: left,q :: right =>
    let value := GeneralPaperEqualBitGroups.coordinate model A budget midpoint p q
    value.2 + price model A budget midpoint left right + rationalWordWidth value.1 + 128 * (A + 1)
  | _,_ => 64 * (A + 1)

theorem source (model : RationalCostModel) (A : ℕ) (budget midpoint : ℚ) (left right : List ℚ)
    (hLength : left.length = right.length) :
    (loop model A budget midpoint left right).1 = some (List.zipWith (fun p q => budget * ((1 - midpoint) * p + midpoint * q)) left right) ∧
      (loop model A budget midpoint left right).2 = price model A budget midpoint left right := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.eq_nil_of_length_eq_zero hLength.symm
    subst right
    exact ⟨rfl,rfl⟩
  | cons p left ih =>
    cases right with
    | nil => simp only [List.length_cons,List.length_nil] at hLength; omega
    | cons q right =>
      have hTail : left.length = right.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hLength
      obtain ⟨hv,hw⟩ := ih right hTail
      simp only [loop,hv,hw,Option.map_some,GeneralPaperEqualBitGroups.coordinate_data,List.zipWith_cons_cons,price,and_self]

theorem array_rows {m : ℕ} (budget midpoint : ℚ) (left right : FixedArrayTable m ℚ) :
    List.zipWith (fun p q => budget * ((1 - midpoint) * p + midpoint * q)) left.data.toList right.data.toList =
      List.ofFn (fun g : Fin m => budget * ((1 - midpoint) * left.read g + midpoint * right.read g)) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith,Array.length_toList,left.size,right.size,min_self,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_zipWith,Array.getElem_toList,List.getElem_ofFn,FixedArrayTable.read]

def array (model : RationalCostModel) (A : ℕ) (budget midpoint : ℚ) (left right : List ℚ) : Option (Array ℚ) × ℕ :=
  let values := loop model A budget midpoint left right
  match values.1 with
  | none => (none,values.2 + 64 * (A + 1))
  | some rows =>
    let buffer := PaperListReferenceArray.run (fun w => w) A rows
    (some buffer.1,values.2 + buffer.2 + 128 * (A + 1))

theorem array_source {m : ℕ} (model : RationalCostModel) (A : ℕ) (budget midpoint : ℚ) (left right : FixedArrayTable m ℚ) :
    (array model A budget midpoint left.data.toList right.data.toList).1 =
      some (FixedArrayTable.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g))).data ∧
      (array model A budget midpoint left.data.toList right.data.toList).2 = price model A budget midpoint left.data.toList right.data.toList +
        (PaperListReferenceArray.run (fun w => w) A
          (List.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g)))).2 + 128 * (A + 1) := by
  obtain ⟨hv,hw⟩ := source model A budget midpoint left.data.toList right.data.toList (by rw [Array.length_toList,Array.length_toList,left.size,right.size])
  rw [array_rows] at hv
  have hList : (List.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g))).toArray =
      (FixedArrayTable.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g))).data := by
    have h := GeneralPaperRowPrefix.list_ofFn (FixedArrayTable.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g)))
    have hFn : (FixedArrayTable.ofFn (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g))).read =
        (fun g => budget * ((1 - midpoint) * left.read g + midpoint * right.read g)) := by
      funext g
      exact FixedArrayTable.read_ofFn _ g
    rw [hFn] at h
    rw [h,Array.toArray_toList]
  simp only [array,hv,hw,PaperListReferenceArray.data,hList,and_self]

end Blotto.GeneralPaperStoredInterpolation

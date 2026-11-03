import Blotto.WholeQuantileRounding

/-! The actual finite signed order cell of labelled real anchors. There are
m(K-1) anchor variables and one common margin. All field pairs, the fixed
endpoints zero/one, and every labelled tuple against both rational budgets
are included. The original anchors produce a concrete positive feasible
margin by taking the minimum of a finite set of nonzero absolute gaps.
No vertex, rationalization, uniform-label law or optimization oracle is
supplied. The active-vertex/Cramer bounded rational witness is constructed
in the FinitePolytope support modules. The constraints are an existence witness, not runtime
data to be enumerated by the general compiler. -/

namespace Blotto.RationalOrderCell
open Set
open scoped BigOperators Classical

abbrev Variable (m K : ℕ) := Fin m × Fin (K - 1)
abbrev Coordinate (m K : ℕ) := Option (Variable m K)
abbrev Check (m K : ℕ) :=
  (Fin m × (Fin (K + 1) × Fin (K + 1))) ⊕ ((Fin m → Fin K) × Fin 2)
abbrev CellRow (m K : ℕ) := (Coordinate m K × Bool) ⊕ (Check m K × Bool)

theorem coordinate_card (m K : ℕ) : Fintype.card (Coordinate m K) = m * (K - 1) + 1 := by
  simp only [Coordinate,Variable,Fintype.card_option,Fintype.card_prod,Fintype.card_fin]

theorem sum_neg_map {d : Type*} (items : List d) (f : d → ℝ) :
    (items.map (fun v => -f v)).sum = -(items.map f).sum := by
  induction items with
  | nil => simp
  | cons item rest ih => simp only [List.map_cons,List.sum_cons,ih,neg_add_rev]; ring

structure LinearRow (d : Type*) where
  terms : List (d × ℤ)
  bound : ℚ

namespace LinearRow

noncomputable def evaluate {d : Type*} (row : LinearRow d) (x : d → ℝ) : ℝ :=
  (row.terms.map (fun term => (term.2 : ℝ) * x term.1)).sum

noncomputable def residual {d : Type*} (row : LinearRow d) (x : d → ℝ) : ℝ :=
  row.evaluate x - (row.bound : ℝ)

def neg {d : Type*} (row : LinearRow d) : LinearRow d :=
  ⟨row.terms.map (fun term => (term.1,-term.2)),-row.bound⟩

theorem evaluate_neg {d : Type*} (row : LinearRow d) (x : d → ℝ) :
    row.neg.evaluate x = -row.evaluate x := by
  simp only [neg,evaluate,List.map_map,Function.comp_def,Int.cast_neg,neg_mul]
  exact sum_neg_map _ _

theorem residual_neg {d : Type*} (row : LinearRow d) (x : d → ℝ) :
    row.neg.residual x = -row.residual x := by
  rw [residual,evaluate_neg]
  simp only [neg,Rat.cast_neg,residual]
  ring

end LinearRow

abbrev Reference (m K : ℕ) := Option (Option (Variable m K))

def reference {m K : ℕ} (field : Fin m) (label : Fin (K + 1)) : Reference m K :=
  if hZero : label.val = 0 then none
  else if hOne : label.val = K then some none
  else some (some (field,⟨label.val - 1,by have hl := label.isLt; omega⟩))

def refTerms {m K : ℕ} : Reference m K → List (Variable m K × ℤ)
  | none | some none => []
  | some (some v) => [(v,1)]

def refBound {m K : ℕ} : Reference m K → ℚ
  | none => 0
  | some none => 1
  | some (some _) => 0

noncomputable def refValue {m K : ℕ} (a : Variable m K → ℝ) : Reference m K → ℝ
  | none => 0
  | some none => 1
  | some (some v) => a v

theorem refValue_linear {m K : ℕ} (a : Variable m K → ℝ) (r : Reference m K) :
    refValue a r = ((refTerms r).map (fun term => (term.2 : ℝ) * a term.1)).sum + (refBound r : ℝ) := by
  cases r with
  | none => simp [refValue,refTerms,refBound]
  | some r => cases r <;> simp [refValue,refTerms,refBound]

noncomputable def anchor {m K : ℕ} (a : Variable m K → ℝ)
    (field : Fin m) (label : Fin (K + 1)) : ℝ := refValue a (reference field label)

theorem anchor_zero {m K : ℕ} (a : Variable m K → ℝ) (field : Fin m) :
    anchor a field ⟨0,by omega⟩ = 0 := by simp [anchor,reference,refValue]

theorem anchor_one {m K : ℕ} (a : Variable m K → ℝ) (hK : 0 < K) (field : Fin m) :
    anchor a field ⟨K,by omega⟩ = 1 := by simp [anchor,reference,refValue,Nat.ne_of_gt hK]

def tupleReference {m K : ℕ} (field : Fin m) (label : Fin K) : Reference m K :=
  reference field ⟨label.val,by have hl := label.isLt; omega⟩

theorem tupleReference_bound {m K : ℕ} (field : Fin m) (label : Fin K) :
    refBound (tupleReference field label) = 0 := by
  unfold tupleReference reference
  by_cases hZero : label.val = 0
  · simp [hZero,refBound]
  · have hOne : label.val ≠ K := Nat.ne_of_lt label.isLt
    simp [hZero,hOne,refBound]

noncomputable def tupleSum {m K : ℕ} (a : Variable m K → ℝ) (labels : Fin m → Fin K) : ℝ :=
  ∑ field, refValue a (tupleReference field (labels field))

def rawRow {m K : ℕ} (budgets : Fin 2 → ℚ) : Check m K → LinearRow (Variable m K)
  | .inl (field,left,right) =>
      ⟨refTerms (reference field left) ++
          (refTerms (reference field right)).map (fun term => (term.1,-term.2)),
        refBound (reference field right) - refBound (reference field left)⟩
  | .inr (labels,budget) =>
      ⟨(List.ofFn (fun field => refTerms (tupleReference field (labels field)))).flatten,budgets budget⟩

theorem rawRow_order {m K : ℕ} (budgets : Fin 2 → ℚ) (a : Variable m K → ℝ)
    (field : Fin m) (left right : Fin (K + 1)) :
    (rawRow budgets (.inl (field,left,right))).residual a = anchor a field left - anchor a field right := by
  rw [anchor,anchor,refValue_linear,refValue_linear]
  simp only [rawRow,LinearRow.residual,LinearRow.evaluate,List.map_append,List.sum_append,
    List.map_map,Function.comp_def,Int.cast_neg,neg_mul,Rat.cast_sub]
  rw [sum_neg_map]
  ring

theorem rawRow_sum {m K : ℕ} (budgets : Fin 2 → ℚ) (a : Variable m K → ℝ)
    (labels : Fin m → Fin K) (budget : Fin 2) :
    (rawRow budgets (.inr (labels,budget))).residual a = tupleSum a labels - (budgets budget : ℝ) := by
  unfold rawRow LinearRow.residual LinearRow.evaluate tupleSum
  rw [List.map_flatten,List.sum_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
  congr 1
  apply Finset.sum_congr rfl
  intro field _
  rw [refValue_linear,tupleReference_bound,Rat.cast_zero,add_zero]

def liftRow {m K : ℕ} (row : LinearRow (Variable m K)) : LinearRow (Coordinate m K) :=
  ⟨row.terms.map (fun term => (some term.1,term.2)),row.bound⟩

def withMargin {m K : ℕ} (row : LinearRow (Variable m K)) : LinearRow (Coordinate m K) :=
  ⟨(liftRow row).terms ++ [(none,1)],row.bound⟩

noncomputable def point {m K : ℕ} (a : Variable m K → ℝ) (margin : ℝ) : Coordinate m K → ℝ
  | none => margin
  | some v => a v

theorem residual_liftRow {m K : ℕ} (row : LinearRow (Variable m K)) (x : Coordinate m K → ℝ) :
    (liftRow row).residual x = row.residual (fun v => x (some v)) := by
  simp only [liftRow,LinearRow.residual,LinearRow.evaluate,List.map_map,Function.comp_def]

theorem residual_withMargin {m K : ℕ} (row : LinearRow (Variable m K)) (x : Coordinate m K → ℝ) :
    (withMargin row).residual x = row.residual (fun v => x (some v)) + x none := by
  simp only [withMargin,liftRow,LinearRow.residual,LinearRow.evaluate,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.cast_one,one_mul,add_zero]
  simp only [List.map_map,Function.comp_def]
  ring

/-- The orientation is computed from the original real residual. Equality
gets both rational halfspaces; a strict sign gets the common margin. -/
noncomputable def signedRow {m K : ℕ} (original : Variable m K → ℝ)
    (row : LinearRow (Variable m K)) (half : Bool) : LinearRow (Coordinate m K) :=
  if row.residual original < 0 then withMargin row
  else if 0 < row.residual original then withMargin row.neg
  else if half then liftRow row else liftRow row.neg

def boxRow {m K : ℕ} (coordinate : Coordinate m K) (upper : Bool) : LinearRow (Coordinate m K) :=
  if upper then ⟨[(coordinate,1)],1⟩ else ⟨[(coordinate,-1)],0⟩

noncomputable def constraint {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    CellRow m K → LinearRow (Coordinate m K)
  | .inl (coordinate,upper) => boxRow coordinate upper
  | .inr (check,half) => signedRow original (rawRow budgets check) half

def FeasibleCell {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (x : Coordinate m K → ℝ) : Prop :=
  ∀ row : CellRow m K, (constraint budgets original row).residual x ≤ 0

noncomputable def gaps {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) : Finset ℝ :=
  insert 1 (Finset.univ.image (fun check : Check m K =>
    if (rawRow budgets check).residual original = 0 then 1 else |(rawRow budgets check).residual original|))

noncomputable def margin {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) : ℝ :=
  (gaps budgets original).inf' (Finset.insert_nonempty _ _) id

theorem margin_positive {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    0 < margin budgets original := by
  apply (Finset.lt_inf'_iff _).mpr
  intro gap hgap
  rcases Finset.mem_insert.mp hgap with rfl | hgap
  · norm_num
  · obtain ⟨check,_hc,rfl⟩ := Finset.mem_image.mp hgap
    split
    · norm_num
    · exact abs_pos.mpr ‹(rawRow budgets check).residual original ≠ 0›

theorem margin_le_one {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    margin budgets original ≤ 1 :=
  Finset.inf'_le _ (Finset.mem_insert_self _ _)

theorem margin_le_gap {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (check : Check m K) (h : (rawRow budgets check).residual original ≠ 0) :
    margin budgets original ≤ |(rawRow budgets check).residual original| := by
  apply Finset.inf'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨check,Finset.mem_univ _,by rw [ite_eq_right h]; exact abs_eq_max_neg⟩

theorem original_signed_feasible {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (check : Check m K) (half : Bool) :
    (signedRow original (rawRow budgets check) half).residual
      (point original (margin budgets original)) ≤ 0 := by
  unfold signedRow
  split
  · rename_i hNeg
    rw [residual_withMargin]
    change (rawRow budgets check).residual original + margin budgets original ≤ 0
    have hGap := margin_le_gap budgets original check (ne_of_lt hNeg)
    rw [abs_of_neg hNeg] at hGap
    linarith
  · rename_i hNotNeg
    split
    · rename_i hPos
      rw [residual_withMargin,LinearRow.residual_neg]
      change -(rawRow budgets check).residual original + margin budgets original ≤ 0
      have hGap := margin_le_gap budgets original check (ne_of_gt hPos)
      rw [abs_of_pos hPos] at hGap
      linarith
    · rename_i hNotPos
      have hZero : (rawRow budgets check).residual original = 0 := by linarith
      cases half <;> simp only [Bool.false_eq_true,ite_false,ite_true,residual_liftRow,LinearRow.residual_neg]
      all_goals change _ ≤ 0
      all_goals simp only [point,hZero,neg_zero,le_refl]

theorem original_feasible {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    FeasibleCell budgets original (point original (margin budgets original)) := by
  intro row
  cases row with
  | inr check => exact original_signed_feasible budgets original check.1 check.2
  | inl bound =>
    obtain ⟨coordinate,upper⟩ := bound
    have hUnit : point original (margin budgets original) coordinate ∈ Icc (0 : ℝ) 1 := by
      cases coordinate
      · exact ⟨(margin_positive budgets original).le,margin_le_one budgets original⟩
      · exact hOriginal _
    cases upper <;> simp only [constraint,boxRow,Bool.false_eq_true,ite_false,ite_true,
      LinearRow.residual,LinearRow.evaluate,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Int.cast_neg,Int.cast_one,Rat.cast_zero,Rat.cast_one,one_mul,neg_mul,add_zero]
    all_goals linarith [hUnit.1,hUnit.2]

theorem exists_positive_feasible {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ x : Coordinate m K → ℝ, FeasibleCell budgets original x ∧ 0 < x none :=
  ⟨point original (margin budgets original),original_feasible budgets original hOriginal,margin_positive budgets original⟩

theorem feasible_unit {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (x : Coordinate m K → ℝ) (hx : FeasibleCell budgets original x) (coordinate : Coordinate m K) :
    x coordinate ∈ Icc (0 : ℝ) 1 := by
  have hLower := hx (.inl (coordinate,false))
  have hUpper := hx (.inl (coordinate,true))
  simp only [constraint,boxRow,Bool.false_eq_true,ite_false,ite_true,
    LinearRow.residual,LinearRow.evaluate,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Int.cast_neg,Int.cast_one,Rat.cast_zero,Rat.cast_one,one_mul,neg_mul,add_zero] at hLower hUpper
  exact ⟨by linarith,by linarith⟩

def SameSign (first second : ℝ) : Prop :=
  (first < 0 ↔ second < 0) ∧ (first = 0 ↔ second = 0) ∧ (0 < first ↔ 0 < second)

theorem signed_rows_preserve {m K : ℕ} (original : Variable m K → ℝ)
    (row : LinearRow (Variable m K)) (x : Coordinate m K → ℝ) (hMargin : 0 < x none)
    (hx : ∀ half, (signedRow original row half).residual x ≤ 0) :
    SameSign (row.residual original) (row.residual (fun v => x (some v))) := by
  have hTrue := hx true
  have hFalse := hx false
  rcases lt_trichotomy (row.residual original) 0 with hNeg | hZero | hPos
  · simp only [signedRow,ite_eq_left hNeg,residual_withMargin] at hTrue hFalse
    have hNew : row.residual (fun v => x (some v)) < 0 := by linarith
    simp [SameSign,hNeg,hNew,not_lt_of_gt hNeg,not_lt_of_gt hNew,ne_of_lt hNeg,ne_of_lt hNew]
  · simp only [signedRow,hZero,lt_self_iff_false,Bool.false_eq_true,ite_false,ite_true,residual_liftRow,LinearRow.residual_neg] at hTrue hFalse
    have hNew : row.residual (fun v => x (some v)) = 0 := by linarith
    simp [SameSign,hZero,hNew]
  · simp only [signedRow,not_lt_of_gt hPos,ite_false,ite_eq_left hPos,residual_withMargin,LinearRow.residual_neg] at hTrue hFalse
    have hNew : 0 < row.residual (fun v => x (some v)) := by linarith
    simp [SameSign,not_lt_of_gt hPos,not_lt_of_gt hNew,ne_of_gt hPos,ne_of_gt hNew,hPos,hNew]

theorem all_signs_preserved {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (x : Coordinate m K → ℝ) (hx : FeasibleCell budgets original x) (hMargin : 0 < x none)
    (check : Check m K) :
    SameSign ((rawRow budgets check).residual original)
      ((rawRow budgets check).residual (fun v => x (some v))) :=
  signed_rows_preserve original _ x hMargin (fun half => hx (.inr (check,half)))

theorem field_order_preserved {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (x : Coordinate m K → ℝ) (hx : FeasibleCell budgets original x) (hMargin : 0 < x none)
    (field : Fin m) (left right : Fin (K + 1)) :
    (anchor original field left < anchor original field right ↔
      anchor (fun v => x (some v)) field left < anchor (fun v => x (some v)) field right) ∧
    (anchor original field left = anchor original field right ↔
      anchor (fun v => x (some v)) field left = anchor (fun v => x (some v)) field right) ∧
    (anchor original field right < anchor original field left ↔
      anchor (fun v => x (some v)) field right < anchor (fun v => x (some v)) field left) := by
  have h := all_signs_preserved budgets original x hx hMargin (.inl (field,left,right))
  rw [rawRow_order,rawRow_order] at h
  simpa only [SameSign,sub_lt_zero,sub_eq_zero,sub_pos] using h

theorem all_tuple_budgets_preserved {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (x : Coordinate m K → ℝ) (hx : FeasibleCell budgets original x) (hMargin : 0 < x none)
    (labels : Fin m → Fin K) (budget : Fin 2) :
    (tupleSum original labels < (budgets budget : ℝ) ↔
      tupleSum (fun v => x (some v)) labels < (budgets budget : ℝ)) ∧
    (tupleSum original labels = (budgets budget : ℝ) ↔
      tupleSum (fun v => x (some v)) labels = (budgets budget : ℝ)) ∧
    ((budgets budget : ℝ) < tupleSum original labels ↔
      (budgets budget : ℝ) < tupleSum (fun v => x (some v)) labels) := by
  have h := all_signs_preserved budgets original x hx hMargin (.inr (labels,budget))
  rw [rawRow_sum,rawRow_sum] at h
  simpa only [SameSign,sub_lt_zero,sub_eq_zero,sub_pos] using h

theorem refTerms_length {m K : ℕ} (r : Reference m K) : (refTerms r).length ≤ 1 := by
  cases r with
  | none => simp [refTerms]
  | some r => cases r <;> simp [refTerms]

theorem rawRow_order_length {m K : ℕ} (budgets : Fin 2 → ℚ)
    (field : Fin m) (left right : Fin (K + 1)) :
    (rawRow budgets (.inl (field,left,right))).terms.length ≤ 2 := by
  have hl := refTerms_length (reference field left)
  have hr := refTerms_length (reference field right)
  simp only [rawRow,List.length_append,List.length_map]
  omega

theorem rawRow_sum_length {m K : ℕ} (budgets : Fin 2 → ℚ)
    (labels : Fin m → Fin K) (budget : Fin 2) :
    (rawRow budgets (.inr (labels,budget))).terms.length ≤ m := by
  change (List.ofFn (fun field => refTerms (tupleReference field (labels field)))).flatten.length ≤ _
  rw [List.length_flatten,List.map_ofFn,List.sum_ofFn]
  exact (Finset.sum_le_sum (fun field _ => refTerms_length (tupleReference field (labels field)))).trans_eq (by simp)

theorem signedRow_length {m K : ℕ} (original : Variable m K → ℝ)
    (row : LinearRow (Variable m K)) (half : Bool) :
    (signedRow original row half).terms.length ≤ row.terms.length + 1 := by
  unfold signedRow
  split
  · simp [withMargin,liftRow]
  · split
    · simp [withMargin,liftRow,LinearRow.neg]
    · cases half <;> simp [liftRow,LinearRow.neg]

theorem constraint_terms_length {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) : (constraint budgets original row).terms.length ≤ m + 2 := by
  cases row with
  | inl bound =>
    obtain ⟨coordinate,upper⟩ := bound
    cases upper <;> simp [constraint,boxRow]
  | inr signed =>
    have h := signedRow_length original (rawRow budgets signed.1) signed.2
    change (signedRow original (rawRow budgets signed.1) signed.2).terms.length ≤ _
    cases hc : signed.1 with
    | inl order =>
      obtain ⟨field,left,right⟩ := order
      have hl := rawRow_order_length budgets field left right
      rw [hc] at h
      have hf := field.isLt
      omega
    | inr summed =>
      obtain ⟨labels,budget⟩ := summed
      have hl := rawRow_sum_length budgets labels budget
      rw [hc] at h
      omega

def UnitTerms {d : Type*} (row : LinearRow d) : Prop :=
  ∀ term ∈ row.terms, term.2 = 1 ∨ term.2 = -1

theorem refTerms_coefficient {m K : ℕ} (r : Reference m K) (term : Variable m K × ℤ)
    (h : term ∈ refTerms r) : term.2 = 1 := by
  cases r with
  | none => simp [refTerms] at h
  | some r =>
    cases r with
    | none => simp [refTerms] at h
    | some v => simpa only [refTerms,List.mem_singleton] using congrArg Prod.snd (List.mem_singleton.mp h)

theorem unitTerms_neg {d : Type*} (row : LinearRow d) (h : UnitTerms row) : UnitTerms row.neg := by
  intro term ht
  obtain ⟨before,hb,rfl⟩ := List.mem_map.mp ht
  rcases h before hb with hOne | hNeg
  · exact Or.inr (by simp [hOne])
  · exact Or.inl (by simp [hNeg])

theorem rawRow_unitTerms {m K : ℕ} (budgets : Fin 2 → ℚ) (check : Check m K) :
    UnitTerms (rawRow budgets check) := by
  intro term ht
  cases check with
  | inl order =>
    obtain ⟨field,left,right⟩ := order
    rcases List.mem_append.mp ht with hLeft | hRight
    · exact Or.inl (refTerms_coefficient _ term hLeft)
    · obtain ⟨before,hb,rfl⟩ := List.mem_map.mp hRight
      exact Or.inr (by rw [refTerms_coefficient _ before hb])
  | inr summed =>
    obtain ⟨terms,hTerms,hTerm⟩ := List.mem_flatten.mp ht
    obtain ⟨field,rfl⟩ := List.mem_ofFn.mp hTerms
    exact Or.inl (refTerms_coefficient _ term hTerm)

theorem unitTerms_lift {m K : ℕ} (row : LinearRow (Variable m K)) (h : UnitTerms row) :
    UnitTerms (liftRow row) := by
  intro term ht
  obtain ⟨before,hb,rfl⟩ := List.mem_map.mp ht
  exact h before hb

theorem unitTerms_margin {m K : ℕ} (row : LinearRow (Variable m K)) (h : UnitTerms row) :
    UnitTerms (withMargin row) := by
  intro term ht
  rcases List.mem_append.mp ht with hOld | hMargin
  · exact unitTerms_lift row h term hOld
  · obtain rfl := List.mem_singleton.mp hMargin
    exact Or.inl rfl

theorem signedRow_unitTerms {m K : ℕ} (original : Variable m K → ℝ)
    (row : LinearRow (Variable m K)) (h : UnitTerms row) (half : Bool) :
    UnitTerms (signedRow original row half) := by
  unfold signedRow
  split
  · exact unitTerms_margin row h
  · split
    · exact unitTerms_margin row.neg (unitTerms_neg row h)
    · cases half
      · exact unitTerms_lift row.neg (unitTerms_neg row h)
      · exact unitTerms_lift row h

theorem constraint_unitTerms {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) : UnitTerms (constraint budgets original row) := by
  cases row with
  | inl bound =>
    obtain ⟨coordinate,upper⟩ := bound
    cases upper <;> intro term ht <;> simp only [constraint,boxRow,Bool.false_eq_true,
      ite_false,ite_true,List.mem_singleton] at ht <;> cases ht
    · exact Or.inr rfl
    · exact Or.inl rfl
  | inr signed => exact signedRow_unitTerms original _ (rawRow_unitTerms budgets signed.1) signed.2

/-- Clearing the two input rational budgets uses ONE common denominator.
For normalized budgets (1,rho) this product is exactly rho.den. -/
def commonDenominator (budgets : Fin 2 → ℚ) : ℕ := (budgets 0).den * (budgets 1).den

theorem commonDenominator_positive (budgets : Fin 2 → ℚ) : 0 < commonDenominator budgets :=
  Nat.mul_pos (budgets 0).den_pos (budgets 1).den_pos

def IntegralAfter (q : ℕ) (value : ℚ) : Prop := ∃ z : ℤ, (q : ℚ) * value = z

theorem integralAfter_zero (q : ℕ) : IntegralAfter q 0 := ⟨0,by simp⟩
theorem integralAfter_one (q : ℕ) : IntegralAfter q 1 := ⟨q,by simp⟩

theorem integralAfter_neg (q : ℕ) (value : ℚ) (h : IntegralAfter q value) : IntegralAfter q (-value) := by
  obtain ⟨z,hz⟩ := h
  exact ⟨-z,by rw [mul_neg,hz,Int.cast_neg]⟩

theorem integralAfter_sub (q : ℕ) (first second : ℚ)
    (hFirst : IntegralAfter q first) (hSecond : IntegralAfter q second) : IntegralAfter q (first - second) := by
  obtain ⟨z,hz⟩ := hFirst
  obtain ⟨w,hw⟩ := hSecond
  exact ⟨z-w,by rw [mul_sub,hz,hw,Int.cast_sub]⟩

theorem budget_integralAfter (budgets : Fin 2 → ℚ) (which : Fin 2) :
    IntegralAfter (commonDenominator budgets) (budgets which) := by
  have hNum (r : ℚ) : (r.den : ℚ) * r = r.num := by
    have hDen : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    have h := (div_eq_iff hDen).mp r.num_div_den
    exact (mul_comm _ _).trans h.symm
  fin_cases which
  · refine ⟨(budgets 0).num * (budgets 1).den,?_⟩
    simp only [commonDenominator,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    calc
      ((budgets 0).den : ℚ) * (budgets 1).den * budgets 0 = (budgets 1).den * ((budgets 0).den * budgets 0) := by ring
      _ = (budgets 1).den * (budgets 0).num := by rw [hNum]
      _ = (budgets 0).num * (budgets 1).den := by ring
  · refine ⟨(budgets 1).num * (budgets 0).den,?_⟩
    simp only [commonDenominator,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    calc
      ((budgets 0).den : ℚ) * (budgets 1).den * budgets 1 = (budgets 0).den * ((budgets 1).den * budgets 1) := by ring
      _ = (budgets 0).den * (budgets 1).num := by rw [hNum]
      _ = (budgets 1).num * (budgets 0).den := by ring

theorem refBound_integralAfter {m K : ℕ} (q : ℕ) (r : Reference m K) : IntegralAfter q (refBound r) := by
  cases r with
  | none => exact integralAfter_zero q
  | some r =>
    cases r with
    | none => exact integralAfter_one q
    | some v => exact integralAfter_zero q

theorem rawRow_integralAfter {m K : ℕ} (budgets : Fin 2 → ℚ) (check : Check m K) :
    IntegralAfter (commonDenominator budgets) (rawRow budgets check).bound := by
  cases check with
  | inl order => exact integralAfter_sub _ _ _ (refBound_integralAfter _ _) (refBound_integralAfter _ _)
  | inr summed => exact budget_integralAfter budgets summed.2

theorem signedRow_integralAfter {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (check : Check m K) (half : Bool) :
    IntegralAfter (commonDenominator budgets) (signedRow original (rawRow budgets check) half).bound := by
  have h := rawRow_integralAfter budgets check
  unfold signedRow
  split
  · exact h
  · split
    · exact integralAfter_neg _ _ h
    · cases half
      · exact integralAfter_neg _ _ h
      · exact h

theorem constraint_integralAfter {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) :
    IntegralAfter (commonDenominator budgets) (constraint budgets original row).bound := by
  cases row with
  | inl bound =>
    obtain ⟨coordinate,upper⟩ := bound
    cases upper
    · exact integralAfter_zero _
    · exact integralAfter_one _
  | inr signed => exact signedRow_integralAfter budgets original signed.1 signed.2

theorem commonDenominator_normalized (ratio : ℚ) : commonDenominator ![1,ratio] = ratio.den := by
  simp [commonDenominator]

noncomputable def coefficientTerms {d : Type*} [DecidableEq d] (terms : List (d × ℤ)) (coordinate : d) : ℤ :=
  (terms.map (fun term => if term.1 = coordinate then term.2 else 0)).sum

noncomputable def LinearRow.coefficient {d : Type*} [DecidableEq d] (row : LinearRow d) (coordinate : d) : ℤ :=
  coefficientTerms row.terms coordinate

theorem coefficientTerms_mass {d : Type*} [Fintype d] [DecidableEq d]
    (terms : List (d × ℤ)) (hTerms : ∀ term ∈ terms, term.2.natAbs ≤ 1) :
    (∑ coordinate, (coefficientTerms terms coordinate).natAbs) ≤ terms.length := by
  induction terms with
  | nil => simp [coefficientTerms]
  | cons first rest ih =>
    have hRest := ih (fun term ht => hTerms term (List.mem_cons_of_mem _ ht))
    have hFirst := hTerms first List.mem_cons_self
    have hTriangle := Finset.sum_le_sum (s := Finset.univ) (fun coordinate _ =>
      Int.natAbs_add_le (if first.1 = coordinate then first.2 else 0) (coefficientTerms rest coordinate))
    have hSingle : (∑ coordinate : d, (if first.1 = coordinate then first.2 else (0 : ℤ)).natAbs) = first.2.natAbs := by
      simp only [apply_ite Int.natAbs,Int.natAbs_zero]
      simp
    simp only [coefficientTerms,List.map_cons,List.sum_cons,List.length_cons] at hRest ⊢
    simp only [Finset.sum_add_distrib,hSingle] at hTriangle
    change (∑ coordinate, ((if first.1 = coordinate then first.2 else 0) + coefficientTerms rest coordinate).natAbs) ≤ _
    change (∑ coordinate, (coefficientTerms rest coordinate).natAbs) ≤ rest.length at hRest
    omega

theorem coefficientTerms_evaluate {d : Type*} [Fintype d] [DecidableEq d]
    (terms : List (d × ℤ)) (x : d → ℝ) :
    (∑ coordinate, (coefficientTerms terms coordinate : ℝ) * x coordinate) =
      (terms.map (fun term => (term.2 : ℝ) * x term.1)).sum := by
  induction terms with
  | nil => simp [coefficientTerms]
  | cons first rest ih =>
    change (∑ coordinate, (((if first.1 = coordinate then first.2 else 0) + coefficientTerms rest coordinate : ℤ) : ℝ) * x coordinate) =
      (first.2 : ℝ) * x first.1 + (rest.map (fun term => (term.2 : ℝ) * x term.1)).sum
    simp only [Int.cast_add,add_mul,Finset.sum_add_distrib]
    rw [ih]
    congr 1
    simp only [Int.cast_ite,Int.cast_zero,ite_mul,zero_mul]
    simp

theorem LinearRow.evaluate_coefficients {d : Type*} [Fintype d] [DecidableEq d]
    (row : LinearRow d) (x : d → ℝ) :
    row.evaluate x = ∑ coordinate, (row.coefficient coordinate : ℝ) * x coordinate :=
  (coefficientTerms_evaluate row.terms x).symm

theorem constraint_coefficient_mass {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (row : CellRow m K) :
    (∑ coordinate, ((constraint budgets original row).coefficient coordinate).natAbs) ≤ m + 2 := by
  have hUnit := constraint_unitTerms budgets original row
  apply (coefficientTerms_mass (constraint budgets original row).terms ?_).trans
    (constraint_terms_length budgets original row)
  intro term ht
  rcases hUnit term ht with hOne | hNeg
  · simp [hOne]
  · simp [hNeg]

theorem LinearRow.evaluate_continuous {d : Type*} (row : LinearRow d) :
    Continuous row.evaluate := by
  cases row with
  | mk terms bound =>
    induction terms with
    | nil => exact continuous_const
    | cons first rest ih =>
      change Continuous (fun x : d → ℝ => (first.2 : ℝ) * x first.1 + (LinearRow.mk rest bound).evaluate x)
      exact (continuous_const.mul (continuous_apply first.1)).add ih

theorem LinearRow.residual_continuous {d : Type*} (row : LinearRow d) :
    Continuous row.residual :=
  row.evaluate_continuous.sub continuous_const

noncomputable def polytope {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    Set (Coordinate m K → ℝ) := {x | FeasibleCell budgets original x}

theorem polytope_closed {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    IsClosed (polytope budgets original) := by
  have hSet : polytope budgets original = ⋂ row : CellRow m K,
      {x | (constraint budgets original row).residual x ≤ 0} := by
    ext x
    simp [polytope,FeasibleCell]
  rw [hSet]
  exact isClosed_iInter (fun row => isClosed_le (constraint budgets original row).residual_continuous continuous_const)

theorem polytope_compact {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ) :
    IsCompact (polytope budgets original) := by
  have hBox : IsCompact {x : Coordinate m K → ℝ | ∀ coordinate, x coordinate ∈ Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  exact hBox.of_isClosed_subset (polytope_closed budgets original)
    (fun x hx coordinate => feasible_unit budgets original x hx coordinate)

/-- An actual positive-margin maximizer is obtained from the constructed
compact cell. This does not yet assert that it is an active full-rank vertex. -/
theorem exists_positive_margin_maximizer {m K : ℕ} (budgets : Fin 2 → ℚ) (original : Variable m K → ℝ)
    (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ x : Coordinate m K → ℝ, FeasibleCell budgets original x ∧ 0 < x none ∧
      ∀ y, FeasibleCell budgets original y → y none ≤ x none := by
  have hOriginalCell := original_feasible budgets original hOriginal
  obtain ⟨x,hx,hMax⟩ := (polytope_compact budgets original).exists_isMaxOn
    ⟨point original (margin budgets original),hOriginalCell⟩ (continuous_apply none).continuousOn
  refine ⟨x,hx,?_,fun y hy => hMax hy⟩
  have h := hMax hOriginalCell
  exact (margin_positive budgets original).trans_le h

end Blotto.RationalOrderCell

import Blotto.GeneralPaperMeasuredRecordPlanLifetime

/-! Complete counted-list size-plan lifetimes. The current child plan and
left copy are retained once per source element. The recursive output tail
is shared, and one complete output size list is owned at the caller.
Header area pays for control even when a child has an empty payload. -/
namespace Blotto.GeneralPaperMeasuredListPlanLifetime
open GeneralPaperMeasuredBlockPlan (Plan references)
open GeneralPaperMeasuredListBlockPlan (body run)
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def bodyPlan {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (xs : List α) : Plan :=
  ⟨(body model S measure xs).sizes,(body model S measure xs).work⟩

theorem body_positive {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (xs : List α)
    (h : ∀ x ∈ xs,GeneralPaperMeasuredPlanPositive.Positive (measure x)) :
    GeneralPaperMeasuredPlanPositive.Positive (bodyPlan model S measure xs) := by
  intro size hs
  change size ∈ (body model S measure xs).sizes at hs
  rw [GeneralPaperMeasuredListBlockPlan.body_data] at hs
  obtain ⟨sizes,hSizes,hSize⟩ := List.mem_flatten.mp hs
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hSizes
  exact h x hx size hSize

def controls {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (x : α) (xs : List α) : List ℕ :=
  let current := measure x
  let later := body model S measure xs
  let actual := GeneralPaperMeasuredBlockPlan.append S current.sizes later.sizes
  let increment := GeneralPaperNaturalScalarStep.run model S .add later.count 1
  [S,current.work,later.count,later.work,actual.2,increment.2,current.work + later.work,
    current.work + later.work + actual.2,current.work + later.work + actual.2 + increment.2,
    (body model S measure (x :: xs)).work]

def frames {α : Type*} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan) (space : α → ℕ) : List α → ℕ
  | [] => fields S [S,0,(body model S measure []).work] + 64 * S
  | x :: xs => space x + GeneralPaperMeasuredLayoutStorage.planFoot S (measure x) +
    appendFrames S A (measure x).sizes (body model S measure xs).sizes +
    GeneralPaperNaturalScalarLifetime.footprint model S .add (body model S measure xs).count 1 +
    fields S (controls model S measure x xs) + 192 * S + frames model S A measure space xs

theorem frames_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (measure : α → Plan)
    (space : α → ℕ) (xs : List α) (hA : 0 < A) (hGood : ∀ x ∈ xs,Good model S A C (measure x) (space x))
    (hWidth : binaryWordWidth xs.length ≤ A + 8)
    (hCap : (xs.map (fun x => (measure x).sizes.sum)).sum < 2 ^ A)
    (hWork : (body model S measure xs).work ≤ Q) :
    frames model S A measure space xs ≤
      ((xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1) * (C + 8) * unit model S A Q := by
  induction xs with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,0,(body model S measure []).work] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
    nlinarith only [hFields,hUnit,Nat.zero_le (C * unit model S A Q)]
  | cons x xs ih =>
    have hh := hGood x (List.mem_cons_self ..)
    have hWhole := hWork
    change (measure x).work + (body model S measure xs).work +
      (GeneralPaperMeasuredBlockPlan.append S (measure x).sizes (body model S measure xs).sizes).2 +
      (GeneralPaperNaturalScalarStep.run model S .add (body model S measure xs).count 1).2 + 64 * S + 64 ≤ Q at hWork
    have hHeadCap : (measure x).sizes.sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hTailCap : (xs.map (fun y => (measure y).sizes.sum)).sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hTailWidth := (binaryWordWidth_mono (show xs.length ≤ (x :: xs).length by simp only [List.length_cons]; omega)).trans hWidth
    have ht := ih (fun y hy => hGood y (List.mem_cons_of_mem _ hy)) hTailWidth hTailCap (by omega)
    have hChild := hh.2 Q hHeadCap (by omega)
    have hPlan := plan_bound model S A Q (measure x) hh.1 hA hHeadCap (by omega)
    have hAppend := append_bound model S A Q (measure x).sizes (body model S measure xs).sizes hA hh.1 hHeadCap (by omega)
    have hStep := GeneralPaperStoredHeaderPreparationWork.increment_work model S A xs.length hTailWidth
    have hScratch := GeneralPaperNaturalScalarLifetime.bounded model S .add (body model S measure xs).count 1
    rw [GeneralPaperMeasuredListBlockPlan.body_count] at hScratch
    have hFields := fields_bound S (A + 9 + natBits (cap S A Q)) (controls model S measure x xs) (by
      intro z hz
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|hz
      · have h := Nat.add_le_add_left (binaryWordWidth_mono (show z ≤ cap z A Q by unfold cap; omega)) 1
        change natBits z ≤ natBits (cap z A Q) at h
        omega
      · rcases hz with rfl|rfl|hz
        · have h := price_word S A Q (measure x).work (by omega); omega
        · rw [GeneralPaperMeasuredListBlockPlan.body_count]
          unfold natBits; omega
        · have hp : z ≤ Q := by rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
          have h := price_word S A Q z hp; omega)
    change fields S _ ≤ 10 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hScalar := GeneralPaperMeasuredPlanWorkAlgebra.unit_bounds model S A
    have hIncrement : GeneralPaperNaturalScalarLifetime.footprint model S .add xs.length 1 ≤ unit model S A Q := by omega
    have hParent : fields S (controls model S measure x xs) + 192 * S ≤ unit model S A Q := by omega
    simp only [frames,List.map_cons,List.sum_cons,List.length_cons]
    rw [GeneralPaperMeasuredListBlockPlan.body_count]
    nlinarith only [hChild,hPlan,hAppend,hIncrement,hParent,ht,
      Nat.zero_le ((measure x).sizes.sum * unit model S A Q)]

def bodyWindow {α : Type*} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan) (space : α → ℕ) (xs : List α) : ℕ :=
  frames model S A measure space xs + GeneralPaperMeasuredLayoutStorage.planFoot S (bodyPlan model S measure xs) +
    fields S [(body model S measure xs).count,(body model S measure xs).work] + 64 * S

theorem body_bound {α : Type*} (model : RationalCostModel) (S A C Q : ℕ) (measure : α → Plan)
    (space : α → ℕ) (xs : List α) (hA : 0 < A) (hGood : ∀ x ∈ xs,Good model S A C (measure x) (space x))
    (hWidth : binaryWordWidth xs.length ≤ A + 8)
    (hCap : (xs.map (fun x => (measure x).sizes.sum)).sum < 2 ^ A)
    (hWork : (body model S measure xs).work ≤ Q) :
    bodyWindow model S A measure space xs ≤
      ((xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1) * (C + 12) * unit model S A Q := by
  have hFrames := frames_bound model S A C Q measure space xs hA hGood hWidth hCap hWork
  have hPlan := plan_bound model S A Q (bodyPlan model S measure xs)
    (body_positive model S measure xs (fun x hx => (hGood x hx).1)) hA
    (by change (body model S measure xs).sizes.sum < _; rw [GeneralPaperMeasuredListBlockPlan.body_sum]; exact hCap) hWork
  change GeneralPaperMeasuredLayoutStorage.planFoot S (bodyPlan model S measure xs) ≤
    ((body model S measure xs).sizes.sum + 1) * unit model S A Q at hPlan
  rw [GeneralPaperMeasuredListBlockPlan.body_sum] at hPlan
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q))
    [(body model S measure xs).count,(body model S measure xs).work] (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · rw [GeneralPaperMeasuredListBlockPlan.body_count]; unfold natBits; omega
      · have h := price_word S A Q (body model S measure xs).work hWork; omega)
  change fields S _ ≤ 2 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S [(body model S measure xs).count,(body model S measure xs).work] + 64 * S ≤ unit model S A Q := by omega
  have hFactor := Nat.mul_le_mul_right (unit model S A Q)
    (show (xs.map (fun x => (measure x).sizes.sum)).sum + 1 ≤ (xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ (xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1 by omega)
  unfold bodyWindow
  nlinarith only [hFrames,hPlan,hParent,hFactor,hBase]

def window {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan) (space : α → ℕ) (xs : List α) : ℕ :=
  joinWindow S A (references model S A xs.length stride fixed) (bodyPlan model S measure xs)
    (GeneralPaperMeasuredScalarPlanLifetime.referencesWindow model S A xs.length stride fixed)
    (bodyWindow model S A measure space xs)

theorem run_good {α : Type*} (model : RationalCostModel) (S A C stride fixed : ℕ) (measure : α → Plan)
    (space : α → ℕ) (xs : List α) (hA : 0 < A) (hStride : 0 < stride) (hStride64 : stride ≤ 64)
    (hFixed : 0 < fixed) (hFixed64 : fixed ≤ 64) (hGood : ∀ x ∈ xs,Good model S A C (measure x) (space x)) :
    Good model S A (C + 24) (run model S A stride fixed measure xs) (window model S A stride fixed measure space xs) := by
  have hPositive := GeneralPaperMeasuredPlanPositive.list model S A stride fixed measure xs hA (by omega)
    (fun x hx => (hGood x hx).1)
  refine ⟨hPositive,?_⟩
  intro Q hCap hWork
  have hOriginalCap := hCap
  have hRun : run model S A stride fixed measure xs = GeneralPaperMeasuredBlockPlan.join S
      (references model S A xs.length stride fixed) (bodyPlan model S measure xs) := by
    dsimp only [run,bodyPlan]
    rw [GeneralPaperMeasuredListBlockPlan.body_count]
  rw [GeneralPaperMeasuredListPlanWork.area] at hCap ⊢
  have hN : xs.length ≤ A * (stride * xs.length + fixed) := by
    have hs := Nat.mul_le_mul_right xs.length hStride
    have ha := Nat.mul_le_mul_right (stride * xs.length + fixed) hA
    nlinarith only [hs,ha]
  have hCount := binaryWordWidth_le_of_lt_pow hA (show xs.length < 2 ^ A by omega)
  have hStrideW := binaryWordWidth_mono hStride64
  have hFixedW := binaryWordWidth_mono hFixed64
  have h64 : binaryWordWidth 64 = 7 := by decide
  have hHeader := GeneralPaperMeasuredScalarPlanLifetime.references_good model S A xs.length stride fixed hA
    (Nat.mul_pos hA (by omega)) (by omega) (by omega) (by omega)
  have hWhole := hWork
  rw [hRun] at hWork
  change (references model S A xs.length stride fixed).work + (body model S measure xs).work +
    (GeneralPaperMeasuredBlockPlan.append S (references model S A xs.length stride fixed).sizes
      (body model S measure xs).sizes).2 + 64 * S + 64 ≤ Q at hWork
  have hHeaderCap : (references model S A xs.length stride fixed).sizes.sum < 2 ^ A := by
    rw [GeneralPaperMeasuredBlockPlan.references_data]; simp only [List.sum_cons,List.sum_nil,Nat.add_zero]; omega
  have hHeaderSpace := hHeader.2 Q hHeaderCap (by omega)
  simp only [GeneralPaperMeasuredBlockPlan.references_data,List.sum_cons,List.sum_nil,Nat.add_zero] at hHeaderSpace
  have hBodySpace := body_bound model S A C Q measure space xs hA hGood (by omega) (by omega) (by omega)
  have hOverhead := GeneralPaperMeasuredRecordPlanLifetime.join_overhead model S A Q
    (references model S A xs.length stride fixed) (bodyPlan model S measure xs) hA hHeader.1
    (body_positive model S measure xs (fun x hx => (hGood x hx).1)) (by rw [← hRun]; exact hOriginalCap) (by rw [← hRun]; exact hWhole)
  rw [← hRun,GeneralPaperMeasuredListPlanWork.area] at hOverhead
  have hHeaderFactor := Nat.mul_le_mul_right (4 * unit model S A Q)
    (show A * (stride * xs.length + fixed) + 1 ≤ A * (stride * xs.length + fixed) + (xs.map (fun x => (measure x).sizes.sum)).sum + 1 by omega)
  have hBodyFactor := Nat.mul_le_mul_right ((C + 12) * unit model S A Q)
    (show (xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1 ≤
      A * (stride * xs.length + fixed) + (xs.map (fun x => (measure x).sizes.sum)).sum + 1 by omega)
  unfold window
  rw [GeneralPaperMeasuredRecordPlanLifetime.join_window_split]
  nlinarith only [hHeaderSpace,hBodySpace,hOverhead,hHeaderFactor,hBodyFactor]

end Blotto.GeneralPaperMeasuredListPlanLifetime

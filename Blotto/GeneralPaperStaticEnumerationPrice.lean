import Blotto.GeneralPaperPricedListMap

/-! Construct the EXACT native static row index list, including both native
variable-list traversals, all score/field/index constructors and both list
appends. High-score tuples are never enumerated.
-/
namespace Blotto.GeneralPaperStaticEnumerationPrice
open RationalOrderCell GeneralPaperStaticRayRows
set_option autoImplicit false
set_option maxHeartbeats 5000000

def variableRun (W m K : ℕ) : List (Variable m K) × ℕ :=
  let fields := GeneralPaperPricedListStream.flatMap W (fun j =>
    let labels := GeneralPaperPricedListMap.run W (fun l => ((j,l),8*W)) (List.finRange (K-1))
    (labels.1,labels.2+16*((K-1)+1)*W)) (List.finRange m)
  (fields.1,fields.2+16*(m+1)*W)

theorem variable_data (W m K : ℕ) : (variableRun W m K).1=variableList m K := by
  simp only [variableRun,GeneralPaperPricedListStream.flatMap_data,GeneralPaperPricedListMap.data,variableList]

theorem variable_work (W m K : ℕ) : (variableRun W m K).2≤128*(m*(K-1)+m+1)*W := by
  have hInner (j : Fin m) :
      (GeneralPaperPricedListMap.run W (fun l => ((j,l),8*W)) (List.finRange (K-1))).2+
        16*((K-1)+1)*W≤(32*(K-1)+18)*W := by
    have hh := GeneralPaperPricedListMap.work W (8*W) (fun l : Fin (K-1) => ((j,l),8*W))
      (List.finRange (K-1)) (fun _ _ => le_rfl)
    simp only [List.length_finRange] at hh
    nlinarith only [hh]
  have hh := GeneralPaperPricedListStream.flatMap_work W (K-1) ((32*(K-1)+18)*W)
    (fun j : Fin m => let labels := GeneralPaperPricedListMap.run W (fun l => ((j,l),8*W)) (List.finRange (K-1))
      (labels.1,labels.2+16*((K-1)+1)*W)) (List.finRange m)
    (by intro j _; simp only [GeneralPaperPricedListMap.length,List.length_finRange]; exact le_rfl)
    (fun j _ => hInner j)
  simp only [List.length_finRange] at hh
  change _+16*(m+1)*W≤_
  nlinarith only [hh,Nat.zero_le (m*(K-1)*W),Nat.zero_le (m*W)]

def boxesRun (W T m K : ℕ) : List (StaticIndex T m K) × ℕ :=
  let vars := variableRun W m K
  let rows := GeneralPaperPricedListStream.flatMap W
    (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W)) vars.1
  (rows.1,vars.2+rows.2)

theorem boxes_data (W T m K : ℕ) : (boxesRun W T m K).1=boxes T m K := by
  simp only [boxesRun,GeneralPaperPricedListStream.flatMap_data,variable_data,boxes]

theorem boxes_length (W T m K : ℕ) : (boxesRun W T m K).1.length=2*(m*(K-1)) := by
  rw [boxes_data]
  simp [boxes,List.length_flatMap,variableList_length]
  omega

theorem boxes_work (W T m K : ℕ) : (boxesRun W T m K).2≤256*(m*(K-1)+m+1)*W := by
  have hv := variable_work W m K
  have hn : (variableRun W m K).1.length=m*(K-1) := by rw [variable_data,variableList_length]
  have hh := GeneralPaperPricedListStream.flatMap_work W 2 (32*W)
    (fun v => (([.inl (v,false),.inl (v,true)] : List (StaticIndex T m K)),32*W)) (variableRun W m K).1
    (by intro v _; simp only [List.length_cons,List.length_nil]; omega) (fun _ _ => le_rfl)
  rw [hn] at hh
  change (variableRun W m K).2+_≤_
  nlinarith only [hv,hh,Nat.zero_le (m*(K-1)*W),Nat.zero_le (m*W)]

def ordersRun (W T m K : ℕ) : List (StaticIndex T m K) × ℕ :=
  let vars := variableRun W m K
  let rows := GeneralPaperPricedListMap.run W (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) vars.1
  (rows.1,vars.2+rows.2)

theorem orders_data (W T m K : ℕ) : (ordersRun W T m K).1=orders T m K := by
  simp only [ordersRun,GeneralPaperPricedListMap.data,variable_data,orders]

theorem orders_length (W T m K : ℕ) : (ordersRun W T m K).1.length=m*(K-1) := by
  simp only [orders_data,orders,List.length_map,variableList_length]

theorem orders_work (W T m K : ℕ) : (ordersRun W T m K).2≤256*(m*(K-1)+m+1)*W := by
  have hv := variable_work W m K
  have hn : (variableRun W m K).1.length=m*(K-1) := by rw [variable_data,variableList_length]
  have hh := GeneralPaperPricedListMap.work W (8*W)
    (fun v => ((.inr (.inl v) : StaticIndex T m K),8*W)) (variableRun W m K).1 (fun _ _ => le_rfl)
  rw [hn] at hh
  change (variableRun W m K).2+_≤_
  nlinarith only [hv,hh,Nat.zero_le (m*(K-1)*W),Nat.zero_le (m*W)]

def budgetsRun (W T m K : ℕ) : List (StaticIndex T m K) × ℕ :=
  let rows := GeneralPaperPricedListMap.run W (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (List.finRange T)
  (rows.1,rows.2+16*(T+1)*W)

theorem budgets_data (W T m K : ℕ) : (budgetsRun W T m K).1=budgets T m K := by
  simp only [budgetsRun,GeneralPaperPricedListMap.data,budgets]

theorem budgets_work (W T m K : ℕ) : (budgetsRun W T m K).2≤64*(T+1)*W := by
  have hh := GeneralPaperPricedListMap.work W (8*W)
    (fun i => ((.inr (.inr i) : StaticIndex T m K),8*W)) (List.finRange T) (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hh
  change _+16*(T+1)*W≤_
  nlinarith only [hh,Nat.zero_le (T*W)]

def run (W T m K : ℕ) : List (StaticIndex T m K) × ℕ :=
  let b := boxesRun W T m K
  let o := ordersRun W T m K
  let r := budgetsRun W T m K
  (b.1++o.1++r.1,b.2+o.2+r.2+(16*b.1.length+8*o.1.length+16)*W)

theorem data (W T m K : ℕ) : (run W T m K).1=enumerate T m K := by
  simp only [run,boxes_data,orders_data,budgets_data,enumerate]

theorem work (W T m K : ℕ) : (run W T m K).2≤1024*(m*(K-1)+m+T+1)*W := by
  have hb := boxes_work W T m K
  have ho := orders_work W T m K
  have hr := budgets_work W T m K
  change (boxesRun W T m K).2+(ordersRun W T m K).2+(budgetsRun W T m K).2+
    (16*(boxesRun W T m K).1.length+8*(ordersRun W T m K).1.length+16)*W≤_
  rw [boxes_length,orders_length]
  nlinarith only [hb,ho,hr,Nat.zero_le (m*(K-1)*W),Nat.zero_le (m*W),Nat.zero_le (T*W)]

end Blotto.GeneralPaperStaticEnumerationPrice

import Blotto.GeneralPaperSourceSearchStorageRates

/-! Literal filtering/deduplication storage. A returned list shares its
child tail; only one output-list reservation is active during unwinding.
Frames count native work/length/Boolean metadata and actual comparison
scratch. Analytical bounds never enter the executable traversals. -/
namespace Blotto.GeneralPaperCrossingPassStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPricedCrossingPasses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def workCap (W C N : ℕ) : ℕ := (2*C+16*W)*N+2*W
def metadataCap (W C N : ℕ) : ℕ := N+1+3*workCap W C N+2*C+16*W
def listProfile (W P N : ℕ) : ℕ := N*(P+2*W)+32*W
def frameProfile (W P C N : ℕ) : ℕ := 3*P+2*C+11*(natBits (metadataCap W C N)+W)+160*W

def scalarFrame (model : RationalCostModel) (W : ℕ) (a b c : ℚ) (slots : List ℕ) : ℕ :=
  rationalWordWidth a+rationalWordWidth b+rationalWordWidth c+
    model.rat (RationalExpression.pairWidth a b)+model.rat (RationalExpression.pairWidth b c)+fields W slots+128*W

theorem scalar_bound (model : RationalCostModel) (W P C N : ℕ) (a b c : ℚ) (slots : List ℕ)
    (ha : rationalWordWidth a≤P) (hb : rationalWordWidth b≤P) (hc : rationalWordWidth c≤P)
    (hC : model.rat P≤C) (hl : slots.length≤11) (hs : ∀ t∈slots,t≤metadataCap W C N) :
    scalarFrame model W a b c slots≤frameProfile W P C N := by
  have hab := (model.monotone (max_le ha hb)).trans hC
  have hbc := (model.monotone (max_le hb hc)).trans hC
  have hf := fields_bound W (natBits (metadataCap W C N)) slots
    (fun t ht => Nat.add_le_add_left (binaryWordWidth_mono (hs t ht)) 1)
  have hlen := Nat.mul_le_mul_right (natBits (metadataCap W C N)+W) hl
  unfold scalarFrame frameProfile RationalExpression.pairWidth at *
  omega

def filterFrame (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) : List ℚ → ℕ
  | [] => scalarFrame model W lo lo hi [0,2*W]
  | x::rest =>
    let child := filterRun model.rat W lo hi rest
    let result := filterRun model.rat W lo hi (x::rest)
    let a := (leRun model.rat lo x).2
    let b := (leRun model.rat x hi).2
    scalarFrame model W lo x hi [(x::rest).length,child.1.length,result.1.length,child.2,result.2,a,b,
      child.2+a,child.2+a+b,16*W,if lo≤x ∧ x≤hi then 1 else 0]

theorem filter_frame (model : RationalCostModel) (W P C N : ℕ) (lo hi : ℚ) (xs : List ℚ)
    (hn : xs.length≤N) (hl : rationalWordWidth lo≤P) (hh : rationalWordWidth hi≤P)
    (hp : ∀ t∈xs,rationalWordWidth t≤P) (hC : model.rat P≤C) : filterFrame model W lo hi xs≤frameProfile W P C N := by
  cases xs with
  | nil =>
    apply scalar_bound model W P C N lo lo hi _ hl hl hh hC (by simp)
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> unfold metadataCap workCap <;> omega
  | cons x rest =>
    let child := filterRun model.rat W lo hi rest
    let result := filterRun model.rat W lo hi (x::rest)
    let a := (leRun model.rat lo x).2
    let b := (leRun model.rat x hi).2
    have hx := hp x List.mem_cons_self
    have ha : a≤C := (le_work model.rat model.monotone lo x P hl hx).trans hC
    have hb : b≤C := (le_work model.rat model.monotone x hi P hx hh).trans hC
    have hChild := filter_work model.rat model.monotone W P lo hi rest hl hh (fun t ht => hp t (List.mem_cons_of_mem _ ht))
    have hResult := filter_work model.rat model.monotone W P lo hi (x::rest) hl hh hp
    have hChildLen : child.1.length≤N := by
      dsimp only [child]; rw [filter_data]
      exact (List.length_filter_le _ _).trans (by simp only [List.length_cons] at hn; omega)
    have hResultLen : result.1.length≤N := by
      dsimp only [result]; rw [filter_data]
      exact (List.length_filter_le _ _).trans hn
    have hChild' : child.2≤workCap W C N := hChild.trans (by unfold workCap; gcongr; simp only [List.length_cons] at hn; omega)
    have hResult' : result.2≤workCap W C N := hResult.trans (by unfold workCap; gcongr)
    have hBool : (if lo≤x ∧ x≤hi then 1 else 0)≤1 := by split_ifs <;> omega
    refine scalar_bound model W P C N lo x hi
      [(x::rest).length,child.1.length,result.1.length,child.2,result.2,a,b,child.2+a,child.2+a+b,16*W,if lo≤x ∧ x≤hi then 1 else 0]
      hl hx hh hC (by simp) ?_
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; simp only [List.length_cons] at hn ⊢; omega

def filterPeak (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) : List ℚ → ℕ
  | [] => filterFrame model W lo hi []+listFootprint W rationalWordWidth (filterRun model.rat W lo hi []).1
  | x::rest => filterFrame model W lo hi (x::rest)+
      max (listFootprint W rationalWordWidth (filterRun model.rat W lo hi (x::rest)).1) (filterPeak model W lo hi rest)

theorem filter_peak (model : RationalCostModel) (W P C N : ℕ) (lo hi : ℚ) (xs : List ℚ)
    (hn : xs.length≤N) (hl : rationalWordWidth lo≤P) (hh : rationalWordWidth hi≤P)
    (hp : ∀ t∈xs,rationalWordWidth t≤P) (hC : model.rat P≤C) :
    filterPeak model W lo hi xs≤(xs.length+1)*frameProfile W P C N+listProfile W P N := by
  have output (ys : List ℚ) (hy : ys.length≤N) (he : ∀ t∈ys,rationalWordWidth t≤P) :
      listFootprint W rationalWordWidth (filterRun model.rat W lo hi ys).1≤listProfile W P N := by
    rw [filter_data]
    exact (list_bound W P rationalWordWidth _ (fun t ht => he t (List.mem_filter.mp ht).1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans hy)) _)
  induction xs with
  | nil => simpa only [filterPeak,List.length_nil,Nat.zero_add,Nat.one_mul] using
      Nat.add_le_add (filter_frame model W P C N lo hi [] hn hl hh hp hC) (output [] hn hp)
  | cons x rest ih =>
    have hc := ih (by simp only [List.length_cons] at hn; omega) (fun t ht => hp t (List.mem_cons_of_mem _ ht))
    have ho := output (x::rest) hn hp
    have hm := max_le (ho.trans (Nat.le_add_left _ _)) hc
    exact (Nat.add_le_add (filter_frame model W P C N lo hi _ hn hl hh hp hC) hm).trans_eq (by simp only [List.length_cons]; ring)

def afterFrame (model : RationalCostModel) (W : ℕ) (last : ℚ) : List ℚ → ℕ
  | [] => scalarFrame model W last last last [0,2*W]
  | x::rest =>
    let next := if x=last then last else x
    let child := afterRun model.rat W next rest
    let result := afterRun model.rat W last (x::rest)
    let c := model.rat (RationalExpression.pairWidth x last)
    scalarFrame model W last x x [(x::rest).length,child.1.length,result.1.length,child.2,result.2,c,child.2+c,16*W,
      if x=last then 1 else 0]

theorem after_frame (model : RationalCostModel) (W P C N : ℕ) (last : ℚ) (xs : List ℚ)
    (hn : xs.length≤N) (hl : rationalWordWidth last≤P) (hp : ∀ t∈xs,rationalWordWidth t≤P) (hC : model.rat P≤C) :
    afterFrame model W last xs≤frameProfile W P C N := by
  cases xs with
  | nil =>
    apply scalar_bound model W P C N last last last _ hl hl hl hC (by simp)
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> unfold metadataCap workCap <;> omega
  | cons x rest =>
    let next := if x=last then last else x
    let child := afterRun model.rat W next rest
    let result := afterRun model.rat W last (x::rest)
    let c := model.rat (RationalExpression.pairWidth x last)
    have hx := hp x List.mem_cons_self
    have hNext : rationalWordWidth next≤P := by dsimp only [next]; split_ifs <;> assumption
    have hc : c≤C := (model.monotone (max_le hx hl)).trans hC
    have hChild := after_work model.rat model.monotone W P next rest hNext (fun t ht => hp t (List.mem_cons_of_mem _ ht))
    have hResult := after_work model.rat model.monotone W P last (x::rest) hl hp
    have hChildLen : child.1.length≤N := by
      dsimp only [child]; rw [after_data]
      exact (GeneralPaperRaySortedCrossings.after_sublist rest next).length_le.trans (by simp only [List.length_cons] at hn; omega)
    have hResultLen : result.1.length≤N := by
      dsimp only [result]; rw [after_data]
      exact (GeneralPaperRaySortedCrossings.after_sublist _ last).length_le.trans hn
    have hChild' : child.2≤workCap W C N := hChild.trans (by unfold workCap; gcongr <;> (simp only [List.length_cons] at hn; omega))
    have hResult' : result.2≤workCap W C N := hResult.trans (by unfold workCap; gcongr; omega)
    have hBool : (if x=last then 1 else 0)≤1 := by split_ifs <;> omega
    refine scalar_bound model W P C N last x x
      [(x::rest).length,child.1.length,result.1.length,child.2,result.2,c,child.2+c,16*W,if x=last then 1 else 0]
      hl hx hx hC (by simp) ?_
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; simp only [List.length_cons] at hn ⊢; omega

def afterPeak (model : RationalCostModel) (W : ℕ) (last : ℚ) : List ℚ → ℕ
  | [] => afterFrame model W last []+listFootprint W rationalWordWidth (afterRun model.rat W last []).1
  | x::rest => afterFrame model W last (x::rest)+
      max (listFootprint W rationalWordWidth (afterRun model.rat W last (x::rest)).1)
        (afterPeak model W (if x=last then last else x) rest)

theorem after_peak (model : RationalCostModel) (W P C N : ℕ) (last : ℚ) (xs : List ℚ)
    (hn : xs.length≤N) (hl : rationalWordWidth last≤P) (hp : ∀ t∈xs,rationalWordWidth t≤P) (hC : model.rat P≤C) :
    afterPeak model W last xs≤(xs.length+1)*frameProfile W P C N+listProfile W P N := by
  have output (ys : List ℚ) (last : ℚ) (hy : ys.length≤N) (he : ∀ t∈ys,rationalWordWidth t≤P) :
      listFootprint W rationalWordWidth (afterRun model.rat W last ys).1≤listProfile W P N := by
    rw [after_data]
    have hs := GeneralPaperRaySortedCrossings.after_sublist ys last
    exact (list_bound W P rationalWordWidth _ (fun t ht => he t (hs.subset ht))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hs.length_le.trans hy)) _)
  induction xs generalizing last with
  | nil => simpa only [afterPeak,List.length_nil,Nat.zero_add,Nat.one_mul] using
      Nat.add_le_add (after_frame model W P C N last [] hn hl hp hC) (output [] last hn hp)
  | cons x rest ih =>
    have hNext : rationalWordWidth (if x=last then last else x)≤P := by split_ifs; exact hl; exact hp x List.mem_cons_self
    have hc := ih (if x=last then last else x) (by simp only [List.length_cons] at hn; omega) hNext
      (fun t ht => hp t (List.mem_cons_of_mem _ ht))
    have ho := output (x::rest) last hn hp
    have hm := max_le (ho.trans (Nat.le_add_left _ _)) hc
    exact (Nat.add_le_add (after_frame model W P C N last _ hn hl hp hC) hm).trans_eq (by simp only [List.length_cons]; ring)

def uniquePeak (model : RationalCostModel) (W : ℕ) : List ℚ → ℕ
  | [] => scalarFrame model W 0 0 0 [0,2*W]+listFootprint W rationalWordWidth []
  | x::rest =>
    let child := afterRun model.rat W x rest
    let result := uniqueRun model.rat W (x::rest)
    scalarFrame model W x x x [(x::rest).length,child.2,result.2,8*W]+
      max (listFootprint W rationalWordWidth result.1) (afterPeak model W x rest)

theorem unique_peak (model : RationalCostModel) (W P C N : ℕ) (xs : List ℚ)
    (hn : xs.length≤N) (hp : ∀ t∈xs,rationalWordWidth t≤P) (hZero : rationalWordWidth (0:ℚ)≤P) (hC : model.rat P≤C) :
    uniquePeak model W xs≤(xs.length+1)*frameProfile W P C N+listProfile W P N := by
  cases xs with
  | nil =>
    have hf := scalar_bound model W P C N 0 0 0 [0,2*W] hZero hZero hZero hC (by simp) (by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> unfold metadataCap workCap <;> omega)
    have ho : listFootprint W rationalWordWidth ([]:List ℚ)≤listProfile W P N := by unfold listFootprint listProfile; simp
    simpa only [uniquePeak,List.length_nil,Nat.zero_add,Nat.one_mul] using Nat.add_le_add hf ho
  | cons x rest =>
    let child := afterRun model.rat W x rest
    let result := uniqueRun model.rat W (x::rest)
    have hx := hp x List.mem_cons_self
    have ha := after_work model.rat model.monotone W P x rest hx (fun t ht => hp t (List.mem_cons_of_mem _ ht))
    have hu := unique_work model.rat model.monotone W P (x::rest) hp
    have ha' : child.2≤workCap W C N := ha.trans (by unfold workCap; gcongr <;> (simp only [List.length_cons] at hn; omega))
    have hu' : result.2≤workCap W C N := hu.trans (by unfold workCap; gcongr; omega)
    have hf := scalar_bound model W P C N x x x [(x::rest).length,child.2,result.2,8*W] hx hx hx hC (by simp) (by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; simp only [List.length_cons] at hn ⊢; omega)
    have hAfter := after_peak model W P C N x rest (by simp only [List.length_cons] at hn; omega) hx
      (fun t ht => hp t (List.mem_cons_of_mem _ ht)) hC
    have hOut : listFootprint W rationalWordWidth result.1≤listProfile W P N := by
      dsimp only [result]; rw [unique_data]
      have hs := GeneralPaperRaySortedCrossings.unique_sublist (x::rest)
      exact (list_bound W P rationalWordWidth _ (fun t ht => hp t (hs.subset ht))).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hs.length_le.trans hn)) _)
    have hm := max_le (hOut.trans (Nat.le_add_left _ _)) hAfter
    exact (Nat.add_le_add hf hm).trans_eq (by simp only [List.length_cons]; ring)

def profile (W P C N : ℕ) : ℕ := 2*listProfile W P N+(N+2)*frameProfile W P C N+2*P+128*W

def filterWindow (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (xs : List ℚ) : ℕ :=
  listFootprint W rationalWordWidth xs+rationalWordWidth lo+rationalWordWidth hi+filterPeak model W lo hi xs+128*W

theorem filter_window (model : RationalCostModel) (W P C N : ℕ) (lo hi : ℚ) (xs : List ℚ)
    (hn : xs.length≤N) (hl : rationalWordWidth lo≤P) (hh : rationalWordWidth hi≤P)
    (hp : ∀ t∈xs,rationalWordWidth t≤P) (hC : model.rat P≤C) : filterWindow model W lo hi xs≤profile W P C N := by
  have hInput := (list_bound W P rationalWordWidth xs hp).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hk := (filter_peak model W P C N lo hi xs hn hl hh hp hC).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show xs.length+1≤N+2 by omega)) _)
  change listFootprint W rationalWordWidth xs≤listProfile W P N at hInput
  unfold filterWindow profile
  omega

def uniqueWindow (model : RationalCostModel) (W : ℕ) (xs : List ℚ) : ℕ :=
  listFootprint W rationalWordWidth xs+uniquePeak model W xs+128*W

theorem unique_window (model : RationalCostModel) (W P C N : ℕ) (xs : List ℚ)
    (hn : xs.length≤N) (hp : ∀ t∈xs,rationalWordWidth t≤P) (hZero : rationalWordWidth (0:ℚ)≤P) (hC : model.rat P≤C) :
    uniqueWindow model W xs≤profile W P C N := by
  have hInput := (list_bound W P rationalWordWidth xs hp).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hk := (unique_peak model W P C N xs hn hp hZero hC).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show xs.length+1≤N+2 by omega)) _)
  change listFootprint W rationalWordWidth xs≤listProfile W P N at hInput
  unfold uniqueWindow profile
  omega

end Blotto.GeneralPaperCrossingPassStorage

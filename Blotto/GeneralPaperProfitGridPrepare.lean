import Blotto.GeneralPaperFloorSearch

/-! Prepare the fixed profit grid once, with its exact scaled copy for
leaf comparisons and a constructed binary-search depth. Sorting/deduplication
only materializes grid-sized data, never option tuples or code alphabets.
-/
namespace Blotto.GeneralPaperProfitGridPrepare
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 3500000

def ordered (w B : ℕ) : List ℕ := GeneralPaperSortedBreakpoints.ordered (2*denominator w B) (points w B)

def scaled {n : ℕ} (q : ℕ) (values : FixedArrayTable n ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun r => (q*values.read r,16))

structure Prepared (q w B : ℕ) where
  size : ℕ
  numerators : FixedArrayTable size ℕ
  leafNumerators : FixedArrayTable size ℕ
  depth : ℕ
  profitDenominator : ℕ
  scaledWork : ℕ
  depthWork : ℕ
  nonempty : 0<size
  depthCap : size<2^depth

def prepare (q w B : ℕ) : Prepared q w B :=
  let values := ordered w B
  let table : FixedArrayTable values.length ℕ := ⟨values.toArray,by simp⟩
  let leaf := scaled q table
  let cap := GeneralPaperPowerCeiling.ceiling (values.length+1)
  ⟨values.length,table,leaf.1,cap.doublings,denominator w B,leaf.2,cap.work,
    GeneralPaperSortedBreakpoints.ordered_positive _ _,by
      dsimp only [cap]
      have he := GeneralPaperPowerCeiling.ceiling_lower (values.length+1)
      rw [GeneralPaperPowerCeiling.ceiling_power] at he
      omega⟩

theorem read_numerator (q w B : ℕ) (i : Fin (prepare q w B).size) :
    (prepare q w B).numerators.read i=(ordered w B)[i.val]'i.isLt := by
  dsimp only [prepare] at i ⊢
  simp only [FixedArrayTable.read,List.getElem_toArray]
  rfl

theorem denominator_spec (q w B : ℕ) : (prepare q w B).profitDenominator=denominator w B := rfl

theorem numerator_member (q w B : ℕ) (i : Fin (prepare q w B).size) :
    (prepare q w B).numerators.read i∈ordered w B := by
  rw [read_numerator]
  exact List.getElem_mem _

theorem represents (q w B value : ℕ) (hValue : value∈ordered w B) :
    ∃ i, (prepare q w B).numerators.read i=value := by
  obtain ⟨i,hi,hv⟩ := List.getElem_of_mem hValue
  exact ⟨⟨i,hi⟩,by rw [read_numerator]; exact hv⟩

theorem member_iff (w B value : ℕ) : value∈ordered w B ↔ value=0 ∨ value=2*denominator w B ∨ value∈points w B := by
  rw [ordered,GeneralPaperSortedBreakpoints.ordered_mem]
  simp only [List.mem_cons,List.mem_map]
  constructor
  · rintro (h|h|⟨x,hx,he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [Nat.min_eq_left (points_bound w B x hx)] at he
      subst value
      exact Or.inr (Or.inr hx)
  · rintro (h|h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨value,h,Nat.min_eq_left (points_bound w B value h)⟩)

theorem strict (q w B : ℕ) : StrictMono (prepare q w B).numerators.read := by
  intro i j hij
  rw [read_numerator,read_numerator]
  exact List.Pairwise.rel_getElem_of_lt i.isLt j.isLt
    (GeneralPaperSortedBreakpoints.ordered_strict _ _) (show i.val<j.val from hij)

theorem numerator_bound (q w B : ℕ) (i : Fin (prepare q w B).size) :
    (prepare q w B).numerators.read i≤2*denominator w B :=
  GeneralPaperSortedBreakpoints.ordered_bound _ _ _ (numerator_member q w B i)

theorem zero (q w B : ℕ) : (prepare q w B).numerators.read ⟨0,(prepare q w B).nonempty⟩=0 := by
  obtain ⟨i,hi⟩ := represents q w B 0 ((member_iff w B 0).mpr (Or.inl rfl))
  have he := (strict q w B).monotone (show (⟨0,(prepare q w B).nonempty⟩:Fin (prepare q w B).size)≤ i from Nat.zero_le _)
  rw [hi] at he
  omega

theorem upper (q w B : ℕ) :
    (prepare q w B).numerators.read ⟨(prepare q w B).size-1,by have := (prepare q w B).nonempty; omega⟩=2*denominator w B := by
  obtain ⟨i,hi⟩ := represents q w B _ ((member_iff w B _).mpr (Or.inr (Or.inl rfl)))
  have he := (strict q w B).monotone (show i≤⟨(prepare q w B).size-1,by have := (prepare q w B).nonempty; omega⟩ from by
    change i.val≤(prepare q w B).size-1; have := i.isLt; omega)
  rw [hi] at he
  exact le_antisymm (numerator_bound q w B _) he

theorem size_bound (q w B : ℕ) : (prepare q w B).size≤(B+1)*w+2 := by
  have he := GeneralPaperSortedBreakpoints.ordered_length (2*denominator w B) (points w B)
  simpa only [prepare,ordered,points_length] using he

theorem scaled_read (q w B : ℕ) (i : Fin (prepare q w B).size) :
    (prepare q w B).leafNumerators.read i=q*(prepare q w B).numerators.read i := by
  dsimp only [prepare] at i ⊢
  rw [scaled,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem scaled_mono (q w B : ℕ) : Monotone (prepare q w B).leafNumerators.read := by
  intro i j hij
  rw [scaled_read,scaled_read]
  exact Nat.mul_le_mul_left q ((strict q w B).monotone hij)

theorem scaled_zero (q w B : ℕ) : (prepare q w B).leafNumerators.read ⟨0,(prepare q w B).nonempty⟩=0 := by
  rw [scaled_read,zero,Nat.mul_zero]

theorem scaled_work (q w B : ℕ) : (prepare q w B).scaledWork=58*(prepare q w B).size+18 := by
  change (scaled q _).2=58*(ordered w B).length+18
  rw [scaled,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

end Blotto.GeneralPaperProfitGridPrepare

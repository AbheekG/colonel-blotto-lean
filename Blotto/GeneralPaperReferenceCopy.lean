import Blotto.GeneralPaperEqualSelectedPreparationContract

/-! Explicit copy passes between source and destination reference widths.
Array callbacks charge source loads separately from indexed destination
writes. List copies construct fresh head/tail cells. Payload callbacks own
their copied encodings; no host allocator/GC cost is asserted. -/
namespace Blotto.GeneralPaperReferenceCopy
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def scalar {α : Type*} (S D : ℕ) (encode : α → ℕ) (x : α) : α × ℕ :=
  (x,encode x + 32 * (S + D + 1))

def array {α : Type*} {n : ℕ} (S D : ℕ) (copy : α → α × ℕ) (source : FixedArrayTable n α) :
    FixedArrayTable n α × ℕ :=
  let actual := PaperIndexedArrayConstruction.run id D (fun j : Fin n =>
    let loaded := copy (source.read j)
    (loaded.1,loaded.2 + 32 * S + 32))
  (actual.1,actual.2 + 64 * (S + D + 1))

theorem array_data {α : Type*} {n : ℕ} (S D : ℕ) (copy : α → α × ℕ)
    (h : ∀ x,(copy x).1 = x) (source : FixedArrayTable n α) : (array S D copy source).1 = source := by
  apply GeneralPaperNativeQuantizedLabels.table_ext
  intro j
  change (PaperIndexedArrayConstruction.run id D (fun j : Fin n =>
    let loaded := copy (source.read j); (loaded.1,loaded.2 + 32 * S + 32))).1.read j = _
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact h _

theorem array_work {α : Type*} {n : ℕ} (S D : ℕ) (copy : α → α × ℕ) (source : FixedArrayTable n α) :
    (array S D copy source).2 = (∑ j : Fin n,(copy (source.read j)).2) + n * (32 * S + 32) +
      PaperIndexedArrayConstruction.overhead id D n n + 64 * (S + D + 1) := by
  unfold array
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

def arrayPrice (S D n P : ℕ) : ℕ := n * P + n * (32 * S + 32) +
  (n + 1) * (6 * D + 10 * binaryWordWidth (n + 1) + 28) + 64 * (S + D + 1)

theorem array_bound {α : Type*} {n : ℕ} (S D P : ℕ) (copy : α → α × ℕ) (source : FixedArrayTable n α)
    (h : ∀ j,(copy (source.read j)).2 ≤ P) : (array S D copy source).2 ≤ arrayPrice S D n P := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ho := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) D n n le_rfl
  rw [array_work]
  unfold arrayPrice
  nlinarith only [hs,ho]

def list {α : Type*} (S D : ℕ) (copy : α → α × ℕ) : List α → List α × ℕ
  | [] => ([],64 * (S + D + 1))
  | x :: xs =>
    let head := copy x
    let tail := list S D copy xs
    (head.1 :: tail.1,head.2 + tail.2 + 64 * (S + D + 1))

theorem list_data {α : Type*} (S D : ℕ) (copy : α → α × ℕ) (h : ∀ x,(copy x).1 = x) (source : List α) :
    (list S D copy source).1 = source := by
  induction source with
  | nil => rfl
  | cons x xs ih => simp only [list,h,ih]

theorem list_work {α : Type*} (S D : ℕ) (copy : α → α × ℕ) (source : List α) :
    (list S D copy source).2 = (source.map (fun x => (copy x).2)).sum +
      (source.length + 1) * (64 * (S + D + 1)) := by
  induction source with
  | nil => simp only [list,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons x xs ih => simp only [list,List.map_cons,List.sum_cons,List.length_cons,ih]; ring

theorem list_bound {α : Type*} (S D P : ℕ) (copy : α → α × ℕ) (source : List α)
    (h : ∀ x ∈ source,(copy x).2 ≤ P) :
    (list S D copy source).2 ≤ source.length * P + (source.length + 1) * (64 * (S + D + 1)) := by
  have hs := GeneralPaperEncodedScalarStorage.sum_bound (fun x => (copy x).2) P source h
  rw [list_work]
  omega

theorem array_charged {α : Type*} {n : ℕ} (S D c : ℕ) (copy : α → α × ℕ)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hc : 16 ≤ c)
    (h : ∀ j,encode (copy (source.read j)).1 ≤ c * (copy (source.read j)).2) :
    arrayFootprint D encode (array S D copy source).1 ≤ c * (array S D copy source).2 := by
  have ha := GeneralPaperIndexedArrayAllocationCredit.prefix_charged id D c
    (fun j : Fin n => let copied := copy (source.read j); (copied.1,copied.2 + 32 * S + 32)) encode hc
    (fun j => (h j).trans (Nat.mul_le_mul_left c (by dsimp only; omega))) n le_rfl
  have he : GeneralPaperIndexedArrayLifetime.prefixTable id D
      (fun j : Fin n => let copied := copy (source.read j); (copied.1,copied.2 + 32 * S + 32)) n le_rfl =
      (array S D copy source).1 := rfl
  rw [he] at ha
  apply ha.trans
  apply Nat.mul_le_mul_left c
  dsimp only [array,PaperIndexedArrayConstruction.run]
  omega

theorem list_charged {α : Type*} (S D c : ℕ) (copy : α → α × ℕ)
    (encode : α → ℕ) (source : List α) (hc : 16 ≤ c)
    (h : ∀ x ∈ source,encode (copy x).1 ≤ c * (copy x).2) :
    listFootprint D encode (list S D copy source).1 ≤ c * (list S D copy source).2 := by
  induction source with
  | nil => simp only [list,listFootprint,List.map_nil,List.sum_nil,List.length_nil]; nlinarith
  | cons x xs ih =>
    have hh := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [list,listFootprint,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end Blotto.GeneralPaperReferenceCopy

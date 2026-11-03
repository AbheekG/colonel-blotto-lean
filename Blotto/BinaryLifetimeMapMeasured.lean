import Blotto.BinaryLifetimeArray
import Blotto.BinaryPRGHeapTraceUsage

/-! Structural maps call each producer once and retain its actual result.
The counted map is used inside aggregate numerical regions; the traced pure
projection also refines the physical-array map's exact old trace. Charges
are source cell/control work, with native reference/observer costs separate. -/
namespace Blotto.BinaryLifetimeMapMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def map {α β : Type*} (produce : α → β × ℕ) : List α → List β × ℕ
  | [] => ([],2)
  | item::rest =>
      let first := produce item
      let later := map produce rest
      (first.1::later.1,first.2+later.2+4)

theorem map_data {α β : Type*} (produce : α → β × ℕ) (items : List α) :
    (map produce items).1 = BinaryLifetimeArray.mapDirect (fun item => (produce item).1) items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [map,BinaryLifetimeArray.mapDirect,ih]

theorem map_length {α β : Type*} (produce : α → β × ℕ) (items : List α) :
    (map produce items).1.length = items.length := by rw [map_data,BinaryLifetimeArray.mapDirect_length]

theorem map_work {α β : Type*} (produce : α → β × ℕ) (items : List α) :
    (map produce items).2 = (items.map (fun item => (produce item).2)).sum+4*items.length+2 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [map,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

theorem map_bound {α β : Type*} (produce : α → β × ℕ) (items : List α) (P : ℕ)
    (h : ∀ item ∈ items,(produce item).2 ≤ P) : (map produce items).2 ≤ items.length*(P+4)+2 := by
  induction items with
  | nil => simp [map]
  | cons item rest ih =>
      have ht := ih (fun next hn => h next (by simp [hn]))
      have hh := h item (by simp)
      simp only [map,List.length_cons,Nat.add_mul,one_mul]
      omega

def project {α β : Type*} (f : α → β) : List α → (List β × Trace) × ℕ
  | [] => (([],[.frames 1]),2)
  | item::rest =>
      let later := project f rest
      ((f item::later.1.1,[.frames 1,.listAllocation 1]++under 1 later.1.2),later.2+4)

theorem project_erases {α β : Type*} (f : α → β) (items : List α) :
    (project f items).1 = BinaryLifetimeArray.mapDirectWithTrace f items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [project,BinaryLifetimeArray.mapDirectWithTrace,ih]

theorem project_work {α β : Type*} (f : α → β) (items : List α) :
    (project f items).2 = 4*items.length+2 := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [project,List.length_cons,ih]; omega

theorem project_usage {α β : Type*} (f : α → β) (items : List α) :
    usage (project f items).1.2 ≤ 2*items.length+1 := by
  rw [project_erases]
  obtain ⟨hc,ha,hf⟩ := BinaryLifetimeArray.mapDirectWithTrace_bounds f items
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

end Blotto.BinaryLifetimeMapMeasured

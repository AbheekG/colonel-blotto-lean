import Blotto.GeneralPaperReferenceLayoutInstallation

/-! Native selected descriptions supply both reference-pool capacities.
Any valid field headers extracted in actual pool order can be installed and
read together; no independent address/non-aliasing/capacity input is needed.
The two pools retain their different stored word widths. Schema-specific
header extraction and complete draw composition are separate obligations. -/
namespace Blotto.GeneralPaperEqualReferencePoolInstallation
open GeneralPaperReferenceRegionSlots GeneralPaperReferenceRegionProgram GeneralPaperReferenceLayoutInstallation
open GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem inner_from {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (headers : List (Header (innerWidth a)))
    (hFrom : (headers.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner) :
    FromLayout model S (innerWidth a) 0 (inner model S a) headers := hFrom

theorem outer_from {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (headers : List (Header a.address))
    (hFrom : (headers.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer) :
    FromLayout model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary (outer model S a) headers := hFrom

theorem outer_capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (GeneralPaperEqualMeasuredLayout.run model S a).boundary + (outer model S a).sizes.sum < 2 ^ a.address := by
  change (GeneralPaperMeasuredBlockLayout.run model S (innerWidth a) 0 (inner model S a)).2.1 + _ < _
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]
  exact total_capacity model W S k values v hv budget a

theorem inner_read {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (headers : List (Header (innerWidth a)))
    (hFrom : (headers.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hValid : ∀ header ∈ headers,Valid header) (memory : GeneralPaperRawReferenceMemory.Memory (innerWidth a))
    (header : Header (innerWidth a)) (hHeader : header ∈ headers) (j : Fin header.targets.length) :
    (read model (innerWidth a) (prepare model S (innerWidth a) headers memory).memory header.region.reference header.fixed j.val).1 =
      some header.targets[j.val] :=
  GeneralPaperReferenceLayoutInstallation.read_prepared model S (innerWidth a) 0 (inner model S a) headers
    (inner_from model S a headers hFrom) memory (widths_positive a).1 hValid
    (by simpa only [Nat.zero_add] using inner_capacity model W S k values v hv budget a) header hHeader j

theorem outer_read {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (headers : List (Header a.address))
    (hFrom : (headers.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hValid : ∀ header ∈ headers,Valid header) (memory : GeneralPaperRawReferenceMemory.Memory a.address)
    (header : Header a.address) (hHeader : header ∈ headers) (j : Fin header.targets.length) :
    (read model a.address (prepare model S a.address headers memory).memory header.region.reference header.fixed j.val).1 =
      some header.targets[j.val] :=
  GeneralPaperReferenceLayoutInstallation.read_prepared model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary
    (outer model S a) headers (outer_from model S a headers hFrom) memory (widths_positive a).2 hValid
    (outer_capacity model W S k values v hv budget a) header hHeader j

theorem cross_pool_keys {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hInside : (inside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hInsideValid : ∀ header ∈ inside,Valid header) (hOutsideValid : ∀ header ∈ outside,Valid header) :
    List.Disjoint ((collect model S (innerWidth a) inside).entries.map (fun entry => entry.location.value))
      ((collect model S a.address outside).entries.map (fun entry => entry.location.value)) := by
  have hiCap := GeneralPaperReferenceLayoutInstallation.capacities model S (innerWidth a) 0 (inner model S a) inside
    (inner_from model S a inside hInside) (by simpa only [Nat.zero_add] using inner_capacity model W S k values v hv budget a)
  have hoCap := GeneralPaperReferenceLayoutInstallation.capacities model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary
    (outer model S a) outside (outer_from model S a outside hOutside) (outer_capacity model W S k values v hv budget a)
  apply List.disjoint_left.mpr
  intro key hI hO
  obtain ⟨i,hi,hiKey⟩ := List.mem_map.mp hI
  obtain ⟨o,ho,hoKey⟩ := List.mem_map.mp hO
  obtain ⟨ihd,hihd,hiEntry⟩ := (member model S (innerWidth a) inside i).mp hi
  obtain ⟨ohd,hohd,hoEntry⟩ := (member model S a.address outside o).mp ho
  have hIRange := GeneralPaperReferenceRegionSlots.entry_key_in_region model S (innerWidth a) ihd (widths_positive a).1
    (hInsideValid ihd hihd) (hiCap ihd hihd) i hiEntry
  have hORange := GeneralPaperReferenceRegionSlots.entry_key_in_region model S a.address ohd (widths_positive a).2
    (hOutsideValid ohd hohd) (hoCap ohd hohd) o hoEntry
  rw [hiKey] at hIRange
  rw [hoKey] at hORange
  exact Set.disjoint_left.mp (disjoint_pools model S a ihd.region
    (hInside.subset (List.mem_map.mpr ⟨ihd,hihd,rfl⟩)) ohd.region (hOutside.subset (List.mem_map.mpr ⟨ohd,hohd,rfl⟩))) hIRange hORange

end Blotto.GeneralPaperEqualReferencePoolInstallation

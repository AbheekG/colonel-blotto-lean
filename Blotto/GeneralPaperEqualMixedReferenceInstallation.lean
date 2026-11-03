import Blotto.GeneralPaperMixedReferenceRegionProgram

/-! Actual selected native pools instantiate the common RAM installer and
computed local-word readers. Native measured layout derives owner separation,
roots and both capacities, including cross-width key disjointness. Valid
schema-selected headers are still inputs of this component; complete retained
schema extraction, scalar wiring and full draw/pipeline joins remain open. -/
namespace Blotto.GeneralPaperEqualMixedReferenceInstallation
open GeneralPaperReferenceRegionSlots GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def prepare {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (memory : GeneralPaperPayloadMemory.Memory Word) : GeneralPaperMixedReferenceRegionProgram.Prepared :=
  GeneralPaperMixedReferenceRegionProgram.prepare model S (innerWidth a) a.address inside outside memory

theorem inner_read {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hInside : (inside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hInsideValid : ∀ header ∈ inside,Valid header) (hOutsideValid : ∀ header ∈ outside,Valid header)
    (memory : GeneralPaperPayloadMemory.Memory Word) (header : Header (innerWidth a))
    (hHeader : header ∈ inside) (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model (innerWidth a) (prepare model S a inside outside memory).memory
      header.region.reference header.fixed j.val).1 = some (⟨innerWidth a,header.targets[j.val]⟩ : Word) := by
  have hFrom := GeneralPaperEqualReferencePoolInstallation.inner_from model S a inside hInside
  have hCap : 0 + (inner model S a).sizes.sum < 2 ^ innerWidth a := by
    simpa only [Nat.zero_add] using inner_capacity model W S k values v hv budget a
  exact GeneralPaperMixedReferenceRegionProgram.inside_read model S (innerWidth a) a.address inside outside memory
    (widths_positive a).1 hInsideValid
    (GeneralPaperReferenceLayoutInstallation.capacities model S (innerWidth a) 0 (inner model S a) inside hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.roots model S (innerWidth a) 0 (inner model S a) inside hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.owners model S (innerWidth a) 0 (inner model S a) inside hFrom)
    (GeneralPaperEqualReferencePoolInstallation.cross_pool_keys model W S k values v hv budget a inside outside hInside hOutside
      hInsideValid hOutsideValid) header hHeader j

theorem outer_read {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hOutsideValid : ∀ header ∈ outside,Valid header)
    (memory : GeneralPaperPayloadMemory.Memory Word) (header : Header a.address)
    (hHeader : header ∈ outside) (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model a.address (prepare model S a inside outside memory).memory
      header.region.reference header.fixed j.val).1 = some (⟨a.address,header.targets[j.val]⟩ : Word) := by
  have hFrom := GeneralPaperEqualReferencePoolInstallation.outer_from model S a outside hOutside
  have hCap := GeneralPaperEqualReferencePoolInstallation.outer_capacity model W S k values v hv budget a
  exact GeneralPaperMixedReferenceRegionProgram.outside_read model S (innerWidth a) a.address inside outside memory
    (widths_positive a).2 hOutsideValid
    (GeneralPaperReferenceLayoutInstallation.capacities model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary
      (outer model S a) outside hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.roots model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary
      (outer model S a) outside hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.owners model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary
      (outer model S a) outside hFrom) header hHeader j

theorem inner_read_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hInside : (inside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).inner)
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hInsideValid : ∀ header ∈ inside,Valid header) (hOutsideValid : ∀ header ∈ outside,Valid header)
    (memory : GeneralPaperPayloadMemory.Memory Word) (header : Header (innerWidth a))
    (hHeader : header ∈ inside) (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model (innerWidth a) (prepare model S a inside outside memory).memory
      header.region.reference header.fixed j.val).2 =
      (GeneralPaperStoredWordEncoding.word model (innerWidth a) (innerWidth a) 0).2 +
      (GeneralPaperReferenceSlotConstruction.run model (innerWidth a) (innerWidth a) header.region.reference.value header.fixed 1 j.val 0
        (GeneralPaperStoredWordEncoding.word model (innerWidth a) (innerWidth a) 0).1).2 + 129 * innerWidth a + 128 :=
  GeneralPaperMixedReferenceRegionProgram.read_work_of_some model (innerWidth a) _ header.region.reference header.fixed j.val _
    (inner_read model W S k values v hv budget a inside outside hInside hOutside hInsideValid hOutsideValid memory header hHeader j)

theorem outer_read_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (inside : List (Header (innerWidth a))) (outside : List (Header a.address))
    (hOutside : (outside.map Header.region).Sublist (GeneralPaperEqualMeasuredLayout.run model S a).outer)
    (hOutsideValid : ∀ header ∈ outside,Valid header)
    (memory : GeneralPaperPayloadMemory.Memory Word) (header : Header a.address)
    (hHeader : header ∈ outside) (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model a.address (prepare model S a inside outside memory).memory
      header.region.reference header.fixed j.val).2 =
      (GeneralPaperStoredWordEncoding.word model a.address a.address 0).2 +
      (GeneralPaperReferenceSlotConstruction.run model a.address a.address header.region.reference.value header.fixed 1 j.val 0
        (GeneralPaperStoredWordEncoding.word model a.address a.address 0).1).2 + 129 * a.address + 128 :=
  GeneralPaperMixedReferenceRegionProgram.read_work_of_some model a.address _ header.region.reference header.fixed j.val _
    (outer_read model W S k values v hv budget a inside outside hOutside hOutsideValid memory header hHeader j)

end Blotto.GeneralPaperEqualMixedReferenceInstallation

import Blotto.BinaryPRGHeapResourcePolynomial
import Blotto.BinaryPRGResourceWork

/-! The actual prepared PRG request supplies all canonical, lattice, box and
word-width premises of the physical array-to-native resource runner. -/

namespace Blotto.BinaryPRGHeapResourceRequest
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork

variable {n : ℕ}

def run (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) :
    BinaryPRGWordControllerResource.Result seed (resourceInput request rich).length × ℕ :=
  BinaryPRGHeapResourceMaterialization.runNativeWithWork seed
    (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2

theorem run_erasure (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) : (run seed request rich).1 =
      BinaryPRGWordControllerResource.requestRun seed request rich :=
  BinaryPRGHeapResourceMaterialization.runNativeWithWork_reference _ _ _ _ _

theorem input_widths (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (∀ j,width ((resourceInput request rich).length.read j) ≤
      BinaryPRGWordControllerBooleanResourceLoopWork.widthBound request.source.normalizedInput.latticeDenominator) ∧
    (∀ j,width ((resourceInput request rich).resource.read j) ≤
      BinaryPRGWordControllerBooleanResourceLoopWork.widthBound request.source.normalizedInput.latticeDenominator) := by
  obtain ⟨hl,hr,hb,hrb⟩ := resource_lattice_boxes request rich
  have hD := request.source.normalizedInput.latticeDenominator_pos
  have hNative := BinaryGeneralResourceLattice.initial_invariant
    (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
    request.source.normalizedInput.latticeDenominator hr hrb
  constructor
  · intro j
    have h := BinaryGeneralResourceLattice.capacity_wordWidth
      (resourceInput request rich).length (resource_canonical request rich).2.1
      _ hD hl hb j
    unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  · intro j
    have h := BinaryGeneralResourceLattice.state_wordWidth
      (BinaryResourcePair.initial (resourceInput request rich).length
        (resourceInput request rich).resource (resource_canonical request rich).2.1
        (resource_canonical request rich).2.2) _ hD (fun j => (hb j).2) hNative j
    change width ((resourceInput request rich).resource.read j) ≤ _ at h
    unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega

noncomputable def bound (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapResourceInputCost.nativeBound n
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound request.source.normalizedInput.latticeDenominator)
    request.source.normalizedInput.latticeDenominator indexWidth seedCap

theorem run_bound (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) : (run seed request rich).2 ≤ bound request seed.width seed.cap.value := by
  obtain ⟨hl,hr,hb,hrb⟩ := resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := input_widths request rich
  exact BinaryPRGHeapResourceInputCost.runNativeWithWork_input_bound _ _ _ _ _ _ _
    (by unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    request.source.normalizedInput.latticeDenominator_pos hcWidth hrWidth hl hb hr hrb

theorem uniform_request_work_bound : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool),
      (run seed request rich).2 ≤
        C * (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 1)^d := by
  rcases BinaryPRGHeapResourcePolynomial.uniform_native_work_bound with ⟨C,d,hBound⟩
  refine ⟨C * 7^d,d,?_⟩
  intro n seed request rich
  obtain ⟨hl,hr,hb,hrb⟩ := resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := input_widths request rich
  have h := hBound seed (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 _ _
    (by unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    request.source.normalizedInput.latticeDenominator_pos hcWidth hrWidth hl hb hr hrb
  have hWidth := request.source.normalized_lattice_wordWidth_original
  have hSize : n + BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      request.source.normalizedInput.latticeDenominator +
      binaryWordWidth request.source.normalizedInput.latticeDenominator + seed.width + seed.cap.value + 1 ≤
      7 * (n + request.source.originalInputWordWidth + seed.width + seed.cap.value + 1) := by
    unfold BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

end Blotto.BinaryPRGHeapResourceRequest

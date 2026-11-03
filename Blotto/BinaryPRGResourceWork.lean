import Blotto.BinaryPRGRequest
import Blotto.BinaryGeneralResourceRunWork
import Blotto.RationalPRGRequestInputWords

/-! Both actual prepared original-game resource inputs derive their lattice,
unit boxes and native resource-work bounds. The request's semantic original
input width is derived from successful parsing on arbitrary frames. No caller
supplies a resource-state, width, source-construction or primitive-price oracle.
Boolean arithmetic, logical access/control and conservative full-table copies
remain separate charges; full terminal/backend/physical-space costs are open. -/

namespace Blotto.BinaryPRGResourceWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGPreparation
open BinaryGeneralResourceExecution BinaryGeneralResourceRunWork

def resourceInput {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : BinaryLottoResourceInput.Input n :=
  if rich then request.prepared.rich else request.prepared.poor

theorem resource_canonical {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (resourceInput request rich).Canonical := by
  cases rich
  · exact request.prepared.poor_canonical request.valid
  · exact request.prepared.rich_canonical request.valid

theorem resource_admissible {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryLottoResourceInput.Admissible (resourceInput request rich) := by
  cases rich
  · exact request.prepared.poor_admissible request.valid
  · exact request.prepared.rich_admissible request.valid

noncomputable def sourceSystem {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : RationalLottoResourceSystem n :=
  if rich then request.source.normalizedInput.richNativeSystem else request.source.normalizedInput.poorNativeSystem

theorem resource_refines {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (resourceInput request rich).Refines (sourceSystem request rich) := by
  cases rich
  · exact request.prepared.poor_refines request.valid
  · exact request.prepared.rich_refines request.valid

theorem source_unit {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (sourceSystem request rich).B ≤ 1 := by
  cases rich
  · exact request.source.normalizedInput.b_le
  · exact le_rfl

theorem source_length_lattice {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    ∀ j, OnRationalLattice request.source.normalizedInput.latticeDenominator ((sourceSystem request rich).length j) := by
  cases rich <;> exact request.source.normalizedInput.lengths_on_lattice

theorem source_initial_lattice {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    ∀ j, OnRationalLattice request.source.normalizedInput.latticeDenominator ((sourceSystem request rich).initial j) := by
  cases rich
  · exact request.source.normalizedInput.poorInitial_on_lattice
  · exact request.source.normalizedInput.richInitial_on_lattice

def resourceWork {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (Option (BinaryResourcePair.Certified (resourceInput request rich).length) × ℕ) × Charge :=
  initialRun (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2 N bits

theorem resourceWork_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWork request rich N bits).1 =
      BinaryLottoResourceInput.run (resourceInput request rich) (resource_canonical request rich) N bits := by
  rw [resourceWork, initialRun_state]
  rfl

theorem resourceWork_position {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) : (resourceWork request rich N bits).1.2 ≤ N :=
  initialRun_bitReads_le _ _ _ _ N bits

theorem resource_lattice_boxes {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (∀ j, OnRationalLattice request.source.normalizedInput.latticeDenominator
      (value ((resourceInput request rich).length.read j))) ∧
    (∀ j, OnRationalLattice request.source.normalizedInput.latticeDenominator
      (value ((resourceInput request rich).resource.read j))) ∧
    (∀ j, 0 ≤ value ((resourceInput request rich).length.read j) ∧
      value ((resourceInput request rich).length.read j) ≤ 1) ∧
    (∀ j, 0 ≤ value ((resourceInput request rich).resource.read j) ∧
      value ((resourceInput request rich).resource.read j) ≤ value ((resourceInput request rich).length.read j)) := by
  have hr := resource_refines request rich
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; rw [hr.2.1 j]; exact source_length_lattice request rich j
  · intro j; rw [hr.2.2 j]; exact source_initial_lattice request rich j
  · intro j; rw [hr.2.1 j]
    exact ⟨((sourceSystem request rich).length_pos j).le,
      ((sourceSystem request rich).length_le j).trans (source_unit request rich)⟩
  · intro j; rw [hr.2.2 j, hr.2.1 j]; exact (sourceSystem request rich).initial_box j

theorem resource_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWork request rich N bits).2.booleanWork ≤
      7100000 * n * (request.source.originalInputWordWidth + 2) ^ 3 +
        52 * N * (request.source.originalInputWordWidth + 2) := by
  have h := validLotto_initialRun_boolean_bound (resourceInput request rich) (sourceSystem request rich)
    (resource_canonical request rich) (resource_refines request rich)
    request.source.normalizedInput.latticeDenominator request.source.normalizedInput.latticeDenominator_pos
    (source_unit request rich) (source_length_lattice request rich) (source_initial_lattice request rich) N bits
  have hw : binaryWordWidth request.source.normalizedInput.latticeDenominator + 1 ≤
      request.source.originalInputWordWidth + 2 := by
    have hd := request.source.normalized_lattice_wordWidth_original
    omega
  exact h.trans (Nat.add_le_add
    (Nat.mul_le_mul_left (7100000 * n) (Nat.pow_le_pow_left hw 3))
    (Nat.mul_le_mul_left (52 * N) hw))

theorem resource_access_copy_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWork request rich N bits).2.reads ≤ 2 * n + 14 * (n - 1) + N ∧
    (resourceWork request rich N bits).2.writes ≤ 2 * (n - 1) ∧
    (resourceWork request rich N bits).2.listControl ≤ 6 * n + 3 + 26 * (n - 1) + 4 * N ∧
    (resourceWork request rich N bits).2.copyAllowance ≤
      (n - 1) * (8 * (7 + 4 * request.source.originalInputWordWidth) + 4 +
        4 * (n + 1) * (7 + 4 * request.source.originalInputWordWidth)) := by
  obtain ⟨hL, hR, hCB, hRB⟩ := resource_lattice_boxes request rich
  have h := initialRun_access_copy_bound (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
    request.source.normalizedInput.latticeDenominator request.source.normalizedInput.latticeDenominator_pos
    hL hR hCB hRB N bits
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans ?_⟩
  have hd := request.source.normalized_lattice_wordWidth_original
  have hw : 3 + 4 * binaryWordWidth request.source.normalizedInput.latticeDenominator ≤
      7 + 4 * request.source.originalInputWordWidth := by omega
  gcongr

theorem parsed_original_wordWidth {n : ℕ} (frame suffix : List Bool) (request : BinaryPRGRequest.Request n)
    (h : BinaryPRGRequest.read frame = some (⟨n, request⟩, suffix)) :
    request.source.originalInputWordWidth ≤ (frame.length + 2) * (4 * frame.length + 13) := by
  have hr := BinaryPRGRequest.read_refines frame
  rw [h, Option.map_some] at hr
  exact RationalPRGBinaryRequest.readWords_inputWordWidth frame (⟨n, request.source⟩)
    request.accuracy suffix hr.symm

theorem parsed_resource_boolean_bound {n : ℕ} (frame suffix : List Bool) (request : BinaryPRGRequest.Request n)
    (h : BinaryPRGRequest.read frame = some (⟨n, request⟩, suffix)) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWork request rich N bits).2.booleanWork ≤
      7100000 * n * ((frame.length + 2) * (4 * frame.length + 13) + 2) ^ 3 +
        52 * N * ((frame.length + 2) * (4 * frame.length + 13) + 2) := by
  have hw := Nat.add_le_add_right (parsed_original_wordWidth frame suffix request h) 2
  exact (resource_boolean_bound request rich N bits).trans (Nat.add_le_add
    (Nat.mul_le_mul_left (7100000 * n) (Nat.pow_le_pow_left hw 3))
    (Nat.mul_le_mul_left (52 * N) hw))

end Blotto.BinaryPRGResourceWork

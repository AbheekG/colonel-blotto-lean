import Blotto.BinaryFourPartialRun
import Blotto.BinaryFourSpecSampler

/-! Native unsorted partial four coupling retains exact source-machine output,
none and absolute reader position. Coordinate restoration never creates a
fallback, so the outer global PRG can use its original B-zero exhaustion row. -/

namespace Blotto.BinaryFourSpecPartialRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourSpecSampler

noncomputable def sourceRow (row : FixedArrayTable 4 SignedWord) : Fin 4 → ℚ := fun j => value (row.read j)

def runIndexed (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let result := BinaryFourPartialRun.runIndexed (orderedInput input) (orderedInput_canonical input hC)
    (orderedInput_admissible input hC hAd) K N outer scalar bits pos hp
  (result.1.map (fun row => FixedArrayTable.ofFn (fun j => row.read (permutation input j))),result.2)

theorem runIndexed_refines (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((runIndexed input hC hAd K N outer scalar bits pos hp).1.map sourceRow,(runIndexed input hC hAd K N outer scalar bits pos hp).2) =
      (source.machine K outer scalar).runCursorIndexed N bits (.state (source.input.start K outer scalar)) pos hp := by
  have he := BinaryFourPartialRun.runIndexed_refines (orderedInput input) source.input (orderedInput_canonical input hC)
    (orderedInput_refines input source hC hr) (orderedInput_admissible input hC hAd) K N outer scalar bits pos hp
  unfold runIndexed RationalFourSpec.machine
  rw [WordMappedIndexedRefinement.indexed_refines]
  have hf := congrArg (WordMappedIndexedRefinement.mapResult (RationalAffineAllocation.permutation source.permutation).value) he
  simp only [WordMappedIndexedRefinement.mapResult,Option.map_map,Function.comp_def] at hf ⊢
  apply Prod.ext
  · apply Eq.trans _ (congrArg Prod.fst hf)
    apply congrArg (fun f => (BinaryFourPartialRun.runIndexed (orderedInput input) (orderedInput_canonical input hC)
      (orderedInput_admissible input hC hAd) K N outer scalar bits pos hp).1.map f)
    funext row j
    unfold sourceRow
    rw [FixedArrayTable.read_ofFn,permutation_refines input source hC hr]
    exact (BinaryTerminalProfileCompiler.permutation_value source.permutation (fun j => value (row.read j)) j).symm
  · have hPosition := congrArg (fun result : Option (Fin 4 → ℚ) × ℕ => result.2) hf
    exact hPosition

theorem runIndexed_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (row : FixedArrayTable 4 SignedWord) (hs : (runIndexed input hC hAd K N outer scalar bits pos hp).1=some row) :
    ∀ j, CanonicalWord (row.read j) := by
  obtain ⟨old,hOld,rfl⟩ := Option.map_eq_some_iff.mp hs
  have hc := BinaryFourPartialRun.runIndexed_canonical _ (orderedInput_canonical input hC) (orderedInput_admissible input hC hAd)
    K N outer scalar bits pos hp old hOld
  intro j
  rw [FixedArrayTable.read_ofFn]
  exact hc _

end Blotto.BinaryFourSpecPartialRun

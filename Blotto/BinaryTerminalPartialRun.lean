import Blotto.BinaryGroupPartialRun
import Blotto.BinaryTerminalSampler
import Blotto.GroupEmissionTransport
import Blotto.RationalTerminalProgram
import Blotto.BinaryRoutePartialRefinement

/-! The native terminal partial coupling emits whole original allocations
without swallowing exhaustion. It retains the caller's reader/cap/position,
so the general PRG supplies its original B-zero fallback at the outer level. -/

namespace Blotto.BinaryTerminalPartialRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping BinaryTerminalGroupInputs BinaryTerminalPromises

noncomputable def sourceRow {n : ℕ} (row : FixedArrayTable n SignedWord) : Fin n → ℚ := fun j => value (row.read j)

def runIndexed {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable n SignedWord) × ℕ :=
  let routes := BinaryTerminalRoutes.prepare input
  match hs : pivot input with
  | none =>
      let result := BinaryGroupPartialRun.uniformRun (BinaryTerminalGroupInputs.uniform input) (uniform_canonical input hC)
        (uniformAdmissible input hC hAd hs) (groupCount input hC hAd) K N scalar bits pos hp
      (result.1.map (BinaryGroupRoutes.emit routes),result.2)
  | some selected =>
      let result := BinaryGroupPartialRun.mixedRun (mixed input selected) (mixed_canonical input hC selected)
        (mixedAdmissible input hC hAd selected hs) (groupCount input hC hAd) K N outer scalar bits pos hp
      (result.1.map (BinaryGroupRoutes.emitMixed routes selected),result.2)

theorem runIndexed_refines {n : ℕ} (input : Input n) (source : RationalTerminalLotto n) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    ((runIndexed input hC hAd K N outer scalar bits pos hp).1.map sourceRow,(runIndexed input hC hAd K N outer scalar bits pos hp).2) =
      (source.program K outer scalar).machine.runCursorIndexed N bits (.state (source.program K outer scalar).start) pos hp := by
  rw [source.program_refines]
  unfold runIndexed RationalTerminalLotto.programReference
  dsimp only
  have hRoutes := BinaryTerminalRoutes.prepare_refines input source hC hr
  have hCanon := BinaryTerminalRoutes.prepare_canonical input hC
  have hPivot := pivot_refines input source hC hr
  split
  · rename_i hn
    have hs : source.pivot=none := hPivot.symm.trans hn
    split
    · rename_i hsn
      dsimp only [RationalAllocationProgram.widen,RationalAllocationProgram.mapped]
      rw [WordMappedIndexedRefinement.indexed_refines]
      have hRun := BinaryGroupPartialRun.uniformRun_transport
        (congrArg List.length (groups_refines input source hC hr)).symm (BinaryTerminalGroupInputs.uniform input)
        (source.uniformSpec (source.pivot_none hs)) (uniform_canonical input hC)
        (uniform_refines input source hC hr hs) (uniformAdmissible input hC hAd hn)
        source.groups_count (groupCount input hC hAd) K N scalar bits pos hp
      have hEmit := BinaryRoutePartialRefinement.emit_option (BinaryTerminalRoutes.prepare input)
        (BinaryTerminalRoutes.sourcePartition input source hC hr) hCanon hRoutes
        (BinaryGroupPartialRun.uniformRun (BinaryTerminalGroupInputs.uniform input)
          (uniform_canonical input hC) (uniformAdmissible input hC hAd hn) (groupCount input hC hAd) K N scalar bits pos hp).1
        (fun row hrow => BinaryGroupPartialRun.uniformRun_canonical (BinaryTerminalGroupInputs.uniform input)
          (uniform_canonical input hC) (uniformAdmissible input hC hAd hn) (groupCount input hC hAd) K N scalar bits pos hp row hrow)
      apply Prod.ext
      · dsimp only
        change Option.map BinaryRoutePartialRefinement.sourceRow _=_
        rw [hEmit]
        -- Transport the original group-coordinate row, then map the original split.
        have hm := congrArg (WordMappedIndexedRefinement.mapResult (fun y => (source.partition.emit source.partition.routes y).allocation)) hRun
        simp only [WordMappedIndexedRefinement.mapResult,Option.map_map,Function.comp_def] at hm
        dsimp only [WordMappedIndexedRefinement.mapResult]
        simp only [PreparedGroupOutput.emit_allocation]
        apply Eq.trans _ (congrArg Prod.fst hm)
        dsimp only
        rw [Option.map_map]
        apply congrArg (fun f => (BinaryGroupPartialRun.uniformRun (BinaryTerminalGroupInputs.uniform input)
          (uniform_canonical input hC) (uniformAdmissible input hC hAd hn) (groupCount input hC hAd) K N scalar bits pos hp).1.map f)
        funext row j
        exact BinaryTerminalRoutes.transport_emit _ source.partition (fun g => value (row.read g)) j
      · exact congrArg (fun result : Option (Fin source.groups.length → ℚ) × ℕ => result.2) hRun
    · rename_i selected bad
      rw [hs] at bad
      cases bad
  · rename_i selected hn
    have hs : source.pivot=some selected := hPivot.symm.trans hn
    split
    · rename_i bad
      rw [hs] at bad
      cases bad
    · rename_i pivot hsp
      have he : pivot=selected := Option.some.inj (hsp.symm.trans hs)
      subst pivot
      dsimp only [RationalAllocationProgram.mapped]
      rw [WordMappedIndexedRefinement.indexed_refines]
      have hRun := BinaryGroupPartialRun.mixedRun_transport
        (congrArg List.length (groups_refines input source hC hr)).symm (mixed input selected)
        (source.mixedSpec selected (source.pivot_some hs)) (mixed_canonical input hC selected)
        (mixed_refines input source hC hr selected hs) (mixedAdmissible input hC hAd selected hn)
        source.groups_count (groupCount input hC hAd) K N outer scalar bits pos hp
      have hEmit := BinaryRoutePartialRefinement.emitMixed_option (BinaryTerminalRoutes.prepare input)
        (BinaryTerminalRoutes.sourcePartition input source hC hr) selected hCanon hRoutes
        (BinaryGroupPartialRun.mixedRun (mixed input selected) (mixed_canonical input hC selected)
          (mixedAdmissible input hC hAd selected hn) (groupCount input hC hAd) K N outer scalar bits pos hp).1
        (fun row hrow => BinaryGroupPartialRun.mixedRun_canonical (mixed input selected) (mixed_canonical input hC selected)
          (mixedAdmissible input hC hAd selected hn) (groupCount input hC hAd) K N outer scalar bits pos hp row hrow)
      apply Prod.ext
      · dsimp only
        change Option.map BinaryRoutePartialRefinement.sourceRow _=_
        rw [hEmit]
        have hm := congrArg (WordMappedIndexedRefinement.mapResult (fun y => (source.partition.emitMixed source.partition.routes selected y).allocation)) hRun
        simp only [WordMappedIndexedRefinement.mapResult,Option.map_map,Function.comp_def] at hm
        dsimp only [WordMappedIndexedRefinement.mapResult]
        simp only [PreparedGroupOutput.emitMixed_allocation]
        apply Eq.trans _ (congrArg Prod.fst hm)
        dsimp only
        rw [Option.map_map]
        apply congrArg (fun f => (BinaryGroupPartialRun.mixedRun (mixed input selected) (mixed_canonical input hC selected)
          (mixedAdmissible input hC hAd selected hn) (groupCount input hC hAd) K N outer scalar bits pos hp).1.map f)
        funext row j
        exact BinaryTerminalRoutes.transport_emitMixed _ source.partition selected (fun g => value (row.read g)) j
      · exact congrArg (fun result : Option (Fin (source.groups.length+1) → ℚ) × ℕ => result.2) hRun


theorem runIndexed_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (row : FixedArrayTable n SignedWord) (hs : (runIndexed input hC hAd K N outer scalar bits pos hp).1=some row) :
    ∀ j,CanonicalWord (row.read j):=by
  unfold runIndexed at hs
  dsimp only at hs
  split at hs
  · rename_i hn
    obtain ⟨sampled,hSampled,rfl⟩:=Option.map_eq_some_iff.mp hs
    exact BinaryGroupRoutes.emit_canonical _ _ (BinaryTerminalRoutes.prepare_canonical input hC)
      (BinaryGroupPartialRun.uniformRun_canonical (uniform input) (uniform_canonical input hC)
        (uniformAdmissible input hC hAd hn) (groupCount input hC hAd) K N scalar bits pos hp sampled hSampled)
  · rename_i selected hn
    obtain ⟨sampled,hSampled,rfl⟩:=Option.map_eq_some_iff.mp hs
    exact BinaryGroupRoutes.emitMixed_canonical _ _ _ (BinaryTerminalRoutes.prepare_canonical input hC)
      (BinaryGroupPartialRun.mixedRun_canonical (mixed input selected) (mixed_canonical input hC selected)
        (mixedAdmissible input hC hAd selected hn) (groupCount input hC hAd) K N outer scalar bits pos hp sampled hSampled)

theorem runIndexed_position {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    pos≤(runIndexed input hC hAd K N outer scalar bits pos hp).2 ∧
      (runIndexed input hC hAd K N outer scalar bits pos hp).2≤N:=by
  obtain ⟨source,hr⟩:=hAd
  have hBounds:=(source.program K outer scalar).machine.runCursorIndexed_position_bounds N bits
    (.state (source.program K outer scalar).start) pos hp
  rw [←runIndexed_refines input source hC hr (show Admissible input from ⟨source,hr⟩)] at hBounds
  exact hBounds

end Blotto.BinaryTerminalPartialRun

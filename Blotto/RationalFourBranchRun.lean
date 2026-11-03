import Blotto.WordMachineRunEmbedding
import Blotto.WordMachineLowerLeaf
import Blotto.RationalFourMachine

/-! The final four-variable deterministic guard embeds the selected original
machine exactly. Indexed runs and lower-leaf fallbacks agree, including the
gluing equality boundary and original small-branch shared cap. -/

namespace Blotto.WordStateMachine

theorem embedding_chooseLeaf {S T α : Type*} (first : WordStateMachine S α) (second : WordStateMachine T α)
    (embed : S → T) (he : ∀ s, second.step (embed s) = (first.step s).mapState embed) (state : S) :
    second.chooseLeaf (embed state) = first.chooseLeaf state := by
  conv_lhs => unfold chooseLeaf
  conv_rhs => unfold chooseLeaf
  rw [he]
  cases hs : first.step state with
  | done value => rfl
  | ask a b hb hab upper lower => exact embedding_chooseLeaf first second embed he lower
termination_by first.rank state
decreasing_by
  have hp := first.progress state
  rw [hs] at hp
  exact hp.2

end Blotto.WordStateMachine

namespace Blotto.RationalFourInput

theorem gluing_runIndexed (source : RationalFourInput) (hCase : (1-source.p)*source.ell ≤ source.w)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool)
    (cursor : WordCursor (CategoricalState (Fin 81))) (pos : ℕ) (hp : pos ≤ N) :
    (source.machine K outer scalar).runCursorIndexed N bits (cursor.mapState (FourSamplingState.gluing hCase)) pos hp =
      (source.gluingMachine hCase K scalar).runCursorIndexed N bits cursor pos hp := by
  rw [source.machine_refines]
  exact WordStateMachine.embedding_runCursorIndexed _ _ (FourSamplingState.gluing hCase) (fun _ => rfl) N bits cursor pos hp

theorem small_runIndexed (source : RationalFourInput) (hCase : source.w < (1-source.p)*source.ell)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool)
    (cursor : WordCursor (source.SmallState hCase)) (pos : ℕ) (hp : pos ≤ N) :
    (source.machine K outer scalar).runCursorIndexed N bits (cursor.mapState (FourSamplingState.small hCase)) pos hp =
      (source.smallMachine hCase K outer scalar).runCursorIndexed N bits cursor pos hp := by
  rw [source.machine_refines]
  exact WordStateMachine.embedding_runCursorIndexed _ _ (FourSamplingState.small hCase) (fun _ => rfl) N bits cursor pos hp

theorem gluing_fallback (source : RationalFourInput) (hCase : (1-source.p)*source.ell ≤ source.w)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    source.fallback K outer scalar = (source.gluingMachine hCase K scalar).chooseLeaf (source.gluingDescriptor hCase).start := by
  unfold fallback start
  rw [dite_eq_left hCase]
  rw [source.machine_refines]
  exact WordStateMachine.embedding_chooseLeaf _ _ (FourSamplingState.gluing hCase) (fun _ => rfl) _

theorem small_fallback (source : RationalFourInput) (hCase : source.w < (1-source.p)*source.ell)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    source.fallback K outer scalar = source.smallFallback hCase K outer scalar := by
  unfold fallback start smallFallback
  have hn : ¬(1-source.p)*source.ell ≤ source.w := not_le.mpr hCase
  rw [dite_eq_right hn]
  rw [source.machine_refines]
  exact WordStateMachine.embedding_chooseLeaf _ _ (FourSamplingState.small hCase) (fun _ => rfl) _

end Blotto.RationalFourInput

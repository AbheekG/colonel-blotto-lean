import Blotto.BinaryPRGWordControllerBooleanResourceThreeBridge
import Blotto.BinaryGeneralResourceFallback
import Blotto.BinaryResourceFallback

/-! Dimension-three native lower completion preserves exact stored resource
words and the active list under the concrete general/three conversion. This
covers lower successors of probability-one choices as well. -/
namespace Blotto.BinaryLowerThreeBridge
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerBooleanResourceThreeBridge
set_option maxHeartbeats 2000000

noncomputable def choice_toThree {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)} (choice : BinaryGeneralResourceChoice.Choice capacity hC) :
    BinaryResourceChoice.Choice capacity hC :=
  ⟨generalCertified_toThree choice.state,choice.first,choice.second,choice.tail,choice.head_pair,
    choice.registers,choice.registers_correct⟩

theorem select_toThree {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)} (choice : BinaryGeneralResourceChoice.Choice capacity hC) (branch : Bool) :
    (choice_toThree choice).select branch = generalCertified_toThree (choice.select branch) := rfl

noncomputable def preparation_toThree {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)} : BinaryGeneralResourceChoice.Preparation capacity hC →
    BinaryResourceChoice.Preparation capacity hC
  | .done state => .done (generalCertified_toThree state)
  | .ask choice => .ask (choice_toThree choice)

theorem prepare_toThree (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity) :
    preparation_toThree (BinaryGeneralResourceChoice.prepare capacity hC state) =
      BinaryResourceChoice.prepare capacity hC (generalCertified_toThree state) := by
  cases state with
  | mk data canonical nodup membership =>
      cases data with
      | mk resource active =>
          cases active with
          | nil => rfl
          | cons first rest => cases rest <;> rfl

theorem lower_toThree (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity) :
    generalCertified_toThree (BinaryGeneralResourceFallback.choose hC state) =
      BinaryResourceFallback.choose hC (generalCertified_toThree state) := by
  unfold BinaryGeneralResourceFallback.choose BinaryResourceFallback.choose
  conv_lhs => unfold BinaryGeneralResourceFallback.chooseWithPairs
  conv_rhs => unfold BinaryResourceFallback.chooseWithPairs
  rw [← prepare_toThree capacity hC state]
  dsimp only
  cases h : BinaryGeneralResourceChoice.prepare capacity hC state with
  | done result => rfl
  | ask choice =>
      dsimp only [preparation_toThree]
      rw [select_toThree]
      exact lower_toThree capacity hC (choice.select false)
termination_by state.state.active.length
decreasing_by
  have hProgress := choice.select_progress false
  rw [BinaryGeneralResourceFallback.prepare_owner hC state choice h] at hProgress
  exact hProgress

end Blotto.BinaryLowerThreeBridge

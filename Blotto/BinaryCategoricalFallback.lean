import Blotto.BinarySegmentCategorical
import Blotto.WordMachineFallback

/-! Source-free deterministic categorical fallback follows only the lower
successor of each actual stored-word preparation, including probability one.
Zero-mass lists retain the source's deterministic head rule. Rational source
witnesses occur only in refinement theorems, never native function arguments. -/

namespace Blotto.BinaryCategoricalFallback
open BinaryRationalNormalization BinaryRationalEncoding BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryStoredOverlapEnvironment

theorem prepare_weights {α : Type*} (fallback : α) (weights : WeightList α) (choice : Choice α)
    (h : prepare fallback weights=.ask choice) : choice.weights=weights:=by
  unfold prepare at h
  split at h
  · cases h
  · cases h
  · dsimp only at h
    split at h
    · cases Preparation.ask.inj h; rfl
    · cases h

def choose {α : Type*} (fallback : α) (weights : WeightList α) : α:=
  match _hp : prepare fallback weights with
  | .done value=>value
  | .ask choice=>choose fallback choice.rest
termination_by weights.items.length
decreasing_by
  have h:=rest_length choice
  rw [prepare_weights fallback weights choice _hp] at h
  omega

theorem choose_refines {α : Type*} (fallback : α) (weights : WeightList α) :
    choose fallback weights=(categoricalMachine fallback).chooseLeaf (.remaining weights.reference):=by
  conv_lhs=>unfold choose
  conv_rhs=>unfold WordStateMachine.chooseLeaf
  simp only [categoricalMachine]
  have hp:=prepare_refines fallback weights
  cases he : prepare fallback weights with
  | done result=>rw [he] at hp; dsimp only at hp; rw [hp]
  | ask choice=>
      rw [he] at hp
      dsimp only at hp
      rw [hp]
      exact choose_refines fallback choice.rest
termination_by weights.items.length
decreasing_by
  have h:=rest_length choice
  rw [prepare_weights fallback weights choice he] at h
  omega

def storedWeights {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hn : ∀ i,0≤value (table.weight.read i)) : WeightList (Fin k) where
  items:=List.ofFn (fun i=>(i,table.weight.read i))
  canonical:=by
    intro item hi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
    exact hC.1 i
  nonnegative:=by
    intro item hi
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
    exact hn i

def segment {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hn : ∀ i,0≤value (table.weight.read i)) (fallback : Fin k) : Fin k:=
  choose fallback (storedWeights table hC hn)

theorem storedWeights_eq {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hn : ∀ i,0≤value (table.weight.read i)) (hr : table.Refines source) :
    storedWeights table hC hn=BinarySegmentCategorical.weights table source hC hr:=by
  rfl

theorem segment_refines {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hn : ∀ i,0≤value (table.weight.read i)) (hr : table.Refines source) (fallback : Fin k) :
    segment table hC hn fallback=(categoricalMachine fallback).chooseLeaf source.start:=by
  rw [segment,choose_refines,storedWeights_eq table source hC hn hr,BinarySegmentCategorical.weights_reference]
  rfl

end Blotto.BinaryCategoricalFallback

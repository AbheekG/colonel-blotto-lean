import Blotto.GeneralPaperBorrowedListStorage

/-! Structural working storage of the actual balanced split traversal.
Frames retain original/split/copied list cells and scalar controls; the
right descent retains the completed left tree. Primitive arithmetic
scratch and the preceding field/padding construction remain separate. -/
namespace Blotto.GeneralPaperProfitTreeConstructionStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitTreeBuild
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def controlWord (H : ℕ) : ℕ := 4+binaryWordWidth (H+1)+binaryWordWidth (2^H)

theorem height_word (H h : ℕ) (hh : h≤H) : natBits h≤controlWord H := by
  have hw := binaryWordWidth_mono (show h≤H+1 by omega)
  unfold natBits controlWord
  omega

theorem span_word (H h : ℕ) (hh : h≤H) : natBits (2^h)≤controlWord H := by
  have hp := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hh
  have hw := binaryWordWidth_mono hp
  unfold natBits controlWord
  omega

def frame {K : ℕ} (W height : ℕ) (input : List (WeightedField Tag K)) : ℕ :=
  GeneralPaperBorrowedListStorage.splitWindow W input (2^height) (2^height)+
    natBits (height+1)+natBits (2^(height+1))+natBits (2^height)+128*W

def frameProfile (W H : ℕ) : ℕ := 6*(2^H)*W+256*W+3*controlWord H

theorem frame_bound {K : ℕ} (W H height : ℕ) (input : List (WeightedField Tag K))
    (hh : height+1≤H) (hn : input.length≤2^H) : frame W height input≤frameProfile W H := by
  have hl := GeneralPaperBorrowedListStorage.split_window W (2^H) (2^height) (2^height) input hn
  have hc := height_word H (height+1) hh
  have hs := span_word H (height+1) hh
  have hs' := span_word H height (by omega)
  unfold frame frameProfile
  omega

def peak {K : ℕ} (W : ℕ) : (height : ℕ) → List (WeightedField Tag K) → ℕ
  | 0,input => GeneralPaperBorrowedListStorage.footprint W input+
      GeneralPaperEncodedProfitTree.footprint W (build 0 input)+natBits 0+natBits 1+128*W
  | height+1,input =>
      let left := input.take (2^height)
      let right := input.drop (2^height)
      frame W height input+max (peak W height left)
        (GeneralPaperEncodedProfitTree.footprint W (build height left)+peak W height right)

theorem bounded {K : ℕ} (W H F height : ℕ) (input : List (WeightedField Tag K))
    (hh : height≤H) (hn : input.length≤2^H)
    (hz : GeneralPaperEncodedProfitField.footprint W (dummy Tag K).1≤F)
    (hi : ∀ f∈input,GeneralPaperEncodedProfitField.footprint W f.1≤F) :
    peak W height input≤2^height*(F+64*W)+(height+1)*frameProfile W H := by
  induction height generalizing input with
  | zero =>
    have hl := GeneralPaperBorrowedListStorage.bounded W (2^H) input hn
    have ht := GeneralPaperEncodedProfitTree.bounded W F (build 0 input)
      (GeneralPaperEncodedProfitTree.build_bound W F 0 input hz hi)
    have h0 := height_word H 0 (Nat.zero_le _)
    have h1 := span_word H 0 (Nat.zero_le _)
    change _≤2^0*(F+64*W)+1*frameProfile W H
    simp only [peak,frameProfile,pow_zero,one_mul] at *
    nlinarith only [hl,ht,h0,h1,Nat.zero_le (2^H*W)]
  | succ height ih =>
    have htake : (input.take (2^height)).length≤2^H := by
      calc
        _ ≤ input.length := by rw [List.length_take]; exact Nat.min_le_right _ _
        _≤2^H := hn
    have hdrop : (input.drop (2^height)).length≤2^H := by
      calc
        _ ≤ input.length := by rw [List.length_drop]; exact Nat.sub_le _ _
        _≤2^H := hn
    have hl := ih (input.take (2^height)) (by omega) htake
      (fun f hf => hi f (List.mem_of_mem_take hf))
    have hr := ih (input.drop (2^height)) (by omega) hdrop
      (fun f hf => hi f (List.mem_of_mem_drop hf))
    have ht := GeneralPaperEncodedProfitTree.bounded W F (build height (input.take (2^height)))
      (GeneralPaperEncodedProfitTree.build_bound W F height _ hz (fun f hf => hi f (List.mem_of_mem_take hf)))
    have hf := frame_bound W H height input hh hn
    have hmax : max (peak W height (input.take (2^height)))
        (GeneralPaperEncodedProfitTree.footprint W (build height (input.take (2^height)))+
          peak W height (input.drop (2^height)))≤2^(height+1)*(F+64*W)+(height+1)*frameProfile W H := by
      apply max_le
      · rw [pow_succ]
        nlinarith only [hl,Nat.zero_le (2^height*(F+64*W))]
      · rw [pow_succ]
        nlinarith only [ht,hr]
    change frame W height input+_≤_
    nlinarith only [hf,hmax]

end Blotto.GeneralPaperProfitTreeConstructionStorage

import Blotto.PlayerSpecificSignControlBudget

/-! Complete source price of the actual measured integer sign controls.
All powers, products, width calculations and stored-word copies are priced. -/
namespace Blotto.PlayerSpecificSignControlCost
open PlayerSpecificSignControlExecution PlayerSpecificSignControlBudget
set_option autoImplicit false
set_option maxHeartbeats 4000000

def width (E A B : ℕ) : ℕ := 8*word E A B+64

theorem atom_binary (model : RationalCostModel) (E A B na nb : ℕ) (hna : na≤3) (hnb : nb≤17)
    (op : ℕ → ℕ → ℕ) (x y : ℕ) (hx : x∈atoms E A B na nb) (hy : y∈atoms E A B na nb)
    (hz : op x y∈atoms E A B na nb) :
    (PlayerSpecificNaturalExecution.binary model op x y).2≤64*model.rat (width E A B) := by
  have hf:=fits E A B na nb hna hnb
  have hw : word E A B≤width E A B := by unfold width; omega
  exact PlayerSpecificNaturalExecution.binary_cost model op x y _
    ((hf x hx).trans hw) ((hf y hy).trans hw) ((hf _ hz).trans hw)

theorem dyadic (model : RationalCostModel) (E A B exponent : ℕ) (he : exponent≤size E A B) :
    (PlayerSpecificNaturalExecution.power model 2 exponent).2≤256*(size E A B+1)*model.rat (width E A B) := by
  have hc:=PlayerSpecificNaturalExecution.power_cost model 2 exponent
  have hw: PlayerSpecificNaturalExecution.powerWidth 2 exponent≤width E A B :=
    (dyadic_power_width E A B exponent he).trans (by unfold width; omega)
  exact hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (by omega)) (model.monotone hw))

theorem interval (model : RationalCostModel) (E A B exponent : ℕ) (he : exponent≤17) :
    (PlayerSpecificNaturalExecution.power model (1+2^E) exponent).2≤4608*model.rat (width E A B) := by
  have hc:=PlayerSpecificNaturalExecution.power_cost model (1+2^E) exponent
  have hw: PlayerSpecificNaturalExecution.powerWidth (1+2^E) exponent≤width E A B :=
    (interval_power_width E A B exponent he).trans (by unfold width; omega)
  exact hc.trans (Nat.mul_le_mul (by omega : 256*(exponent+1)≤4608) (model.monotone hw))

theorem sum_words (xs : List ℕ) (W : ℕ) (h : ∀ n∈xs,1+binaryWordWidth n≤W) :
    (xs.map (fun n => 1+binaryWordWidth n)).sum≤xs.length*W := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons n ns ih =>
    have hn:=h n List.mem_cons_self
    have ht:=ih (fun q hq => h q (List.mem_cons_of_mem n hq))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hn,ht]

theorem copies (model : RationalCostModel) (E A B na nb : ℕ) (hna : na≤3) (hnb : nb≤17) :
    copy (run model E A B na nb).1+
      64*((inputs E A B na nb).map (fun n => 1+binaryWordWidth n)).sum≤832*model.rat (width E A B) := by
  have hf:=fits E A B na nb hna hnb
  have hv:=values model E A B na nb
  have hout : ∀ n∈words (run model E A B na nb).1,1+binaryWordWidth n≤word E A B := by
    intro n hn
    apply hf n
    simp only [words,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,hv.2.2.2.2.2.1,
      hv.2.2.2.2.2.2.1,hv.2.2.2.2.2.2.2,List.mem_cons,List.not_mem_nil,or_false] at hn
    simp only [atoms,List.mem_cons,List.not_mem_nil,or_false]
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
  have hin : ∀ n∈inputs E A B na nb,1+binaryWordWidth n≤word E A B := by
    intro n hn
    apply hf n
    simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hn
    simp only [atoms,List.mem_cons,List.not_mem_nil,or_false]
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> tauto
  have ho:=sum_words _ _ hout
  have hi:=sum_words _ _ hin
  have hw : word E A B≤model.rat (width E A B) :=
    (by unfold width; omega : word E A B≤width E A B).trans (model.word_le _)
  rw [show (words (run model E A B na nb).1).length=8 from rfl] at ho
  rw [show (inputs E A B na nb).length=5 from rfl] at hi
  unfold copy
  nlinarith only [ho,hi,hw]

theorem run_cost (model : RationalCostModel) (E A B na nb : ℕ) (hna : na≤3) (hnb : nb≤17) :
    (run model E A B na nb).2≤1500000*size E A B*model.rat (width E A B) := by
  have hsize:=size_large E A B
  have hE : E≤size E A B := by unfold size; omega
  have hA : A≤size E A B := by unfold size; omega
  have hB : B≤size E A B := by unfold size; omega
  have hM:=dyadic model E A B E hE
  have hpa:=dyadic model E A B A hA
  have hpb:=dyadic model E A B B hB
  have hia:=interval model E A B na (by omega)
  have hib:=interval model E A B nb hnb
  have h1:=atom_binary model E A B na nb hna hnb (fun x y => x+y) 1 (2^E) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h2:=atom_binary model E A B na nb hna hnb (fun x y => x*y) na (2^A) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h3:=atom_binary model E A B na nb hna hnb (fun x y => x*y) (na*2^A) ((1+2^E)^na) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h4:=atom_binary model E A B na nb hna hnb (fun x y => x+y) 1 (na*2^A*(1+2^E)^na) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h5:=atom_binary model E A B na nb hna hnb (fun x y => x*y) (2^B) ((1+2^E)^nb) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h6:=atom_binary model E A B na nb hna hnb (fun x y => x*y) 8 (2^E) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h7:=atom_binary model E A B na nb hna hnb (fun x y => x*y) (8*2^E) (1+na*2^A*(1+2^E)^na) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  have h8:=atom_binary model E A B na nb hna hnb (fun x y => x*y) (8*2^E*(1+na*2^A*(1+2^E)^na)) (2^B*(1+2^E)^nb) (by simp [atoms]) (by simp [atoms]) (by simp [atoms])
  let operand:=8*2^E*(1+na*2^A*(1+2^E)^na)*(2^B*(1+2^E)^nb)
  have hf:=fits E A B na nb hna hnb operand (by simp [operand,atoms])
  have hwidth : PlayerSpecificWidthExecution.width operand≤width E A B := by
    unfold PlayerSpecificWidthExecution.width width
    omega
  have hdc:=PlayerSpecificWidthExecution.price model operand
  have hwork : 128*(binaryWordWidth operand+1)≤128*word E A B := by omega
  have hdp:=hdc.trans (Nat.mul_le_mul hwork (model.monotone hwidth))
  have hcopy:=copies model E A B na nb hna hnb
  rw [run]
  dsimp only
  simp only [PlayerSpecificNaturalExecution.power_value,PlayerSpecificNaturalExecution.binary_value]
  dsimp only [run] at hcopy
  simp only [PlayerSpecificNaturalExecution.power_value,PlayerSpecificNaturalExecution.binary_value] at hcopy
  unfold word at hdp
  change (PlayerSpecificWidthExecution.run model operand).2≤128*(1024*size E A B)*model.rat (width E A B) at hdp
  nlinarith only [hM,hpa,hpb,hia,hib,h1,h2,h3,h4,h5,h6,h7,h8,hdp,hcopy,hsize]

end Blotto.PlayerSpecificSignControlCost

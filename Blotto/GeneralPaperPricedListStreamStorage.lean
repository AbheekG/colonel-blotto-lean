import Blotto.GeneralPaperSourceCrossingOperandStorageRates

/-! Native rational filterMap/flatMap storage. Current optional roots or
segments stay owned through recursive descent; append copies only its
current segment. Callback scratch is one active reservation. Native work
counters contribute encoded lengths, never whole callback runtime. -/
namespace Blotto.GeneralPaperPricedListStreamStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPricedListStream
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def listProfile (W R N : ℕ) : ℕ := N*(1+2*R+2*W)+32*W
def filterWork (W C N : ℕ) : ℕ := (C+8*W)*N+2*W
def filterCap (W C N : ℕ) : ℕ := N+1+3*filterWork W C N+C+8*W
def filterFrameProfile (W R C N : ℕ) : ℕ :=
  GeneralPaperAffineArithmeticStorage.rootProfile W R+8*(natBits (filterCap W C N)+W)+160*W

def filterFrame {α : Type*} (W : ℕ) (evaluate : α → Option ℚ×ℕ) : List α → ℕ
  | [] => GeneralPaperAffineArithmeticStorage.rootFoot W none+fields W [0,2*W]+128*W
  | a::rest =>
    let current := evaluate a
    let child := filterMap W evaluate rest
    let result := filterMap W evaluate (a::rest)
    GeneralPaperAffineArithmeticStorage.rootFoot W current.1+
      fields W [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W]+128*W

theorem filter_frame {α : Type*} (W R C N : ℕ) (evaluate : α → Option ℚ×ℕ) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → RationalHeight t R) :
    filterFrame W evaluate xs≤filterFrameProfile W R C N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (filterCap W C N)) [0,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> unfold filterCap filterWork <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (filterCap W C N)+W)+32*W at hf
    change 1+GeneralPaperEncodedScalarStorage.fields W [0,2*W]+128*W≤_
    unfold filterFrameProfile GeneralPaperAffineArithmeticStorage.rootProfile
    omega
  | cons a rest =>
    let current := evaluate a
    let child := filterMap W evaluate rest
    let result := filterMap W evaluate (a::rest)
    have hCurrent : current.2≤C := hC a List.mem_cons_self
    have hChild := (filterMap_work W C evaluate rest (fun b hb => hC b (List.mem_cons_of_mem _ hb))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (show rest.length≤N by simp only [List.length_cons] at hn; omega)) _)
    have hResult := (filterMap_work W C evaluate (a::rest) hC).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)
    change child.2≤filterWork W C N at hChild
    change result.2≤filterWork W C N at hResult
    have hChildLen := (filterMap_length W evaluate rest).trans (show rest.length≤N by simp only [List.length_cons] at hn; omega)
    have hResultLen := (filterMap_length W evaluate (a::rest)).trans hn
    change child.1.length≤N at hChildLen
    change result.1.length≤N at hResultLen
    have hRoot := GeneralPaperAffineArithmeticStorage.root_bound W R current.1 (hR a List.mem_cons_self)
    have hf := fields_bound W (natBits (filterCap W C N))
      [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W] (by
        intro b hb
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold filterCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (filterCap W C N)+W)+32*W at hf
    change GeneralPaperAffineArithmeticStorage.rootFoot W current.1+GeneralPaperEncodedScalarStorage.fields W
      [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W]+128*W≤_
    unfold filterFrameProfile
    omega

def filterFrames {α : Type*} (W : ℕ) (evaluate : α → Option ℚ×ℕ) : List α → ℕ
  | [] => filterFrame W evaluate []
  | a::rest => filterFrame W evaluate (a::rest)+filterFrames W evaluate rest

theorem filter_frames {α : Type*} (W R C N : ℕ) (evaluate : α → Option ℚ×ℕ) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → RationalHeight t R) :
    filterFrames W evaluate xs≤(xs.length+1)*filterFrameProfile W R C N := by
  induction xs with
  | nil => simpa only [filterFrames,List.length_nil,Nat.zero_add,Nat.one_mul] using filter_frame W R C N evaluate [] hn hC hR
  | cons a rest ih =>
    have hc := ih (by simp only [List.length_cons] at hn; omega) (fun b hb => hC b (List.mem_cons_of_mem _ hb))
      (fun b hb => hR b (List.mem_cons_of_mem _ hb))
    exact (Nat.add_le_add (filter_frame W R C N evaluate (a::rest) hn hC hR) hc).trans_eq
      (by simp only [List.length_cons]; ring)

def activeSpace {α : Type*} (space : α → ℕ) : Option α → ℕ
  | none => 0
  | some a => space a

theorem active_bound {α : Type*} (Q : ℕ) (space : α → ℕ) (active : Option α) (xs : List α)
    (hQ : ∀ a∈xs,space a≤Q) (ha : ∀ a,active=some a → a∈xs) : activeSpace space active≤Q := by
  cases active with
  | none => change 0≤_; omega
  | some a => exact hQ a (ha a rfl)

def filterWindow {α : Type*} (W : ℕ) (evaluate : α → Option ℚ×ℕ) (space : α → ℕ) (active : Option α) (xs : List α) : ℕ :=
  filterFrames W evaluate xs+listFootprint W rationalWordWidth (filterMap W evaluate xs).1+activeSpace space active
def filterProfile (W R C N Q : ℕ) : ℕ := (N+1)*filterFrameProfile W R C N+listProfile W R N+Q

theorem filter_bounded {α : Type*} (W R C N Q : ℕ) (evaluate : α → Option ℚ×ℕ) (space : α → ℕ) (active : Option α) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → RationalHeight t R) (hQ : ∀ a∈xs,space a≤Q)
    (ha : ∀ a,active=some a → a∈xs) : filterWindow W evaluate space active xs≤filterProfile W R C N Q := by
  have hFrames := (filter_frames W R C N evaluate xs hn hC hR).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hLen := (filterMap_length W evaluate xs).trans hn
  have hWord : ∀ t∈(filterMap W evaluate xs).1,rationalWordWidth t≤1+2*R := by
    intro t ht
    rw [filterMap_data] at ht
    obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp ht
    exact rationalWordWidth_of_height (hR a ha t he)
  have hOut := (list_bound W (1+2*R) rationalWordWidth _ hWord).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  change listFootprint W rationalWordWidth (filterMap W evaluate xs).1≤listProfile W R N at hOut
  have hActive := active_bound Q space active xs hQ ha
  exact Nat.add_le_add (Nat.add_le_add hFrames hOut) hActive

def flatWork (W B C N : ℕ) : ℕ := (C+(8*B+8)*W)*N+2*W
def flatCap (W B C N : ℕ) : ℕ := N+N*B+B+1+3*flatWork W B C N+C+(8*B+8)*W
def flatFrameProfile (W R B C N : ℕ) : ℕ :=
  listProfile W R B+(2*B*W+32*W)+10*(natBits (flatCap W B C N)+W)+160*W

def flatFrame {α : Type*} (W copied : ℕ) (evaluate : α → List ℚ×ℕ) : List α → ℕ
  | [] => fields W [0,2*W]+128*W
  | a::rest =>
    let current := evaluate a
    let child := flatMap W evaluate rest
    let result := flatMap W evaluate (a::rest)
    let append := (8*current.1.length+8)*W
    listFootprint W rationalWordWidth current.1+GeneralPaperBorrowedListStorage.footprint W (current.1.take copied)+
      fields W [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append]+128*W

theorem flat_frame {α : Type*} (W R B C N copied : ℕ) (evaluate : α → List ℚ×ℕ) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,RationalHeight t R) : flatFrame W copied evaluate xs≤flatFrameProfile W R B C N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (flatCap W B C N)) [0,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> unfold flatCap flatWork <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (flatCap W B C N)+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W [0,2*W]+128*W≤_
    unfold flatFrameProfile
    omega
  | cons a rest =>
    let current := evaluate a
    let child := flatMap W evaluate rest
    let result := flatMap W evaluate (a::rest)
    let append := (8*current.1.length+8)*W
    have hCurrent : current.2≤C := hC a List.mem_cons_self
    have hCurrentLen : current.1.length≤B := hB a List.mem_cons_self
    have hChild := (flatMap_work W B C evaluate rest (fun b hb => hB b (List.mem_cons_of_mem _ hb))
      (fun b hb => hC b (List.mem_cons_of_mem _ hb))).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (show rest.length≤N by simp only [List.length_cons] at hn; omega)) _)
    have hResult := (flatMap_work W B C evaluate (a::rest) hB hC).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)
    change child.2≤flatWork W B C N at hChild
    change result.2≤flatWork W B C N at hResult
    have hChildLen := (flatMap_length W B evaluate rest (fun b hb => hB b (List.mem_cons_of_mem _ hb))).trans
      (Nat.mul_le_mul_right B (show rest.length≤N by simp only [List.length_cons] at hn; omega))
    have hResultLen := (flatMap_length W B evaluate (a::rest) hB).trans (Nat.mul_le_mul_right B hn)
    change child.1.length≤N*B at hChildLen
    change result.1.length≤N*B at hResultLen
    have hAppend : append≤(8*B+8)*W := Nat.mul_le_mul_right W (by omega)
    have hShape : result.2=current.2+child.2+append := rfl
    have hPayload := (list_bound W (1+2*R) rationalWordWidth current.1
      (fun t ht => rationalWordWidth_of_height (hR a List.mem_cons_self t ht))).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCurrentLen) _)
    change listFootprint W rationalWordWidth current.1≤listProfile W R B at hPayload
    have hCopy := GeneralPaperBorrowedListStorage.bounded W B (current.1.take copied)
      (by simp only [List.length_take]; omega)
    have hf := fields_bound W (natBits (flatCap W B C N))
      [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append] (by
        intro b hb
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold flatCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (flatCap W B C N)+W)+32*W at hf
    change listFootprint W rationalWordWidth current.1+GeneralPaperBorrowedListStorage.footprint W (current.1.take copied)+
      GeneralPaperEncodedScalarStorage.fields W [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append]+128*W≤_
    unfold flatFrameProfile
    omega

def flatFrames {α : Type*} (W copied : ℕ) (evaluate : α → List ℚ×ℕ) : List α → ℕ
  | [] => flatFrame W copied evaluate []
  | a::rest => flatFrame W copied evaluate (a::rest)+flatFrames W copied evaluate rest

theorem flat_frames {α : Type*} (W R B C N copied : ℕ) (evaluate : α → List ℚ×ℕ) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,RationalHeight t R) : flatFrames W copied evaluate xs≤(xs.length+1)*flatFrameProfile W R B C N := by
  induction xs with
  | nil => simpa only [flatFrames,List.length_nil,Nat.zero_add,Nat.one_mul] using flat_frame W R B C N copied evaluate [] hn hB hC hR
  | cons a rest ih =>
    have hc := ih (by simp only [List.length_cons] at hn; omega) (fun b hb => hB b (List.mem_cons_of_mem _ hb))
      (fun b hb => hC b (List.mem_cons_of_mem _ hb)) (fun b hb => hR b (List.mem_cons_of_mem _ hb))
    exact (Nat.add_le_add (flat_frame W R B C N copied evaluate (a::rest) hn hB hC hR) hc).trans_eq
      (by simp only [List.length_cons]; ring)

def flatWindow {α : Type*} (W copied : ℕ) (evaluate : α → List ℚ×ℕ) (space : α → ℕ) (active : Option α) (xs : List α) : ℕ :=
  flatFrames W copied evaluate xs+listFootprint W rationalWordWidth (flatMap W evaluate xs).1+activeSpace space active
def flatProfile (W R B C N Q : ℕ) : ℕ := (N+1)*flatFrameProfile W R B C N+listProfile W R (N*B)+Q

theorem flat_bounded {α : Type*} (W R B C N Q copied : ℕ) (evaluate : α → List ℚ×ℕ) (space : α → ℕ) (active : Option α) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,RationalHeight t R) (hQ : ∀ a∈xs,space a≤Q)
    (ha : ∀ a,active=some a → a∈xs) : flatWindow W copied evaluate space active xs≤flatProfile W R B C N Q := by
  have hFrames := (flat_frames W R B C N copied evaluate xs hn hB hC hR).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hLen := (flatMap_length W B evaluate xs hB).trans (Nat.mul_le_mul_right B hn)
  have hWord : ∀ t∈(flatMap W evaluate xs).1,rationalWordWidth t≤1+2*R := by
    intro t ht
    rw [flatMap_data] at ht
    obtain ⟨a,ha,he⟩ := List.mem_flatMap.mp ht
    exact rationalWordWidth_of_height (hR a ha t he)
  have hOut := (list_bound W (1+2*R) rationalWordWidth _ hWord).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  change listFootprint W rationalWordWidth (flatMap W evaluate xs).1≤listProfile W R (N*B) at hOut
  have hActive := active_bound Q space active xs hQ ha
  exact Nat.add_le_add (Nat.add_le_add hFrames hOut) hActive

end Blotto.GeneralPaperPricedListStreamStorage

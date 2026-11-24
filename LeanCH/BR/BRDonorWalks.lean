import LeanCH.BR.BRPairedReturnPaths
import LeanCH.BR.BROutModule

/-! Finite walk helpers for the original four-label donor configuration.
The graph, all paths, and all banks remain on the same original labels. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def OriginalDonor (D : CH.Digraph) (V : Finset ℕ) (z h t u : ℕ) : Prop :=
  z∈V ∧ h∈V ∧ t∈V ∧ u∈V ∧
  z≠h ∧ z≠t ∧ z≠u ∧ h≠t ∧ h≠u ∧ t≠u ∧
  D z h=true ∧ D z u=true ∧ D h t=true ∧
  ¬D z t=true ∧ ¬D u h=true ∧ ¬D u t=true ∧ ¬D t u=true

def DonorAbsent (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ z h t u, ¬OriginalDonor D V z h t u

def StrongBank (D : CH.Digraph) (S : Finset ℕ) : Prop :=
  ∀ x∈S,∀ y∈S,∃ n,Walk D S x y n

def ClosedBank (D : CH.Digraph) (V S : Finset ℕ) : Prop :=
  ∀ x∈S,∀ y∈V,D x y=true → y∈S

theorem donor_of_pattern {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 2) {z h t u : ℕ} (hz : z∈V) (hh : h∈V) (ht : t∈V) (hu : u∈V)
    (ezh : D z h=true) (ezu : D z u=true) (eht : D h t=true)
    (nzt : ¬D z t=true) (nuh : ¬D u h=true) (nut : ¬D u t=true) (ntu : ¬D t u=true) :
    OriginalDonor D V z h t u := by
  refine ⟨hz,hh,ht,hu,?_,?_,?_,?_,?_,?_,ezh,ezu,eht,nzt,nuh,nut,ntu⟩
  · rintro rfl; exact loopfree hf (by decide) hz ezh
  · rintro rfl; exact digonfree hf le_rfl hz hh ezh eht
  · rintro rfl; exact loopfree hf (by decide) hz ezu
  · rintro rfl; exact loopfree hf (by decide) hh eht
  · rintro rfl; exact nut eht
  · rintro rfl; exact nzt ezu

theorem donor_no_triangle {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 3)
    {a b c : ℕ} (ha : a∈V) (hb : b∈V) (hc : c∈V)
    (hab : D a b=true) (hbc : D b c=true) (hca : D c a=true) : False :=
  hf a 3 (by decide) le_rfl (.step hb hab (.step hc hbc (.step ha hca (.refl a))))

theorem walk_closed_bank {D : CH.Digraph} {V S : Finset ℕ}
    (hclosed : ClosedBank D V S) {a b n : ℕ} (ha : a∈S) (w : Walk D V a b n) :
    b∈S ∧ Walk D S a b n := by
  induction w with
  | refl a => exact ⟨ha,.refl a⟩
  | @step a b c n hb hab w ih =>
    have hbS := hclosed a ha b hb hab
    exact ⟨(ih hbS).1,.step hbS hab (ih hbS).2⟩

/-- A finite nonempty induced host has an actual nonempty closed strong bank. -/
theorem exists_closed_strong_bank (D : CH.Digraph) {V : Finset ℕ} (hV : V.Nonempty) :
    ∃ S,S.Nonempty ∧ S⊆V ∧ ClosedBank D V S ∧ StrongBank D S := by
  classical
  let reach := fun v => V.filter (fun x => ∃ n,Walk D V v x n)
  have self : ∀ v∈V,v∈reach v := fun v hv=>mem_filter.mpr ⟨hv,0,.refl v⟩
  have sub : ∀ v,reach v⊆V := fun _=>filter_subset _ _
  have closed : ∀ v,ClosedBank D V (reach v) := by
    intro v x hx y hy hxy
    obtain ⟨n,w⟩ := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨hy,n+1,w.snoc hy hxy⟩
  obtain ⟨v,hv,hmin⟩ := V.exists_min_image (fun v=>(reach v).card) hV
  refine ⟨reach v,⟨v,self v hv⟩,sub v,closed v,?_⟩
  intro x hx y hy
  have hsub : reach x⊆reach v := by
    intro z hz
    obtain ⟨n,w⟩ := (mem_filter.mp hz).2
    exact (walk_closed_bank (closed v) hx w).1
  have heq : reach x=reach v := eq_of_subset_of_card_le hsub (hmin x (sub v hx))
  obtain ⟨n,w⟩ := (mem_filter.mp (heq.symm ▸ hy)).2
  exact ⟨n,(walk_closed_bank (closed v) hx w).2⟩

/-- A shortest actual bank-to-bank walk. No girth or degree hypothesis is used. -/
theorem shortest_bank_walk {D : CH.Digraph} {S A B : Finset ℕ}
    (hAS : A⊆S)
    (hex : ∃ n,∃ a∈A,∃ b∈B,Walk D S a b n) :
    ∃ n,∃ f : ℕ→ℕ,f 0∈A ∧ f n∈B ∧
      (∀ i,i≤n→f i∈S) ∧ (∀ i,i<n→D (f i) (f (i+1))=true) ∧
      (∀ i, 0 < i → i ≤ n → f i ∉ A) ∧ (∀ i, i < n → f i ∉ B) ∧
      (∀ i j, i + 1 < j → j ≤ n → ¬D (f i) (f j)=true) := by
  classical
  let n := Nat.find hex
  obtain ⟨a,ha,b,hb,w⟩ := Nat.find_spec hex
  obtain ⟨f,h0,hn,he⟩ := w.toFun
  have hm : ∀ i,i≤n→f i∈S := by
    intro i hi
    by_cases hi0 : i=0
    · simpa [hi0,h0] using hAS ha
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i-1) (by omega)).1
  have hmin : ∀ k,∀ a∈A,∀ b∈B,Walk D S a b k → n≤k := by
    intro k a ha b hb w
    exact Nat.find_min' hex ⟨a,ha,b,hb,w⟩
  refine ⟨n,f,h0.symm ▸ ha,hn.symm ▸ hb,hm,fun i hi=>(he i hi).2,?_,?_,?_⟩
  · intro i hi hin hia
    have h := hmin (n-i) (f i) hia (f n) (hn.symm ▸ hb) (walk_between he hin le_rfl)
    omega
  · intro i hi hib
    have h := hmin (i-0) (f 0) (h0.symm ▸ ha) (f i) hib (walk_between he (Nat.zero_le i) hi.le)
    omega
  · intro i j hij hj e
    have wp := walk_between he (Nat.zero_le i) (by omega : i≤n)
    have ws := walk_between he hj le_rfl
    have ww := (wp.snoc (hm j hj) e).append ws
    have h := hmin ((i-0)+1+(n-j)) (f 0) (h0.symm ▸ ha) (f n) (hn.symm ▸ hb) ww
    omega

end LeanCH.BR.WeightedSD

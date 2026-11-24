import LeanCH.BR.BRWeightedPathExposure

/-! Actual paired returns. Corpus provenance: PrivateReturnHulls/Pack and
ch-markov-paper manuscript section 11; adapted to the current finite Walk API.
No saturation, weights, degree floor or induction is used here. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem paired_return_length {q l v t u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hv : v∈V) (ht : t∈V)
    (hvt : D v t=true) (huv : D u v=true)
    (hl : l≤q-1) (w : Walk D V t u l) : l=q-1 := by
  by_contra hn
  exact hf v (l+1+1) (by omega) (by omega) (.step ht hvt (w.snoc hv huv))

theorem paired_return_sequences {q v : ℕ} {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V q) (hv : v∈V) (hSV : S⊆V) (u : ℕ→ℕ)
    (hvt : ∀t∈S,D v t=true) (huv : ∀t∈S,D (u t) v=true)
    (hret : ∀t∈S,∃l,l≤q-1 ∧ Walk D V t (u t) l) :
    ∃f : ℕ→ℕ→ℕ,∀t∈S,f t 0=t ∧ f t (q-1)=u t ∧
      ∀i,i<q-1→f t (i+1)∈V ∧ D (f t i) (f t (i+1))=true := by
  classical
  have hex : ∀t,∃f : ℕ→ℕ,t∈S→f 0=t ∧ f (q-1)=u t ∧
      ∀i,i<q-1→f (i+1)∈V ∧ D (f i) (f (i+1))=true := by
    intro t
    by_cases ht : t∈S
    · obtain ⟨l,hl,w⟩ := hret t ht
      have he := paired_return_length hf hv (hSV ht) (hvt t ht) (huv t ht) hl w
      subst l
      obtain ⟨f,h0,hl,hedges⟩ := w.toFun
      exact ⟨f,fun _=>⟨h0,hl,hedges⟩⟩
    · exact ⟨fun _=>t,fun h=>False.elim (ht h)⟩
  choose f hf using hex
  exact ⟨f,hf⟩

theorem return_trace_mem {l : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (f : ℕ→ℕ) (h0 : f 0∈V)
    (he : ∀i,i<l→f (i+1)∈V ∧ D (f i) (f (i+1))=true) : walkTrace f l⊆V := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  have hi' := mem_range.mp hi
  by_cases hi0 : i=0
  · subst i; exact h0
  · have hi1 : 1 ≤ i := by omega
    simpa only [Nat.sub_add_cancel hi1] using (he (i-1) (by omega)).1

theorem crossed_return_traces_disjoint {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (f g : ℕ→ℕ) (hf0 : f 0∈V) (hg0 : g 0∈V)
    (he : ∀i,i<q-1→f (i+1)∈V ∧ D (f i) (f (i+1))=true)
    (hg : ∀i,i<q-1→g (i+1)∈V ∧ D (g i) (g (i+1))=true)
    (hcross : D (g (q-1)) (f 0)=true) (hcross' : D (f (q-1)) (g 0)=true) :
    Disjoint (walkTrace f (q-1)) (walkTrace g (q-1)) := by
  apply disjoint_left.mpr
  intro z hz hz'
  obtain ⟨i,hi,hiz⟩ := mem_image.mp hz
  obtain ⟨j,hj,hjz⟩ := mem_image.mp hz'
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have hij : f i=g j := hiz.trans hjz.symm
  by_cases hle : i≤j
  · have a := walk_between he (Nat.zero_le i) (by omega : i≤q-1)
    have b := walk_between hg (by omega : j≤q-1) (le_refl (q-1))
    rw [hij] at a
    exact hf (f 0) ((i-0)+(q-1-j)+1) (by omega) (by omega) ((a.append b).snoc hf0 hcross)
  · have a := walk_between hg (Nat.zero_le j) (by omega : j≤q-1)
    have b := walk_between he (by omega : i≤q-1) (le_refl (q-1))
    rw [←hij] at a
    exact hf (g 0) ((j-0)+(q-1-i)+1) (by omega) (by omega) ((a.append b).snoc hg0 hcross')

theorem return_trace_avoids_parent {q : ℕ} (hq : 1≤q) {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (f : ℕ→ℕ) (h0 : f 0∈V)
    (he : ∀i,i<q-1→f (i+1)∈V ∧ D (f i) (f (i+1))=true)
    {x : ℕ} (hxt : D x (f 0)=true) : x∉walkTrace f (q-1) := by
  intro hx
  obtain ⟨i,hi,hix⟩ := mem_image.mp hx
  have hi' := mem_range.mp hi
  have w := walk_between he (Nat.zero_le i) (by omega : i≤q-1)
  rw [hix] at w
  exact hf (f 0) ((i-0)+1) (by omega) (by omega) (w.snoc h0 hxt)

theorem return_trace_avoids_extra_parent {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (f : ℕ→ℕ) (h0 : f 0∈V)
    (he : ∀i,i<q-1→f (i+1)∈V ∧ D (f i) (f (i+1))=true)
    {v x : ℕ} (hv : v∈V) (hvt : D v (f 0)=true)
    (hxv : D x v=true) (hxu : x≠f (q-1)) : x∉walkTrace f (q-1) := by
  intro hx
  obtain ⟨i,hi,hix⟩ := mem_image.mp hx
  have hi' := mem_range.mp hi
  have hil : i≠q-1 := by intro h; subst i; exact hxu hix.symm
  have w := walk_between he (Nat.zero_le i) (by omega : i≤q-1)
  rw [hix] at w
  exact hf v ((i-0)+1+1) (by omega) (by omega) (.step h0 hvt (w.snoc hv hxv))

theorem rooted_return_traces_disjoint {q v : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hv : v∈V)
    (f g : ℕ→ℕ) (hf0 : f 0∈V) (hg0 : g 0∈V)
    (he : ∀i,i<q-1→f (i+1)∈V ∧ D (f i) (f (i+1))=true)
    (hg : ∀i,i<q-1→g (i+1)∈V ∧ D (g i) (g (i+1))=true)
    (hvf : D v (f 0)=true) (hgv : D (g (q-1)) v=true)
    (hcross : D (f (q-1)) (g 0)=true) :
    Disjoint (walkTrace f (q-1)) (walkTrace g (q-1)) := by
  apply disjoint_left.mpr
  intro z hz hz'
  obtain ⟨i,hi,hiz⟩ := mem_image.mp hz
  obtain ⟨j,hj,hjz⟩ := mem_image.mp hz'
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have hij : f i=g j := hiz.trans hjz.symm
  have fp := walk_between he (Nat.zero_le i) (by omega : i≤q-1)
  have gp := walk_between hg (Nat.zero_le j) (by omega : j≤q-1)
  have fs := walk_between he (by omega : i≤q-1) (le_refl (q-1))
  have gs := walk_between hg (by omega : j≤q-1) (le_refl (q-1))
  by_cases hlt : i<j
  · rw [hij] at fp
    exact hf v ((i-0)+(q-1-j)+1+1) (by omega) (by omega)
      (.step hf0 hvf ((fp.append gs).snoc hv hgv))
  · rw [←hij] at gp
    exact hf (g 0) ((j-0)+(q-1-i)+1) (by omega) (by omega)
      ((gp.append fs).snoc hg0 hcross)

theorem rooted_return_head_position {q v t i : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hv : v∈V) (ht : t∈V) (hvt : D v t=true)
    (f : ℕ→ℕ) (he : ∀j,j<q-1→f (j+1)∈V ∧ D (f j) (f (j+1))=true)
    (hfv : D (f (q-1)) v=true) (hi : i≤q-1) (hedge : D t (f i)=true) : i≤1 := by
  by_contra hn
  have hmem : f i∈V := by
    have hi1 : 1 ≤ i := by omega
    simpa only [Nat.sub_add_cancel hi1] using (he (i-1) (by omega)).1
  have w := walk_between he hi (le_refl (q-1))
  exact hf v ((q-1-i)+1+1+1) (by omega) (by omega)
    (.step ht hvt (.step hmem hedge (w.snoc hv hfv)))

theorem crossed_return_head_zero {q t i : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (ht : t∈V)
    (f : ℕ→ℕ) (he : ∀j,j<q-1→f (j+1)∈V ∧ D (f j) (f (j+1))=true)
    (hft : D (f (q-1)) t=true) (hi : i≤q-1) (hedge : D t (f i)=true) : i=0 := by
  by_contra hn
  have hmem : f i∈V := by
    have hi1 : 1 ≤ i := by omega
    simpa only [Nat.sub_add_cancel hi1] using (he (i-1) (by omega)).1
  have w := walk_between he hi (le_refl (q-1))
  exact hf t ((q-1-i)+1+1) (by omega) (by omega)
    (.step hmem hedge (w.snoc ht hft))

end LeanCH.BR.WeightedSD

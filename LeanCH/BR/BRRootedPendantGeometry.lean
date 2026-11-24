import LeanCH.BR.BRDonorSinks

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- Four distinct labels, an induced transitive triangle with top r, and
the pendant label independent of the triangle's top and bottom. -/
structure PendantFrame (D : CH.Digraph) (V : Finset ℕ) (r h u t : ℕ) : Prop where
  root_mem : r∈V
  middle_mem : h∈V
  bottom_mem : u∈V
  pendant_mem : t∈V
  rh : r≠h
  ru : r≠u
  rt : r≠t
  hu : h≠u
  ht : h≠t
  ut : u≠t
  root_middle : D r h=true
  middle_bottom : D h u=true
  root_bottom : D r u=true
  no_middle_root : ¬D h r=true
  no_bottom_middle : ¬D u h=true
  no_bottom_root : ¬D u r=true
  no_root_pendant : ¬D r t=true
  no_pendant_root : ¬D t r=true
  no_bottom_pendant : ¬D u t=true
  no_pendant_bottom : ¬D t u=true

def InducedOutPendant (D : CH.Digraph) (V : Finset ℕ) (r h u t : ℕ) : Prop :=
  PendantFrame D V r h u t ∧ D h t=true ∧ ¬D t h=true

def InducedInPendant (D : CH.Digraph) (V : Finset ℕ) (r h u t : ℕ) : Prop :=
  PendantFrame D V r h u t ∧ D t h=true ∧ ¬D h t=true

def RootedPendant (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) : Prop :=
  ∃ h u t,InducedOutPendant D V r h u t ∨ InducedInPendant D V r h u t

theorem pendant_frame_of_pattern {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 2) {r h u t : ℕ} (hr : r∈V) (hh : h∈V) (hu : u∈V) (ht : t∈V)
    (erh : D r h=true) (ehu : D h u=true) (eru : D r u=true)
    (nrt : ¬D r t=true) (ntr : ¬D t r=true)
    (nut : ¬D u t=true) (ntu : ¬D t u=true) : PendantFrame D V r h u t := by
  refine ⟨hr,hh,hu,ht,?_,?_,?_,?_,?_,?_,erh,ehu,eru,?_,?_,?_,nrt,ntr,nut,ntu⟩
  · rintro rfl; exact loopfree hf (by decide) hr erh
  · rintro rfl; exact loopfree hf (by decide) hr eru
  · rintro rfl; exact ntu eru
  · rintro rfl; exact loopfree hf (by decide) hh ehu
  · rintro rfl; exact ntu ehu
  · rintro rfl; exact nrt eru
  · exact digonfree hf le_rfl hr hh erh
  · exact digonfree hf le_rfl hh hu ehu
  · exact digonfree hf le_rfl hr hu eru

/-- Rooted absence alone forces the D/U/M closure; no saturation is used. -/
theorem pendant_absent_strong_heads_all {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) {r t d : ℕ} (hno : ¬RootedPendant D V r)
    (hr : r∈V) (ht : t∈V) (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (nrt : ¬D r t=true) (hd : d∈S) (edt : D d t=true) : ∀ m∈S,D m t=true := by
  classical
  have hSV : S⊆V := hSO.trans outN_subset
  have hroot : ∀ s∈S,D r s=true := fun s hs=>(mem_outN.mp (hSO hs)).2
  have ntr : ¬D t r=true := fun e=>donor_no_triangle hf hr (hSV hd) ht (hroot d hd) edt e
  let A:=S.filter (fun s=>D s t=true ∨ D t s=true)
  have hclosedA : ClosedBank D S A := by
    intro x hx y hy exy
    obtain ⟨hxS,hxt⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hy,?_⟩
    by_contra hn
    have nyt : ¬D y t=true := fun e=>hn (Or.inl e)
    have nty : ¬D t y=true := fun e=>hn (Or.inr e)
    have frame := pendant_frame_of_pattern (hf.mono_bound (by decide)) hr (hSV hxS)
      (hSV hy) ht (hroot x hxS) exy (hroot y hy) nrt ntr nyt nty
    apply hno
    refine ⟨x,y,t,?_⟩
    rcases hxt with ext|etx
    · exact Or.inl ⟨frame,ext,digonfree hf (by decide) (hSV hxS) ht ext⟩
    · exact Or.inr ⟨frame,etx,digonfree hf (by decide) ht (hSV hxS) etx⟩
  have hadj : ∀ s∈S,D s t=true ∨ D t s=true := by
    intro s hs
    obtain ⟨n,w⟩ := hst d hd s hs
    exact (mem_filter.mp (walk_closed_bank hclosedA (mem_filter.mpr ⟨hd,Or.inl edt⟩) w).1).2
  let U:=S.filter (fun s=>¬D s t=true)
  have hclosedU : ClosedBank D S U := by
    intro x hx y hy exy
    obtain ⟨hxS,nxt⟩ := mem_filter.mp hx
    have etx := (hadj x hxS).resolve_left nxt
    refine mem_filter.mpr ⟨hy,?_⟩
    exact fun eyt=>donor_no_triangle hf ht (hSV hxS) (hSV hy) etx exy eyt
  intro m hm
  by_contra nmt
  obtain ⟨n,w⟩ := hst m hm d hd
  exact (mem_filter.mp (walk_closed_bank hclosedU (mem_filter.mpr ⟨hm,nmt⟩) w).1).2 edt

/-- A genuinely partial outgoing contact with a strong bank supplies a
pendant whose triangle top is the prescribed original root. -/
theorem rooted_pendant_of_strong_mixed {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) {r t d m : ℕ} (hr : r∈V) (ht : t∈V)
    (hSO : S⊆outN D V r) (hst : StrongBank D S) (nrt : ¬D r t=true)
    (hd : d∈S) (edt : D d t=true) (hm : m∈S) (nmt : ¬D m t=true) :
    RootedPendant D V r := by
  by_contra hn
  exact nmt (pendant_absent_strong_heads_all hf hn hr ht hSO hst nrt hd edt m hm)

theorem pendant_absent_strong_external_uniform {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) {r t : ℕ} (hno : ¬RootedPendant D V r)
    (hr : r∈V) (ht : t∈V) (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (nrt : ¬D r t=true) : ∀ x∈S,∀ y∈S,D x t=D y t := by
  intro x hx y hy
  by_cases ex : D x t=true
  · rw [ex,pendant_absent_strong_heads_all hf hno hr ht hSO hst nrt hx ex y hy]
  · have ey : ¬D y t=true := fun e=>ex
      (pendant_absent_strong_heads_all hf hno hr ht hSO hst nrt hy e x hx)
    exact (Bool.eq_false_iff.mpr ex).trans (Bool.eq_false_iff.mpr ey).symm

end LeanCH.BR.WeightedSD

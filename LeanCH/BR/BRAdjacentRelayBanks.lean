import LeanCH.BR.BRRelayFold
import LeanCH.BR.BRWeightedStrictBranchAtom

namespace LeanCH.BR.WeightedSD.AdjacentRelay
open Finset BRq2 BRq3 BR45 BRsub RelayFold

structure Base (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) : Prop where
  free : QFree D V 3
  umem : u∈V
  hmem : h∈V
  tmem : t∈V
  uh : u≠h
  ut : u≠t
  ht : h≠t
  edge : D h t=true
  adjacent : D u t=true

def precut (D : CH.Digraph) (u h t : ℕ) : CH.Digraph := eraseArc (eraseArc D u h) u t
def epsilon (D : CH.Digraph) (u h : ℕ) : ℕ := if D u h=true then 1 else 0

theorem precut_row {D : CH.Digraph} {u h t x : ℕ} (hx : x≠u) (y : ℕ) :
    precut D u h t x y=D x y := by simp [precut,eraseArc,hx]

theorem precut_head {D : CH.Digraph} {u h t y : ℕ} (hyh : y≠h) (hyt : y≠t) (x : ℕ) :
    precut D u h t x y=D x y := by simp [precut,eraseArc,hyh,hyt]

theorem precut_sub (D : CH.Digraph) (u h t x y : ℕ) :
    precut D u h t x y=true→D x y=true :=
  fun he=>eraseArc_sub D u h x y (eraseArc_sub (eraseArc D u h) u t x y he)

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B

theorem toRelay : RelayFold.Base (precut D u h t) V u h t := by
  refine ⟨qfree_sub (precut_sub D u h t) B.free,B.umem,B.hmem,B.tmem,
    B.uh,B.ut,B.ht,?_,?_,?_,?_⟩
  · simpa only [precut_row B.uh.symm] using B.edge
  · simp [precut,eraseArc,B.ht]
  · simp [precut,eraseArc]
  · simpa only [precut_row B.ut.symm] using
      digonfree B.free (by decide) B.umem B.tmem B.adjacent

theorem X_eq : X (precut D u h t) V h t=X D V h t := by
  ext x
  by_cases hx : x=u
  · subst x; simp [mem_X,precut,eraseArc,B.ht,B.adjacent]
  · simp only [mem_X,precut_row hx]

theorem X0_eq : X0 (precut D u h t) V u h t=X0 D V u h t := by
  ext x
  have hi : precut D u h t x u=D x u := precut_head B.uh B.ut x
  simp only [X0,mem_sdiff,B.X_eq,mem_inN,hi]

theorem X1_eq : X1 (precut D u h t) V u h t=X1 D V u h t := by
  ext x
  have hi : precut D u h t x u=D x u := precut_head B.uh B.ut x
  simp only [X1,mem_inter,B.X_eq,mem_inN,hi]

theorem X_ne {x : ℕ} (hx : x∈X D V h t) : x≠u ∧ x≠h ∧ x≠t := by
  have f:=B.toRelay.X_facts (B.X_eq.symm ▸ hx)
  exact ⟨f.2.1,f.2.2.1,f.2.2.2.1⟩

theorem C_not_h : h∉C D V u h t := by
  intro hh
  rcases (mem_C.mp hh).2.2 with hx|⟨e,he,ehe⟩
  · exact (B.X_ne (RelayFold.Base.X0_X hx)).2.1 rfl
  · exact digonfree B.free (by decide) B.hmem (mem_X0.mp he).1 ehe (mem_X0.mp he).2.1

theorem C_not_t : t∉C D V u h t := by
  intro hh
  rcases (mem_C.mp hh).2.2 with hx|⟨e,he,ete⟩
  · exact (B.X_ne (RelayFold.Base.X0_X hx)).2.2 rfl
  · exact donor_no_triangle B.free B.hmem B.tmem (mem_X0.mp he).1 B.edge ete (mem_X0.mp he).2.1

theorem C_eq : C (precut D u h t) V u h t=C D V u h t := by
  ext x
  have bank : (x∈X0 (precut D u h t) V u h t ∨
      ∃e∈X0 (precut D u h t) V u h t,precut D u h t x e=true) ↔
      (x∈X0 D V u h t ∨ ∃e∈X0 D V u h t,D x e=true) := by
    rw [B.X0_eq]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨e,he,edge⟩; exact ⟨e,he,precut_sub D u h t x e edge⟩
    · rintro ⟨e,he,edge⟩
      have f:=B.X_ne (RelayFold.Base.X0_X he)
      exact ⟨e,he,(precut_head f.2.1 f.2.2 x).symm ▸ edge⟩
  rw [mem_C,bank,mem_C]
  constructor
  · rintro ⟨hx,he,hb⟩; exact ⟨hx,precut_sub D u h t u x he,hb⟩
  · rintro ⟨hx,he,hb⟩
    have hc : x∈C D V u h t := mem_C.mpr ⟨hx,he,hb⟩
    have nh : x≠h := fun eq=>B.C_not_h (eq ▸ hc)
    have nt : x≠t := fun eq=>B.C_not_t (eq ▸ hc)
    exact ⟨hx,(precut_head nh nt u).symm ▸ he,hb⟩

theorem R_eq : R (precut D u h t) V u h t=R D V u h t := by
  ext x
  have bank : (precut D u h t x u=true ∨
      ∃z∈X1 (precut D u h t) V u h t,precut D u h t x z=true) ↔
      (D x u=true ∨ ∃z∈X1 D V u h t,D x z=true) := by
    rw [precut_head B.uh B.ut,B.X1_eq]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨z,hz,he⟩; exact ⟨z,hz,precut_sub D u h t x z he⟩
    · rintro ⟨z,hz,he⟩
      have f:=B.X_ne (RelayFold.Base.X1_X hz)
      exact ⟨z,hz,(precut_head f.2.1 f.2.2 x).symm ▸ he⟩
  simp only [mem_R,precut_row B.ut.symm,bank]

theorem W_eq : W (precut D u h t) V u h t=W D V u h t := by
  simp only [W,B.X1_eq,B.R_eq]

theorem R_no_receiver {r : ℕ} (hr : r∈R D V u h t) : ¬D r u=true := by
  exact fun eru=>donor_no_triangle B.free B.umem B.tmem (mem_R.mp hr).1
    B.adjacent (mem_R.mp hr).2.1 eru

theorem R_facts {r : ℕ} (hr : r∈R D V u h t) :
    r∈V ∧ r≠u ∧ r≠h ∧ r≠t ∧ ¬D u r=true := by
  have f:=B.toRelay.R_facts (B.R_eq.symm ▸ hr)
  refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,?_⟩
  simpa only [precut_head f.2.2.1 f.2.2.2.1] using f.2.2.2.2.2.2.2.2

theorem validCuts_iff (K : Finset (ℕ×ℕ)) :
    ValidCuts (precut D u h t) V u h t K↔ValidCuts D V u h t K := by
  unfold ValidCuts
  simp only [B.X1_eq,B.R_eq]
  constructor <;> intro hk z r he
  · obtain ⟨hz,hr,ezr⟩:=hk z r he
    exact ⟨hz,hr,precut_sub D u h t z r ezr⟩
  · obtain ⟨hz,hr,ezr⟩:=hk z r he
    exact ⟨hz,hr,(precut_row (B.X_ne (RelayFold.Base.X1_X hz)).1 r).symm ▸ ezr⟩

theorem eligible_eq (K : Finset (ℕ×ℕ)) {r : ℕ} (hr : r∈R D V u h t) :
    eligible (precut D u h t) V u h t K r=eligible D V u h t K r := by
  ext w
  rw [mem_eligible,B.W_eq,mem_eligible]
  have f:=B.R_facts hr
  constructor
  · rintro ⟨hw,nrw,nwr,hret⟩
    have hwu := (mem_W.mp hw).2.2.2.1
    refine ⟨hw,?_,?_,?_⟩
    · simpa only [precut_row f.2.1] using nrw
    · simpa only [precut_row hwu] using nwr
    · intro x hx ewx exr
      have hh := hret x hx ((precut_row hwu x).symm ▸ ewx)
        ((precut_head f.2.2.1 f.2.2.2.1 x).symm ▸ exr)
      simpa only [B.X1_eq] using hh
  · rintro ⟨hw,nrw,nwr,hret⟩
    have hwu := (mem_W.mp hw).2.2.2.1
    refine ⟨hw,?_,?_,?_⟩
    · simpa only [precut_row f.2.1] using nrw
    · simpa only [precut_row hwu] using nwr
    · intro x hx ewx exr
      have hh := hret x hx (precut_sub D u h t w x ewx) (precut_sub D u h t x r exr)
      simpa only [B.X1_eq] using hh

theorem selected_iff (K : Finset (ℕ×ℕ)) (Q : ℕ→Finset ℕ) :
    Selected (precut D u h t) V u h t K Q↔Selected D V u h t K Q := by
  unfold Selected
  rw [B.R_eq]
  constructor <;> intro hQ r hr <;> simpa only [B.eligible_eq K hr] using hQ r hr

end Base
end LeanCH.BR.WeightedSD.AdjacentRelay

import LeanCH.BR.BRDonorWalks
import LeanCH.BR.BRWeightedDeletedOrder

/-! Original banks of the complete two-receiver relay fold.
Provenance: TwoReceiverSharedDonorQuotaFold and CompleteRelayTargetBank,
14 November 2026, independently paper-audited. No payment is assumed here. -/
namespace LeanCH.BR.WeightedSD.RelayFold
open Finset BRq2 BRq3 BR45 BRsub

structure Base (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) : Prop where
  free : QFree D V 3
  umem : u∈V
  hmem : h∈V
  tmem : t∈V
  uh : u≠h
  ut : u≠t
  ht : h≠t
  edge : D h t=true
  miss_h : ¬D u h=true
  miss_t : ¬D u t=true
  back : ¬D t u=true

noncomputable def X (D : CH.Digraph) (V : Finset ℕ) (h t : ℕ) := inN D V h\inN D V t
noncomputable def X0 (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) := X D V h t\inN D V u
noncomputable def X1 (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) := X D V h t∩inN D V u
noncomputable def C (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) :=
  (outN D V u).filter (fun x=>x∈X0 D V u h t ∨ ∃e∈X0 D V u h t,D x e=true)
noncomputable def R (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) :=
  (outN D V t).filter (fun r=>D r u=true ∨ ∃z∈X1 D V u h t,D r z=true)
noncomputable def W (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) :=
  V\({h,t,u}∪X1 D V u h t∪R D V u h t)

theorem mem_X {D : CH.Digraph} {V : Finset ℕ} {h t x : ℕ} :
    x∈X D V h t ↔ x∈V ∧ D x h=true ∧ ¬D x t=true := by
  classical
  simp only [X,mem_sdiff,mem_inN]
  tauto

theorem mem_X0 {D : CH.Digraph} {V : Finset ℕ} {u h t x : ℕ} :
    x∈X0 D V u h t ↔ x∈V ∧ D x h=true ∧ ¬D x t=true ∧ ¬D x u=true := by
  classical
  simp only [X0,mem_sdiff,mem_X,mem_inN]
  tauto

theorem mem_X1 {D : CH.Digraph} {V : Finset ℕ} {u h t x : ℕ} :
    x∈X1 D V u h t ↔ x∈V ∧ D x h=true ∧ ¬D x t=true ∧ D x u=true := by
  classical
  simp only [X1,mem_inter,mem_X,mem_inN]
  tauto

theorem mem_C {D : CH.Digraph} {V : Finset ℕ} {u h t x : ℕ} :
    x∈C D V u h t ↔ x∈V ∧ D u x=true ∧
      (x∈X0 D V u h t ∨ ∃e∈X0 D V u h t,D x e=true) := by
  classical
  simp only [C,mem_filter,mem_outN,and_assoc]

theorem mem_R {D : CH.Digraph} {V : Finset ℕ} {u h t x : ℕ} :
    x∈R D V u h t ↔ x∈V ∧ D t x=true ∧
      (D x u=true ∨ ∃z∈X1 D V u h t,D x z=true) := by
  classical
  simp only [R,mem_filter,mem_outN,and_assoc]

theorem mem_W {D : CH.Digraph} {V : Finset ℕ} {u h t x : ℕ} :
    x∈W D V u h t ↔ x∈V ∧ x≠h ∧ x≠t ∧ x≠u ∧
      x∉X1 D V u h t ∧ x∉R D V u h t := by
  classical
  simp only [W,mem_sdiff,mem_union,mem_insert,mem_singleton]
  tauto

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B

theorem X_facts {x : ℕ} (hx : x∈X D V h t) :
    x∈V ∧ x≠u ∧ x≠h ∧ x≠t ∧ D x h=true ∧ ¬D x t=true ∧ ¬D t x=true := by
  obtain ⟨hxV,exh,nxt⟩ := mem_X.mp hx
  refine ⟨hxV,?_,?_,?_,exh,nxt,?_⟩
  · intro e; subst x; exact B.miss_h exh
  · intro e; subst x; exact loopfree B.free (by decide) B.hmem exh
  · intro e; subst x; exact digonfree B.free (by decide) B.hmem B.tmem B.edge exh
  · intro etx; exact donor_no_triangle B.free B.hmem B.tmem hxV B.edge etx exh

omit B in
theorem X0_X {x : ℕ} (hx : x∈X0 D V u h t) : x∈X D V h t := (mem_sdiff.mp hx).1
omit B in
theorem X1_X {x : ℕ} (hx : x∈X1 D V u h t) : x∈X D V h t := (mem_inter.mp hx).1

omit B in
theorem X_disjoint : Disjoint (X0 D V u h t) (X1 D V u h t) := by
  apply disjoint_left.mpr
  intro x hx hx'
  exact (mem_X0.mp hx).2.2.2 (mem_X1.mp hx').2.2.2

theorem R_facts {r : ℕ} (hr : r∈R D V u h t) :
    r∈V ∧ r≠u ∧ r≠h ∧ r≠t ∧ r∉X D V h t ∧
      D t r=true ∧ ¬D r h=true ∧ ¬D r t=true ∧ ¬D u r=true := by
  obtain ⟨hrV,etr,active⟩ := mem_R.mp hr
  have nrh : ¬D r h=true := fun erh=>donor_no_triangle B.free B.hmem B.tmem hrV B.edge etr erh
  have nrt : ¬D r t=true := fun ert=>digonfree B.free (by decide) B.tmem hrV etr ert
  refine ⟨hrV,?_,?_,?_,?_,etr,nrh,nrt,?_⟩
  · intro e; subst r; exact B.back etr
  · intro e; subst r; exact digonfree B.free (by decide) B.hmem B.tmem B.edge etr
  · intro e; subst r; exact loopfree B.free (by decide) B.tmem etr
  · intro hrX; exact nrh (mem_X.mp hrX).2.1
  · intro eur
    rcases active with eru|⟨z,hz,erz⟩
    · exact digonfree B.free (by decide) B.umem hrV eur eru
    · exact donor_no_triangle B.free B.umem hrV (mem_X1.mp hz).1 eur erz (mem_X1.mp hz).2.2.2

theorem C_facts {x : ℕ} (hx : x∈C D V u h t) :
    x∈V ∧ x≠u ∧ x≠h ∧ x≠t ∧ x∉X1 D V u h t ∧ x∉R D V u h t ∧ D u x=true := by
  obtain ⟨hxV,eux,_⟩ := mem_C.mp hx
  refine ⟨hxV,?_,?_,?_,?_,?_,eux⟩
  · intro e; subst x; exact loopfree B.free (by decide) B.umem eux
  · intro e; subst x; exact B.miss_h eux
  · intro e; subst x; exact B.miss_t eux
  · intro hx1; exact digonfree B.free (by decide) B.umem hxV eux (mem_X1.mp hx1).2.2.2
  · intro hxR; exact (B.R_facts hxR).2.2.2.2.2.2.2.2 eux

theorem X0_W : X0 D V u h t⊆W D V u h t := by
  intro x hx
  obtain ⟨hxV,hxu,hxh,hxt,_,_,_⟩ := B.X_facts (X0_X hx)
  refine mem_W.mpr ⟨hxV,hxh,hxt,hxu,?_,?_⟩
  · exact fun hx1=>disjoint_left.mp X_disjoint hx hx1
  · intro hxR; exact (B.R_facts hxR).2.2.2.2.1 (X0_X hx)

end Base
end LeanCH.BR.WeightedSD.RelayFold


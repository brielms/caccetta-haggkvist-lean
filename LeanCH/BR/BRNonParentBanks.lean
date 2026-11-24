import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BR45Base

/-! Actual head banks in the acyclic non-parent set of a specified root. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45

def nonParentSet (D : CH.Digraph) (V : Finset ℕ) (z : ℕ) : Finset ℕ :=
  V\insert z (inN D V z)

theorem mem_nonParentSet {D : CH.Digraph} {V : Finset ℕ} {z x : ℕ} :
    x∈nonParentSet D V z ↔ x∈V ∧ x≠z ∧ ¬D x z=true := by
  simp only [nonParentSet,mem_sdiff,mem_insert,mem_inN]
  tauto

theorem punctured_ball_nonParent {q j : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) {z : ℕ} (hz : z∈V) (hj : j+1≤q) :
    (ball D V z j).erase z⊆nonParentSet D V z := by
  intro x hx
  obtain ⟨hxz,hxb⟩ := mem_erase.mp hx
  exact mem_nonParentSet.mpr ⟨ball_subset hxb,hxz,no_back_arc hf hz hxb hj⟩

theorem heads_in_punctured_ball {q j : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) {z : ℕ} (hz : z∈V) (hq : 1≤q) (hj : 1≤j) :
    outN D V z⊆(ball D V z j).erase z := by
  intro x hx
  refine mem_erase.mpr ⟨?_,ball_mono_radius hj (ball_of_adj (outN_subset hx) (mem_outN.mp hx).2)⟩
  intro he
  subst x
  exact loopfree hf hq hz (mem_outN.mp hx).2

theorem punctured_ball_sink_heads_layer {q j : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) {z v : ℕ} (hz : z∈V) (hj : j+1≤q)
    (hv : v∈(ball D V z j).erase z)
    (hsink : ∀x∈(ball D V z j).erase z,¬D v x=true) :
    outN D V v⊆(ball D V z (j+1)).erase z\(ball D V z j).erase z := by
  intro x hx
  have hxz : x≠z := by
    intro he
    subst x
    exact no_back_arc hf hz (mem_of_mem_erase hv) hj (mem_outN.mp hx).2
  exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨hxz,
    ball_step (mem_of_mem_erase hv) (outN_subset hx) (mem_outN.mp hx).2⟩,
    fun h=>hsink x h (mem_outN.mp hx).2⟩

theorem nonParent_sink_heads_in {D : CH.Digraph} {V : Finset ℕ} {z t : ℕ}
    (ht : t∈nonParentSet D V z) (hsink : ∀x∈nonParentSet D V z,¬D t x=true) :
    outN D V t⊆inN D V z := by
  intro x hx
  by_contra h
  have hxz : x≠z := by
    intro he
    subst x
    exact (mem_nonParentSet.mp ht).2.2 (mem_outN.mp hx).2
  have hnxz : ¬D x z=true := fun e=>h (mem_inN.mpr ⟨outN_subset hx,e⟩)
  exact hsink x (mem_nonParentSet.mpr ⟨outN_subset hx,hxz,hnxz⟩) (mem_outN.mp hx).2

/-- Failure of finite acyclicity supplies an actual closed walk with both
the lower girth bound and the finite-set upper bound. -/
theorem closed_walk_of_not_acyclic {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ}
    (hf : QFree D V q) (hUV : U⊆V) (hn : ¬QFree D U U.card) :
    ∃x∈U,∃m,q+1≤m ∧ m≤U.card ∧ Walk D U x x m := by
  unfold QFree at hn
  push Not at hn
  obtain ⟨x,m,hm,hmc,w⟩ := hn
  have hqm : q<m := by
    by_contra h
    exact hf x m hm (by omega) (w.mono hUV)
  cases m with
  | zero => omega
  | succ m =>
    obtain ⟨_,_,hx,_⟩ := w.unsnoc
    exact ⟨x,hx,m+1,by omega,hmc,w⟩

end LeanCH.BR.WeightedSD

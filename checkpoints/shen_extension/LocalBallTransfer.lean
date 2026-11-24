import checkpoints.shen_extension.PrivateHeadClone
import checkpoints.shen_extension.OneSpareTurns

namespace LeanCH.BR.LocalBallTransfer
open Finset BRq2 BRq3 BR45

/-- Keep all old heads except at marked rows, where only heads in W
remain. If the whole inner ball is paid in W, every ambient degree-based
ball bound can now be used inside W up to the stated radius. -/
theorem localize {D V W a k q s} (free : QFree D V q) (sub : W⊆V) (aw : a∈W)
    (degree : ∀v∈V,s≤(outN D V v).card)
    (inner : ∀v∈ball D W a (k-1), s≤(outN D W v).card) :
    ∃E, QFree E V q ∧ (∀v∈V,s≤(outN E V v).card) ∧
      ∀i,i≤k → ball E V a i⊆ball D W a i := by
  classical
  let B := ball D W a (k-1)
  let E : CH.Digraph := fun u v=>if u∈B ∧ v∉W then false else D u v
  have arcs {u v} (edge : E u v=true) : D u v=true := by
    dsimp [E] at edge
    split at edge <;> simp_all
  refine ⟨E,qfree_sub (fun _ _=>arcs) free,?_,?_⟩
  · intro v vm
    by_cases here : v∈B
    · apply (inner v here).trans (card_le_card ?_)
      intro w wm
      have ⟨ww,edge⟩ := mem_outN.mp wm
      exact mem_outN.mpr ⟨sub ww,by simpa [E,ww] using edge⟩
    · apply (degree v vm).trans (card_le_card ?_)
      intro w wm
      exact mem_outN.mpr ⟨outN_subset wm,by simpa [E,here] using (mem_outN.mp wm).2⟩
  · intro i
    induction i with
    | zero =>
      intro _ v vm
      obtain ⟨_,j,hj,walk⟩ := mem_ball.mp vm
      obtain rfl : j=0 := by omega
      cases walk
      exact self_mem_ball aw
    | succ i ih =>
      intro fit v vm
      by_cases old : v∈ball E V a i
      · exact ball_mono_radius (Nat.le_succ i) (ih (by omega) old)
      obtain ⟨u,um,edge⟩ := ball_succ_pred (sub aw) vm old
      have pw := ih (by omega) um
      have ub : u∈B := ball_mono_radius (by omega : i≤k-1) pw
      have vw : v∈W := by
        by_contra missing
        simp [E,ub,missing] at edge
      exact ball_step pw vw (arcs edge)

/-- A nonempty carrier of at most 2q labels with every row live contains
two distinct rows with a single internal head. This also identifies a
light row outside any one preselected label. -/
theorem two_light {D W q} (free : QFree D W q) (hq : 1≤q) (live : W.Nonempty)
    (size : W.card≤2*q) (positive : ∀v∈W,0<(outN D W v).card) :
    ∃a∈W,∃b∈W,a≠b ∧ (outN D W a).card=1 ∧ (outN D W b).card=1 := by
  have first : ∃a∈W,(outN D W a).card=1 := by
    by_contra! none
    have all (v) (vm : v∈W) : 2≤(outN D W v).card := by have := positive v vm; have := none v vm; omega
    have := corB hq free all live
    omega
  obtain ⟨a,am,one⟩ := first
  by_contra! none
  have other (v) (vm : v∈W) (ne : v≠a) : 2≤(outN D W v).card := by
    have bad := none a am v vm (Ne.symm ne) one
    have := positive v vm
    omega
  obtain ⟨b,bm⟩ := card_pos.mp (positive a am)
  have edge := (mem_outN.mp bm).2
  have ne : b≠a := by
    intro eq
    subst b
    exact free a 1 (by decide) hq (.step am edge (.refl a))
  exact PrivateHeadClone.degree_two_obstruction free hq size am (outN_subset bm) edge ne other

/-- A cut with two light rows cannot hide both beyond a growing ball.
The degree-two ball bound is invoked on a legal subgraph of the original
ambient digraph. All labels, including the reached light row, are retained. -/
theorem reach_light {D V W a k q} (free : QFree D V q) (hq : 1≤q) (sub : W⊆V) (aw : a∈W)
    (degree : ∀v∈V,2≤(outN D V v).card) (positive : ∀v∈W,0<(outN D W v).card)
    (size : W.card≤2*q) (fit : k≤q) (pressure : W.card<2*k+3) :
    ∃b∈ball D W a k,(outN D W b).card=1 := by
  classical
  by_contra! none
  have heavy (v) (vm : v∈ball D W a k) : 2≤(outN D W v).card := by
    have := positive v (ball_subset vm)
    have := none v vm
    omega
  obtain ⟨E,hf,paid,stay⟩ := localize free sub aw degree
    (fun v vm=>heavy v (ball_mono_radius (Nat.sub_le k 1) vm))
  have lower := (ball_growth q hq E V hf paid a (sub aw) k fit).trans (card_le_card (stay k le_rfl))
  obtain ⟨u,um,v,vm,ne,lo,lo'⟩ := two_light (free.mono_set sub) hq ⟨a,aw⟩ size positive
  have avoid : ({u,v} : Finset ℕ)⊆W\ball D W a k := by
    apply insert_subset (mem_sdiff.mpr ⟨um,fun h=>none u h lo⟩)
    exact singleton_subset_iff.mpr (mem_sdiff.mpr ⟨vm,fun h=>none v h lo'⟩)
  have cnt := card_le_card avoid
  rw [card_pair ne,card_sdiff_of_subset ball_subset] at cnt
  omega

#print axioms localize
#print axioms two_light
#print axioms reach_light
end LeanCH.BR.LocalBallTransfer

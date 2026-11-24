import checkpoints.shen_extension.BoundaryOneOmission
import checkpoints.shen_extension.OneSpareShellEscape
import checkpoints.shen_extension.BoundaryPrefixRank
import checkpoints.shen_extension.RootLayerTransit
namespace LeanCH.BR.OddBoundaryLayers
open Finset BRq2 BRq3 BR45 BRsGen

/-- When an acyclic first shell and the next shell both have exactly r
labels, a marked sink takes the whole second shell as its outgoing row.
Every label of the original third layer belongs to its own second layer. -/
theorem transfer {D V q r u} (free : QFree D V q) (root : u∈V) (reg : OutEq r D V)
    (time : r≤q) (hq : 4≤q) (pos : 0<r) (width : (N2 D V u).card=r) :
    ∃s∈outN D V u,outN D V s=N2 D V u ∧ N3 D V u⊆N2 D V s := by
  classical
  have dim := reg u root
  obtain ⟨s,sm,stop⟩ := exists_sink (free.mono_set (outN_subset : outN D V u⊆V))
    (card_pos.mp (by omega)) (by omega)
  have eq : outN D V s=N2 D V u := eq_of_subset_of_card_le
    (fun a am=>(mem_union.mp (headX (free.mono_bound hq) root sm (outN_subset am) (mem_outN.mp am).2)).resolve_left
      (fun ax=>stop a ax (mem_outN.mp am).2)) (by rw [width,reg s (outN_subset sm)])
  refine ⟨s,sm,eq,?_⟩
  intro z zm
  obtain ⟨y,ym,yz⟩ := ball_succ_pred root (mem_N3.mp zm).1 (mem_N3.mp zm).2
  have yy : y∈N2 D V u := mem_sdiff.mpr ⟨ym,fun low=>(mem_N3.mp zm).2 (ball_step low (N3_subV zm) yz)⟩
  have sy : y∈outN D V s := eq ▸ yy
  refine mem_sdiff.mpr ⟨ball_step (ball_of_adj (outN_subset sy) (mem_outN.mp sy).2) (N3_subV zm) yz,?_⟩
  intro early
  rcases (mem_ball_one (outN_subset sm)).mp early with same|head
  · exact (mem_N3.mp zm).2 (same ▸ ball_mono_radius (by decide : 1≤2) (X_B1 sm))
  · exact (mem_N3.mp zm).2 (mem_N2.mp (eq ▸ head)).1

/-- An equal third ball at a small root forces all four layers to have
degree size and hence forces another full layer at the next step. -/
theorem fifth_at_tight {D V q r u} (free : QFree D V q) (root : u∈V) (reg : OutEq r D V)
    (hr : 7≤r) (time : r+1≤q) (small : (ball D V u 3).card≤3*r+1)
    (fourth : (ball D V u 4).card=4*r+1) : 5*r+1≤(ball D V u 5).card := by
  have deg x (xm : x∈V) := (reg x xm).ge
  obtain ⟨two,three⟩ := BoundaryPrefixRank.third_tight free root deg (by omega) time small
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) root
  rw [reg u root] at one
  have zero : (ball D V u 0).card=1 := by
    have eq : ball D V u 0={u} := eq_of_subset_of_card_le
      (fun _ m=>mem_singleton.mpr (eq_of_mem_ball_zero m)) (by
        rw [card_singleton]; exact card_pos.mpr ⟨u,self_mem_ball root⟩)
    rw [eq,card_singleton]
  have dif (k : ℕ) := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k≤k+1 by omega))
  have layers (i) (h : i<4) : (ball D V u (i+1)\ball D V u i).card=r := by
    have := dif i
    interval_cases i <;> simp only [Nat.reduceAdd] at * <;> omega
  have nextStep := EqualLayerTransit.next_layer free root deg (by omega) (by omega) (by omega : r/2+4≤q) (by decide) layers
  have sum := dif 4
  simp only [Nat.reduceAdd] at nextStep sum
  omega

/-- If the fourth and fifth balls are everywhere tight and the third
ball has at most one extra label, no graph realizes the profile.
The quotient and degree are independent inputs. -/
theorem exclude_flat {D V q r} (free : QFree D V q) (live : V.Nonempty) (reg : OutEq r D V)
    (hr : 7≤r) (time : r+1≤q)
    (tri : ∀u∈V,(ball D V u 3).card≤3*r+2)
    (quad : ∀u∈V,(ball D V u 4).card=4*r+1) (fifth : ∀u∈V,(ball D V u 5).card=5*r) : False := by
  have deg x (xm : x∈V) := (reg x xm).ge
  have profiles u (um : u∈V) : (N2 D V u).card=r ∧ (N3 D V u).card=r+1 := by
    have ub := tri u um
    have f4 := quad u um
    have f5 := fifth u um
    have n3 : (ball D V u 3).card=3*r+2 := by
      by_contra ne
      have := fifth_at_tight free um reg hr time (by omega) f4
      omega
    have b2 := BoundaryPrefixRank.second_cap free um deg (by omega) time ub
    have base := card_ball_two_ge_twice (by omega : 2≤r) (free.mono_bound (by omega)) deg um
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) um
    rw [reg u um] at one
    have two := @card_B2 D V u
    have three := @card_B3 D V u
    have d4 := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    by_cases oneMore : (N2 D V u).card=r+1
    · have := OneOmissionSinkBank.fourth_at_boundary free um deg hr time (reg u um) oneMore (by omega)
      omega
    by_cases twoMore : r+1<(N2 D V u).card
    · have := SparseCycleReturns.two_deficient free um deg (reg u um) hr (by omega) (by omega) (by omega)
      omega
    omega
  obtain ⟨u,um⟩ := live
  obtain ⟨s,sm,_,sub⟩ := transfer free um reg (by omega) (by omega) (by omega) (profiles u um).1
  have := card_le_card sub
  have := (profiles u um).2
  have := (profiles s (outN_subset sm)).1
  omega

attribute [aesop safe forward (immediate := [free,root,reg,time,hq,pos,width]) (rule_sets := [CHGraphFamilies])] transfer
attribute [aesop safe forward (immediate := [free,root,reg,hr,time,small,fourth]) (rule_sets := [CHGraphFamilies])] fifth_at_tight
attribute [aesop safe forward (immediate := [free,live,reg,hr,time,tri,quad,fifth]) (rule_sets := [CHGraphFamilies])] exclude_flat
#print axioms transfer
#print axioms fifth_at_tight
#print axioms exclude_flat
end LeanCH.BR.OddBoundaryLayers

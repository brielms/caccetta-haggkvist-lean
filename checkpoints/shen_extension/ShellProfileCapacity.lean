import checkpoints.shen_extension.EqualShellRows
import LeanCH.BR.BRsubTripleLayers

namespace LeanCH.BR.ShellProfileCapacity
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity RetainedLayerCapacity

theorem short_second {D V q r u} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (um : u∈V) (three : (ball D V u 3).card≤3*r) :
    (ball D V u 2).card≤2*r+1 := by
  let X := outN D V u
  have xv : X⊆V := outN_subset
  have deg x (xm : x∈V) := (reg x xm).ge
  have xsize : X.card=r := reg u um
  by_cases mid : (ball D V u 2).card=2*r+2
  · let W := (ball D V u 2).erase u
    have sub : X⊆W := by
      rw [show X=(ball D V u 1).erase u from (erase_ball_one_eq_outN free (by omega) um).symm]
      exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    have rr := minOut_prefix_erase (d:=2) free um (by omega : 2+1≤q) deg
      (show 2+(ball D V u 3 \ ball D V u 2).card≤r by omega)
    exact False.elim (high_half_two_core_false (by omega : 5≤r)
      ((free.mono_bound (by omega : r-1≤q)).mono_set (show W⊆V from (erase_subset _ _).trans ball_subset))
      (by dsimp [W]; rw [card_erase_of_mem (self_mem_ball um),mid]; omega) rr sub xsize
      (fun x xm=>(deg x (xv xm)).trans (card_le_card
        (outN_prefix_erase_root free um (by omega : 1+1≤q) (X_B1 xm)))))
  by_contra miss
  have grow := PrefixDegreeGrowth.raise_floor (j:=2) (lo:=2*r+3) (target:=3*r+1)
    free um (by omega) deg (by omega) (by omega) (by omega) (by
      intro m lo hi
      by_cases fit : m≤3*q+1
      · exact ⟨3,by decide,by decide,by omega,by omega⟩
      · exact ⟨4,by decide,by decide,by omega,by omega⟩)
  change 3*r+1≤(ball D V u 3).card at grow
  omega

theorem triple_excess {D V q r u} (hf : QFree D V q) (hr : 6≤r) (fit : r≤q+1)
    (ho : OutEq r D V) (hu : u∈V) (b2 : (ball D V u 2).card=2*r+1)
    (b3 : (ball D V u 3).card=3*r+1) (b4 : (ball D V u 4).card≤4*r-1) : False := by
  classical
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  have b1 : (ball D V u 1).card=r+1 := by rw [card_B1 (hf.mono_bound (by omega : 4≤q)) hu,ho u hu]
  have dimY : Y.card+(ball D V u 1).card=(ball D V u 2).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have dimZ : Z.card+(ball D V u 2).card=(ball D V u 3).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have dimT : T.card+(ball D V u 3).card=(ball D V u 4).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (by decide))
  have back := BRsub.equal_triple_layers_no_back (s:=r) hr (hf.mono_bound (by omega : r-1≤q)) hu
    (fun v hv=>(ho v hv).ge) (ho u hu)
    (show Y.card=r by omega) (show Z.card=r by omega) (show T.card≤r-1 by omega)
  have zv : Z⊆V := fun _ hx=>ball_subset (mem_sdiff.mp hx).1
  have minZ (z) (zz : z∈Z) : 2≤(outN D Z z).card := by
    have inc : outN D V z⊆outN D Z z ∪ T := by
      intro x xm
      obtain ⟨xv,e⟩ := mem_outN.mp xm
      have h4 := ball_step (mem_sdiff.mp zz).1 xv e
      by_cases h3 : x∈ball D V u 3
      · apply mem_union_left
        refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨h3,?_⟩,e⟩
        intro h2
        exact back z zz x h2 e
      · exact mem_union_right _ (mem_sdiff.mpr ⟨h4,h3⟩)
    have count := (card_le_card inc).trans (card_union_le _ _)
    rw [ho z (zv zz)] at count
    omega
  have low := corB (D:=D) (U:=Z) (q:=q) (by omega) (hf.mono_set zv)
    minZ (card_pos.mp (by omega))
  omega


def Capacity (r : ℕ) : Prop :=
  ∀a∈Icc (2*r+1) (3*r), (3*r)*(3*r+1)<(3*r-a)*16+(a-r)*(2*r+9)+r*(4*r+2)
instance (r) : Decidable (Capacity r) := by unfold Capacity; infer_instance

/-- Three nested sets of rows in the prefix. The innermost rows keep their
native two-balls and the middle rows keep all their native heads. -/
theorem second_upper {D V q r v} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (room : Capacity r) (reg : OutEq r D V) (root : v∈V)
    (sec : ∀x∈V,2*r+1≤(ball D V x 2).card)
    (mid : (ball D V v 3).card=3*r+1) (last : (ball D V v 4).card≤4*r-1) :
    (ball D V v 2).card≤2*r+1 := by
  have deg x (xm : x∈V) := (reg x xm).ge
  have bn := card_B1 (free.mono_bound (by omega : 4≤q)) root
  have dr := reg v root
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 3≤4))
  have upper := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
  by_contra! big
  have cap := prefix_three_scores (k:=3) (a:=2) (b:=1) (j:=2) (i:=3) (l:=4)
    (h:=2*r+1) (near:=4*r+2) (base:=16) (high:=2*r+9) free root (by omega) (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) deg
    (show 2+(ball D V v 4 \ ball D V v 3).card ≤ r by omega)
    (fun x xm=>sec x (ball_subset (mem_of_mem_erase xm))) (by omega) (fun _ ff rr x xm=>by
      constructor
      · have grow := ball_growth q (by omega) _ _ ff rr x xm
        have := grow 3 (by omega)
        have := grow 4 (by omega)
        omega
      · intro hx
        have score := high_score (k:=r-1) ff (by omega) (by decide : 2≤2) (by omega)
          (by omega) (by omega) rr xm (show r-1+1≤_ by omega)
        omega)
  dsimp only at cap
  simp only [card_erase_of_mem (self_mem_ball root),mid,bn,dr,Nat.add_sub_cancel] at cap
  have fail := room ((ball D V v 2).card-1) (mem_Icc.mpr ⟨by omega,by omega⟩)
  omega

attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,um,three])
  (rule_sets := [CHGraphFamilies])] short_second
attribute [aesop safe forward (immediate := [hf,hr,fit,ho,hu,b2,b3,b4])
  (rule_sets := [CHGraphFamilies])] triple_excess
attribute [aesop safe forward (immediate := [free,hq,hr,fit,room,reg,root,sec,mid,last])
  (rule_sets := [CHGraphFamilies])] second_upper
#print axioms short_second
#print axioms triple_excess
#print axioms second_upper
end LeanCH.BR.ShellProfileCapacity

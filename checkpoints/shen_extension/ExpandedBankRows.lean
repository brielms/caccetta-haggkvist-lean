import checkpoints.shen_extension.ShellBankOrders
namespace LeanCH.BR.ExpandedBankRows
open Finset BRq2 BRq3 BR45 BRsGen BankReachTransfer OneSpareGrowth ConsecutiveShellBanks

/-- A row covering the first outer shell keeps all later labels and
its own internal ball. A positive internal degree gives one additional
distinct label for each step all the way to the allowed horizon. -/
theorem full_row_credit {D V q u w j} (free : QFree D V q) (root : u∈V)
    (wx : w∈outN D V u) (pos : 0<j) (time : j+1≤q)
    (positive : ∀x∈outN D V u,1≤(outN D (outN D V u) x).card)
    (covers : ∀y∈N2 D V u,D w y=true) :
    j+1+((ball D V u (j+1)).card-(ball D V u 1).card)≤(ball D V w j).card := by
  let X := outN D V u
  have xv : X⊆V := outN_subset
  have seen : N2 D V u ⊆ ball D V w 1 := fun _ ym=>
    (mem_ball_one (xv wx)).mpr (.inr (mem_outN.mpr ⟨N2_subV ym,covers _ ym⟩))
  have inside : ball D X w j ⊆ ball D V w j := by
    intro a am
    obtain ⟨ax,l,le,path⟩ := mem_ball.mp am
    exact mem_ball.mpr ⟨xv ax,l,le,path.mono xv⟩
  have sub : ball D X w j⊆ball D V u 1 := fun a am=>X_B1 (ball_subset am)
  have jj : 1+(j-1)=j := by omega
  have ij : 1+1+(j-1)=j+1 := by omega
  have transfer := count_with_prefix (k:=j-1) root sub (show ball D X w j ⊆ ball D V w (1+(j-1)) by rwa [jj]) seen
  rw [ij,jj] at transfer
  have grow := ball_one_growth (free.mono_set xv) positive wx j time
  omega

/-- With only r−1 second-layer slots, every first row can reach the
whole second layer. The next two layers must then sustain a smaller
degree together, with losses only on the outer edge of this pair. -/
theorem outer_slots {D V q r k u d} (free : QFree D V q) (hq : 5≤q)
    (root : u∈V) (reg : OutEq r D V) (hr : 2≤r) (time : k+3≤q)
    (pressure : r≤q+k+1) (ys : (N2 D V u).card+1=r) (dl : 2≤d) (du : d≤5)
    (budget : (N2 D V u).card+(N3 D V u).card≤q*d) :
    r<(ball D V u 4\ball D V u 3).card+d := by
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have xx : X.card=r := reg u root
  have moves := reaches_bank free (by omega) xv yv disjXY
    (fun x xm=>hr.trans (reg x xm).ge)
    (fun x xm=>by rw [←outN_X_eq (free.mono_bound (by omega : 4≤q)) root xm,reg x (xv xm)]; exact ys.le)
    (by omega) (by omega : k≤q) (by omega)
  have f4 := free.mono_bound (show 4≤q by omega)
  have near (x) (xm : x∈X) (z) (zm : z∈Z) : ∃l,l≤k+2 ∧ Walk D V x z l := by
    obtain ⟨y,ym,edge⟩ := ball_succ_pred root (mem_N3.mp zm).1 (mem_N3.mp zm).2
    have yy : y∈Y := mem_sdiff.mpr ⟨ym,fun old=>(mem_N3.mp zm).2 (ball_step old (zv zm) edge)⟩
    obtain ⟨l,_,le,path⟩ := moves x xm y yy
    exact ⟨l+1,by omega,path.snoc (zv zm) edge⟩
  by_contra! poor
  have quota v (vm : v∈Y∪Z) : d≤(outN D (Y∪Z) v).card := by
    have sub : outN D V v⊆outN D (Y∪Z) v ∪ W := by
      intro a am
      have arc := (mem_outN.mp am).2
      have v3 : v∈ball D V u 3 := by
        rcases mem_union.mp vm with yy|zz
        · exact ball_mono_radius (by decide : 2≤3) (mem_N2.mp yy).1
        · exact (mem_N3.mp zz).1
      by_cases outer : a∈ball D V u 3
      · apply mem_union_left
        refine mem_outN.mpr ⟨?_,arc⟩
        by_cases a2 : a∈ball D V u 2
        · apply mem_union_left
          refine mem_sdiff.mpr ⟨a2,?_⟩
          intro early
          rcases (mem_ball_one root).mp early with rfl|ax
          · exact no_back_arc free root v3 (by omega) arc
          · rcases mem_union.mp vm with yy|zz
            · obtain ⟨l,_,le,path⟩ := moves a ax v yy
              exact free a _ (by omega) (by omega) (path.snoc (outN_subset am) arc)
            · obtain ⟨l,le,path⟩ := near a ax v zz
              exact free a _ (by omega) (by omega) (path.snoc (outN_subset am) arc)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨outer,a2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step v3 (outN_subset am) arc,outer⟩)
    have count := (card_le_card sub).trans (card_union_le _ _)
    rw [reg v (union_subset yv zv vm)] at count
    change (ball D V u 4\ball D V u 3).card+_≤_ at poor
    dsimp only [W] at count
    omega
  have live : Y.Nonempty := card_pos.mp (by dsimp [Y]; omega)
  have bound := BRq6.lower_order hq dl (by omega : d<6)
    (free.mono_set (union_subset yv zv)) quota (live.mono subset_union_left)
  have size := card_union_le Y Z
  change Y.card+Z.card≤q*d at budget
  omega

attribute [aesop safe forward (immediate := [free,root,wx,pos,time,positive,covers])
  (rule_sets := [CHGraphFamilies])] full_row_credit
attribute [aesop safe forward (immediate := [free,hq,root,reg,hr,time,pressure,ys,dl,du,budget])
  (rule_sets := [CHGraphFamilies])] outer_slots
#print axioms full_row_credit
#print axioms outer_slots
end LeanCH.BR.ExpandedBankRows

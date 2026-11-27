import checkpoints.shen_extension.JointBankOrderReplay
import checkpoints.shen_extension.JointBankPairLoad

namespace LeanCH.BR.CommonHeadLastCut
open Finset BRq2 BRq3 BR45 FundedCascade BypassRepair BypassBankReplay JointShortcut
open scoped Classical

abbrev heads (D : CH.Digraph) (V : Finset ℕ) (p h : ℕ) := outN D V p ∩ outN D V h

/-- Choose an actual maximum common-head set; if necessary change one of
its two supporting rows. Each common predecessor then misses some head. -/
theorem select_bank {D V q} (free : QFree D V q) (hq : 1≤q) (large : 2≤V.card) :
    ∃ p∈V, ∃ h∈V, p≠h ∧
      (∀ i∈V,∀ j∈V,i≠j → (heads D V i j).card ≤ (heads D V p h).card) ∧
      ∀ u∈jointParents D V p h, ∃ z∈heads D V p h, D u z≠true := by
  classical
  obtain ⟨a,aa,b,bb,ab⟩ := one_lt_card.mp large
  obtain ⟨⟨p,h⟩,pair,top⟩ := V.offDiag.exists_max_image (fun j => (heads D V j.1 j.2).card)
    ⟨(a,b),mem_offDiag.mpr ⟨aa,bb,ab⟩⟩
  obtain ⟨pv,hv,ph⟩ := mem_offDiag.mp pair
  let P := heads D V p h
  have best (i) (iv : i∈V) (j) (jv : j∈V) (ij : i≠j) : (heads D V i j).card≤P.card :=
    top (i,j) (mem_offDiag.mpr ⟨iv,jv,ij⟩)
  by_cases done : ∀ u∈jointParents D V p h,∃ z∈P,D u z≠true
  · exact ⟨p,pv,h,hv,ph,best,done⟩
  push Not at done
  obtain ⟨c,cs,covers⟩ := done
  obtain ⟨cin, _⟩ := mem_inN.mp cs
  obtain ⟨cv,cp⟩ := mem_inN.mp cin
  have diff : c≠p := fun e => loopfree free hq pv (e ▸ cp)
  have sub : P⊆heads D V c p := by
    intro z zP
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨outN_subset (mem_inter.mp zP).1,covers _ zP⟩,(mem_inter.mp zP).1⟩
  refine ⟨c,cv,p,pv,diff,fun i iv j jv ij => (best _ iv _ jv ij).trans (card_le_card sub),?_⟩
  intro u us
  by_contra! allhit
  obtain ⟨ui,up⟩ := mem_inN.mp us
  obtain ⟨uv,uc⟩ := mem_inN.mp ui
  have ne : u≠c := fun e => loopfree free hq cv (e ▸ uc)
  have big : insert p P ⊆ heads D V u c := by
    intro z hz
    rcases mem_insert.mp hz with rfl|zP
    · exact mem_inter.mpr ⟨mem_outN.mpr ⟨pv,up⟩,mem_outN.mpr ⟨pv,cp⟩⟩
    · exact mem_inter.mpr ⟨mem_outN.mpr ⟨outN_subset (mem_inter.mp zP).1,allhit _ (sub zP)⟩,(mem_inter.mp (sub zP)).1⟩
  have pp : p∉P := fun h => loopfree free hq pv (mem_outN.mp (mem_inter.mp h).1).2
  have cmp := (card_le_card big).trans (best u uv c cv ne)
  rw [card_insert_of_notMem pp] at cmp
  omega

/-- Distinct last arcs charged to this one physical tail (for this
assignment). Counting returns that use the same arc only once matters. -/
noncomputable def bill (D : CH.Digraph) (U S : Finset ℕ) (q : ℕ) (f : ℕ → ℕ)
    (y : ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun u => D y u=true ∧ Walk D U (f u) y (q-2))

/-- Seeing a common target and reaching a final payer precludes that
payer's arc back to the row, by a closed walk of exactly q steps. -/
theorem no_back {D V U q z y a} (free : QFree D V q) (hq : 2≤q) (uv : U⊆V)
    (av : a∈V) (zv : z∈V) (path : Walk D U z y (q-2)) (az : D a z=true) : D y a≠true := by
  intro ya
  have w : Walk D V a a ((q-2+1)+1) := .step zv az ((path.mono uv).snoc av ya)
  exact free _ _ (by omega) (by omega) w

theorem parent_data {D V p h u} (us : u∈jointParents D V p h) :
    u∈V ∧ D u p=true ∧ D u h=true := by
  obtain ⟨ui,uh⟩ := mem_inN.mp us
  obtain ⟨uv,up⟩ := mem_inN.mp ui
  exact ⟨uv,up,uh⟩

theorem common_head_retained {D V q p h z} (free : QFree D V q) (hq : 1≤q)
    (pv : p∈V) (hv : h∈V) (mem : z∈heads D V p h) : z∈V \ {p,h} := by
  have vz := outN_subset (mem_inter.mp mem).1
  have a : z≠p := fun e => loopfree free hq pv (e ▸ (mem_outN.mp (mem_inter.mp mem).1).2)
  have b : z≠h := fun e => loopfree free hq hv (e ▸ (mem_outN.mp (mem_inter.mp mem).2).2)
  exact mem_sdiff.mpr ⟨vz,by simp [a,b]⟩

/-- Every affordable cut leaves a return on at least one of the actually
chosen shortcuts. The bank membership and return refer to the same row. -/
theorem chosen_return {D V q s p h} (free : QFree D V q) (hq : 3≤q) (reg : OutEq s D V)
    (hs : 2≤s) (pv : p∈V) (hv : h∈V) (ph : p≠h) (bank : Eligible V {p,h} q (s-1))
    (none : NoHost q (s-1)) (f : ℕ → ℕ)
    (choose : ∀ u∈jointParents D V p h, f u∈heads D V p h ∧ D u (f u)≠true)
    {C : ℕ → Finset ℕ} (budget : ∀ y∈V \ {p,h}, (C y).card≤spare D (V \ {p,h}) (s-1) y) :
    ∃ u∈jointParents D V p h,Walk (cut D C) (V \ {p,h}) (f u) u (q-1) := by
  classical
  let U := V \ {p,h}
  let S := jointParents D V p h
  have sh := short_rows_eq_jointParents free (by omega) reg pv hv ph hs
  have kin (u) (uu : u∈U) (low : (outN D U u).card<s-1) : u∈S := by
    change u∈jointParents D V p h
    rw [←sh]
    exact mem_filter.mpr ⟨uu,low⟩
  obtain ⟨u,uu,low,few⟩ := common_parent_row free (by omega) none bank pv
    (fun u uu low => (parent_data (kin u uu low)).2.1) budget
  have us := kin u uu low
  have base := parent_data us
  have row : (outN D U u).card+2=s := by
    have both : ({p,h} : Finset ℕ)⊆outN D V u := insert_subset (mem_outN.mpr ⟨pv,base.2.1⟩)
      (singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,base.2.2⟩))
    have eq : outN D U u=outN D V u \ {p,h} := by ext z; simp only [U,mem_outN,mem_sdiff]; tauto
    rw [eq,←card_pair ph,card_sdiff_add_card_eq_card both,reg u base.1]
  refine ⟨u,us,?_⟩
  by_contra no
  have z := choose u us
  have hit : f u∈clear D (cut D C) U q p u := mem_filter.mpr
    ⟨common_head_retained free (by omega) pv hv z.1,(mem_outN.mp (mem_inter.mp z.1).1).2,z.2,no⟩
  have positive := card_pos.mpr ⟨f u,hit⟩
  change (clear D (cut D C) U q p u).card+(outN D U u).card<s-1 at few
  omega

#print axioms select_bank
#print axioms no_back
#print axioms chosen_return
end LeanCH.BR.CommonHeadLastCut

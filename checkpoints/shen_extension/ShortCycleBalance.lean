import checkpoints.shen_extension.EqualShellRows
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace LeanCH.BR.ShortCycleBalance
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply ConsecutiveShellBanks

/-- Count distinct physical supports once, with an independent charge for
ordered pairs of source vertices using the same support. -/
theorem count {D V q r c} {S T : Finset ℕ} (free : QFree D V q) (cut : c+2≤q)
    (reg : OutEq r D V) (sv : S⊆V) (tv : T⊆V)
    (rows : ∀u∈S, ∀x∈outN D V u, Rooted D V x (outN D V u) ∧ x∈T)
    (width : ∀u∈S,(N2 D V u).card≤r-1+c) :
    ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*r≤T.card*((c+1)*2^c) ∧
      2*(S.card-g)≤(DotClonePairCompletion.orderedIncomparable D V q).card := by
  classical
  let F := S.image (outN D V)
  let rel := fun (C : Finset ℕ) (x : ℕ)=> x∈C
  have frows C (cm : C∈F) : C⊆T ∧ C.card=r := by
    obtain ⟨u,um,rfl⟩ := mem_image.mp cm
    exact ⟨fun a am=>(rows u um a am).2,reg u (sv um)⟩
  have left C (cm : C∈F) : r≤(T.bipartiteAbove rel C).card := by
    rw [←(frows C cm).2]
    exact card_le_card (fun a am=>(mem_bipartiteAbove _).mpr ⟨(frows C cm).1 am,am⟩)
  have right x (xm : x∈T) : (F.bipartiteBelow rel x).card≤(c+1)*2^c := by
    apply CycleRowMultiplicity.physical_multiplicity free cut (d:=r)
    · intro C cm
      obtain ⟨inF,xc⟩ := (mem_bipartiteBelow _).mp cm
      obtain ⟨u,us,rfl⟩ := mem_image.mp inF
      exact (rows u us x xc).1
    · exact reg x (tv xm)
    · intro C cm y yc
      obtain ⟨u,us,rfl⟩ := mem_image.mp ((mem_bipartiteBelow _).mp cm).1
      exact reg y (outN_subset yc)
    · intro C cm
      obtain ⟨u,us,rfl⟩ := mem_image.mp ((mem_bipartiteBelow _).mp cm).1
      rw [head_exterior free (by omega) (sv us)]
      exact width u us
  have bound : F.card*r≤T.card*((c+1)*2^c) := by
    have lo := sum_le_sum left
    have hi := sum_le_sum right
    have eq := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=F) (t:=T) rel
    rw [sum_const_nat (fun _ _=>rfl)] at lo hi
    exact lo.trans (eq.le.trans hi)
  obtain ⟨g,gs,gp,size,miss⟩ := SharedBankLedger.witness_budget (T:=F)
    (fun u=>{outN D V u}) (d:=1) (fun _ _=>by simp)
    (fun u us=>singleton_subset_iff.mpr (mem_image_of_mem _ us))
    (M:=DotClonePairCompletion.orderedIncomparable D V q) (by
      intro u us v vs ne C cu cv
      have same := (mem_singleton.mp cu).symm.trans (mem_singleton.mp cv)
      have eq := (head_exterior free (by omega) (sv us)).symm.trans
        ((congrArg (exterior D V) same).trans (head_exterior free (by omega) (sv vs)))
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨sv us,sv vs,ne⟩,
        SecondShellClasses.missed free (by omega) (sv us) (sv vs) ne eq.subset
          ((reg u (sv us)).trans (reg v (sv vs)).symm).le,
        SecondShellClasses.missed free (by omega) (sv vs) (sv us) ne.symm eq.symm.subset
          ((reg v (sv vs)).trans (reg u (sv us)).symm).le⟩)
  exact ⟨g,gs,gp,(Nat.mul_le_mul_right r (by simpa using size)).trans bound,miss⟩

/-- A low row owes one slot. A high row owns one extra slot. Distinct
cycle supports cost more rows than their maximum shared multiplicity. -/
theorem positive_balance {V S T : Finset ℕ} {score : ℕ→ℕ} {base missed r m : ℕ}
    (sv : S⊆V) (tv : T⊆V) (apart : Disjoint S T)
    (short : ∀x∈S,base≤score x+1) (ordinary : ∀x∈V\S,base≤score x)
    (high : ∀x∈T,base+1≤score x) (cap : missed+(∑x∈V,score x)≤V.card*base)
    (supply : ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*r≤T.card*m ∧ 2*(S.card-g)≤missed)
    (gain : m<r) : S=∅ := by
  by_contra ne
  obtain ⟨g,gs,pos,rows,holes⟩ := supply
  have gp := pos (nonempty_iff_ne_empty.mpr ne)
  have gt : g<T.card := by
    by_contra! contrary
    exact (Nat.not_lt_of_ge (rows.trans (Nat.mul_le_mul_right m contrary)))
      (Nat.mul_lt_mul_of_pos_left gain gp)
  have off : T⊆V\S := fun x xm=>mem_sdiff.mpr ⟨tv xm,fun xs=>disjoint_left.mp apart xs xm⟩
  have paidS := sum_le_sum short
  have paidT := RetainedRadiusLayers.add_layer (f:=fun _=>base) (g:=score) off ordinary high
  rw [sum_const_nat (fun _ _=>rfl),sum_add_distrib,sum_const_nat (fun _ _=>rfl)] at paidS
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset sv] at paidT
  have merge := sum_sdiff sv (f:=score)
  have split : (V.card-S.card)*base+S.card*base=V.card*base := by
    rw [←Nat.add_mul,Nat.sub_add_cancel (card_le_card sv)]
  omega

attribute [aesop safe forward (immediate := [free,cut,reg,sv,tv,rows,width])
  (rule_sets := [CHGraphFamilies])] count
attribute [aesop safe forward (immediate := [sv,tv,apart,short,ordinary,high,cap,supply,gain])
  (rule_sets := [CHGraphFamilies])] positive_balance
#print axioms count
#print axioms positive_balance
end LeanCH.BR.ShortCycleBalance

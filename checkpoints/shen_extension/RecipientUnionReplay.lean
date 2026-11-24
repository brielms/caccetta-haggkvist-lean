import checkpoints.shen_extension.RecipientUnionAudit
import checkpoints.shen_extension.CHForwardCatalog
namespace LeanCH.BR.RecipientUnionAudit
open Finset BRq2 BRq3

/-- The returning tails in L cost nothing beyond the already selected
recipients in R. Use the union of actual missed head labels in the bill. -/
theorem paid_omissions {D : CH.Digraph} {V X Y S R L : Finset ℕ} {q s : ℕ}
    (free : QFree D V q) (time : 2≤q) (xv : X⊆V) (yv : Y⊆V)
    (lv : L⊆V) (charged : L⊆R) (omitted : ℕ→ℕ)
    (row : ∀t∈S,outN D V t=Y.erase (omitted t))
    (acyclic : QFree D (Y.erase (omitted s)) (Y.erase (omitted s)).card)
    (need : ∀b∈Y.erase (omitted s),(∀z∈Y.erase (omitted s),D b z≠true) → ∃v∈X,D b v=true)
    (bank : ∀v∈X,v∉R → ∃t∈S,∃k,k+3≤q ∧ Walk D X v t k)
    (early : ∀v∈X,v∉L → ∃t∈S,∃k,k+2≤q ∧ Walk D X v t k)
    (small : ∀v∈R,(Y\outN D V v).card<q-1) :
    Y.erase (omitted s) ⊆ R.biUnion (fun v=>Y\outN D V v) ∪ (S.erase s).image omitted := by
  have all := cover_from_depths free time xv yv omitted row acyclic need bank early small
  have paid := late_tails_in_recipient_union free time yv (erase_subset (omitted s) Y) lv charged
  intro a am
  rcases mem_union.mp (all am) with old|other
  · exact mem_union_left _ old
  rcases mem_union.mp other with o|l
  · exact mem_union_right _ o
  · exact mem_union_left _ (paid l)

theorem exit {A : Finset ℕ} {R S : Finset ℕ} {s : ℕ} {loss : ℕ→Finset ℕ} {omitted : ℕ→ℕ}
    (paid : A ⊆ R.biUnion loss ∪ (S.erase s).image omitted)
    (tooFew : (R.biUnion loss).card+((S.erase s).image omitted).card<A.card) : False :=
  tooFew.not_ge ((card_le_card paid).trans (card_union_le _ _))

attribute [aesop safe forward (immediate := [free,time,xv,yv,lv,charged,row,acyclic,need,bank,early,small]) (rule_sets := [CHGraphFamilies])] paid_omissions
attribute [aesop safe forward (immediate := [paid,tooFew]) (rule_sets := [CHGraphFamilies])] exit
#print axioms paid_omissions
#print axioms exit
end LeanCH.BR.RecipientUnionAudit

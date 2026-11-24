import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.CHRuleCatalog
import checkpoints.shen_extension.CHFamilyWorklist

namespace LeanCH.BR.BankExitRanks
open Finset BRq2 BRq3 CHRuleCatalog

/-- After reserving some rows, an acyclic nonempty remainder has a sink.
Every head of that row still inside the bank must use a reserved label. -/
theorem after_reserving {D : CH.Digraph} {V U A : Finset ℕ} {r : ℕ}
    (live : (U\A).Nonempty) (acyclic : QFree D (U\A) (U\A).card)
    (rank : ∀v∈U,r≤(outN D V v).card) :
    ∃x∈U\A, outN D U x⊆A ∧ r-A.card≤(outN D V x\U).card := by
  obtain ⟨x,xm,stop⟩ := exists_sink acyclic live le_rfl
  have inside : outN D U x ⊆ A := by
    intro y ym
    by_contra off
    exact stop y (mem_sdiff.mpr ⟨outN_subset ym,off⟩) (mem_outN.mp ym).2
  have cap := card_le_card (show (outN D V x)∩U⊆A from
    fun y ym=>inside (mem_outN.mpr ⟨(mem_inter.mp ym).2,(mem_outN.mp (mem_inter.mp ym).1).2⟩))
  have total := card_sdiff_add_card_inter (outN D V x) U
  have lo := rank x (mem_sdiff.mp xm).1
  exact ⟨x,xm,inside,by omega⟩

/-- Among the rows of U there are at least j+1 with fewer than t+j
heads still in U. A rival set of just j rows can be removed; on the
remaining labels the lower-quota hypothesis supplies another such row. -/
theorem short_rows {D : CH.Digraph} {V U : Finset ℕ} {q t j : ℕ}
    (lower : BypassRepair.NoHost q t) (free : QFree D V q) (sub : U⊆V)
    (live : j<U.card) (room : U.card≤q*t+j) :
    j+1≤(U.filter (fun x=>(outN D U x).card<t+j)).card := by
  classical
  let P := U.filter (fun x=>(outN D U x).card<t+j)
  by_contra! few
  change P.card<j+1 at few
  obtain ⟨A,pa,au,ac⟩ := exists_subsuperset_card_eq (filter_subset _ _ : P⊆U)
    (by omega : P.card≤j) live.le
  have size := card_sdiff_add_card_eq_card au
  obtain ⟨x,xm,short⟩ := ReachLedger.fragment_row lower free (sdiff_subset.trans sub : U\A⊆V)
    (card_pos.mp (show 0<(U\A).card by omega)) (by omega)
  have split : outN D U x⊆outN D (U\A) x∪A := by
    intro y ym
    by_cases ya : y∈A
    · exact mem_union_right _ ya
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset ym,ya⟩,(mem_outN.mp ym).2⟩)
  have bound := (card_le_card split).trans (card_union_le _ _)
  exact (mem_sdiff.mp xm).2 (pa (mem_filter.mpr ⟨(mem_sdiff.mp xm).1,by omega⟩))

/-- These very short rows have many distinct exterior heads. The count
uses the original arcs from each witness into the complement of U. -/
theorem quota_rows {D : CH.Digraph} {V U : Finset ℕ} {q r t j : ℕ}
    (lower : BypassRepair.NoHost q t) (free : QFree D V q) (sub : U⊆V)
    (rank : ∀v∈U,r≤(outN D V v).card) (live : j<U.card) (room : U.card≤q*t+j) :
    j+1≤(U.filter (fun x=>r+1≤(outN D V x\U).card+t+j)).card := by
  apply (short_rows lower free sub live room).trans (card_le_card ?_)
  intro x xm
  obtain ⟨xu,short⟩ := mem_filter.mp xm
  have matchRows : (outN D V x)∩U=outN D U x := by
    ext y
    simp only [mem_inter,mem_outN]
    exact ⟨fun h=>⟨h.2,h.1.2⟩,fun h=>⟨⟨sub h.1,h.2⟩,h.1⟩⟩
  have count := card_sdiff_add_card_inter (outN D V x) U
  rw [matchRows] at count
  have deg := rank x xu
  exact mem_filter.mpr ⟨xu,by omega⟩

/-- Pick the rows and the exterior head labels that a subsequent rule
asks for. Head sets from different rows may overlap. -/
theorem labelled_exits {D : CH.Digraph} {V U : Finset ℕ} {q r t j d : ℕ}
    (lower : BypassRepair.NoHost q t) (free : QFree D V q) (sub : U⊆V)
    (rank : ∀v∈U,r≤(outN D V v).card) (live : j<U.card) (room : U.card≤q*t+j)
    (need : d+t+j≤r+1) :
    ∃P⊆U,P.card=j+1 ∧ ∀x∈P,∃H⊆outN D V x\U,H.card=d := by
  obtain ⟨P,selected,count⟩ := exists_subset_card_eq (quota_rows lower free sub rank live room)
  refine ⟨P,selected.trans (filter_subset _ _),count,?_⟩
  intro x xm
  have enough := (mem_filter.mp (selected xm)).2
  exact exists_subset_card_eq (show d≤(outN D V x\U).card by omega)

/-- Quota one is unconditional for every cutoff. -/
theorem many_rows {D : CH.Digraph} {V U : Finset ℕ} {q r j : ℕ}
    (free : QFree D V q) (sub : U⊆V) (rank : ∀v∈U,r≤(outN D V v).card)
    (live : j<U.card) (room : U.card≤q+j) :
    j+1≤(U.filter (fun x=>r-j≤(outN D V x\U).card)).card := by
  have rows := quota_rows (t:=1) ReachLedger.noHost_one free sub rank live (by simpa using room)
  apply rows.trans (card_le_card ?_)
  intro x xm
  obtain ⟨xu,heads⟩ := mem_filter.mp xm
  exact mem_filter.mpr ⟨xu,by omega⟩

/-- The whole row distribution is available on every marked subcarrier
and every quota at which the original graph is known to be free. -/
def Laws (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop :=
  ∀U⊆V,∀ r j, (∀v∈U,r≤(outN D V v).card) → j<U.card → U.card≤q+j →
    j+1≤(U.filter (fun x=>r-j≤(outN D V x\U).card)).card

theorem from_free {D V q} (free : QFree D V q) : Laws D V q :=
  fun _ sub _ _ rank live room=>many_rows free sub rank live room

theorem from_bad {p : Input} (bad : Bad p) : Laws p.D (range p.n) (cutoff p) :=
  from_free (qfree_of_noShort bad.loopless bad.missing)

def AtQuota (D : CH.Digraph) (V : Finset ℕ) (q t : ℕ) : Prop :=
  ∀U⊆V,∀ r j, (∀v∈U,r≤(outN D V v).card) → j<U.card → U.card≤q*t+j →
    j+1≤(U.filter (fun x=>r+1≤(outN D V x\U).card+t+j)).card

theorem at_quota {D V q t} (lower : BypassRepair.NoHost q t) (free : QFree D V q) :
    AtQuota D V q t := fun _ sub _ _ rank live room=>quota_rows lower free sub rank live room

attribute [aesop safe forward (immediate := [lower,free,sub,rank,live,room,need]) (rule_sets := [CHGraphFamilies])] labelled_exits
attribute [aesop safe forward (immediate := [free,lower]) (rule_sets := [CHGraphFamilies])] at_quota
attribute [aesop safe forward (immediate := [lower,free,sub,live,room]) (rule_sets := [CHGraphFamilies])] short_rows
attribute [aesop safe forward (immediate := [lower,free,sub,rank,live,room]) (rule_sets := [CHGraphFamilies])] quota_rows
attribute [aesop safe forward (immediate := [live,acyclic,rank]) (rule_sets := [CHGraphFamilies])] after_reserving
attribute [aesop safe forward (immediate := [free,sub,rank,live,room]) (rule_sets := [CHGraphFamilies])] many_rows
attribute [aesop safe forward (immediate := [free]) (rule_sets := [CHGraphFamilies])] from_free
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] from_bad
#print axioms after_reserving
#print axioms labelled_exits
#print axioms at_quota
#print axioms many_rows
#print axioms from_bad
end LeanCH.BR.BankExitRanks


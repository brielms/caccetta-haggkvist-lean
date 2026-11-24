import checkpoints.shen_extension.LabelledCompromiseRecipe

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog CompromiseQuotaTransfer AvoidedHeadQuota

/-- Numerical data are inferred from a verified supplier. The receiver,
its head, the missed column and the return to its head bank are labelled. -/
def Receiver {V : Type} [Fintype V] [DecidableEq V] (A : V→V→Prop) [DecidableRel A]
    (d i s cap miss lo hi : ℕ) : Prop :=
  ∃y, (CH.CompromiseSeven.inN A y).card=i ∧ (CH.CompromiseSeven.second A y).card=s ∧
    (∑h∈CH.CompromiseSeven.outN A y, (d-(CH.CompromiseSeven.inN A h).card))≤cap ∧
    lo≤((CH.CompromiseSeven.second A y).filter fun z=>miss≤(CH.CompromiseSeven.outN A y \ CH.CompromiseSeven.inN A z).card).card ∧
    ((CH.CompromiseSeven.second A y).filter fun z=>miss≤(CH.CompromiseSeven.outN A y \ CH.CompromiseSeven.inN A z).card).card≤hi ∧
    ∃h∈CH.CompromiseSeven.outN A y, d≤(CH.CompromiseSeven.inN A h).card ∧ ∃z∈CH.CompromiseSeven.second A y,
      A h z ∧ miss≤(CH.CompromiseSeven.outN A y \ CH.CompromiseSeven.inN A z).card ∧ ∃a∈CH.CompromiseSeven.outN A y,A z a

structure ReceiverLaw where
  degree : ℕ
  scoreCap : ℕ
  parents : ℕ
  shell : ℕ
  charge : ℕ
  missing : ℕ
  lowerCount : ℕ
  upperCount : ℕ
  supply : ∀{V : Type} [Fintype V] [DecidableEq V] (A : V→V→Prop) [DecidableRel A],
    Recipe A degree scoreCap (Receiver A degree parents shell charge missing lowerCount upperCount)

def from_receiver {d b i s c k l h} (f : ∀{V : Type} [Fintype V] [DecidableEq V] (A : V→V→Prop) [DecidableRel A],
    Recipe A d b (Receiver A d i s c k l h)) : ReceiverLaw := ⟨d,b,i,s,c,k,l,h,f⟩

-- The only inhabitant comes from the degree-ten theorem. The rules that consume a receiver use
-- its shell size and its count of heavily missed columns. ShellExcessFork states the same fork
-- at any root with d = q t + 1 and no receiver.
def currentReceiver := from_receiver (@CH.CompromiseTenTwoException.residual_root_from_induction)

def ReceiverLaw.on (law : ReceiverLaw) (D : CH.Digraph) (U : Finset ℕ) :=
  Receiver (adjacency D U) law.degree law.parents law.shell law.charge law.missing law.lowerCount law.upperCount

theorem receiver_at {D U q} (law : ReceiverLaw) (free : QFree D U q) (live : U.Nonempty)
    (cut : 3≤q) (reg : OutEq law.degree D U) (lower : ∀k,0<k → k<law.degree → NoHost q k)
    (room : U.card≤law.degree+law.scoreCap+1) : law.on D U :=
  run (law.supply (adjacency D U)) free live cut reg lower room

/-- Keep the exact subgraph on the original vertex labels. Later rules
may distinguish its arcs from the larger input graph's additional arcs. -/
structure ReceiverOn (p : Input) (law : ReceiverLaw) : Prop where
  witness : ∃E : CH.Digraph, (∀x y,E x y=true → p.D x y=true) ∧ QFree E (range p.n) (cutoff p) ∧
    OutEq law.degree E (range p.n) ∧ law.on E (range p.n)

theorem source_receiver {p : Input} (bad : Bad p) (law : ReceiverLaw)
    (quota : law.degree≤p.s) (funded : law.degree≤spendingFloor (cutoff p))
    (room : p.n≤law.degree+law.scoreCap+1) : ReceiverOn p law := by
  have lower := available bad
  obtain ⟨E,sub,reg⟩ := exists_outEq (G:=p.D) (s:=law.degree) (fun x (xm : x∈range p.n)=>
    quota.trans (Compose.FloorSix.out_card bad.degree (mem_range.mp xm)))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨E,sub,free,reg,receiver_at law free (nonempty_range_iff.mpr bad.order.ne')
    (remaining_from_run p bad).1 reg (fun k _ hk=>lower k (hk.trans_le funded)) (by simpa using room)⟩

attribute [aesop safe forward (immediate := [law,free,live,cut,reg,lower,room])
  (rule_sets := [CHGraphFamilies])] receiver_at
attribute [aesop safe forward (immediate := [bad,law,quota,funded,room])
  (rule_sets := [CHGraphFamilies])] source_receiver
attribute [aesop safe forward (immediate := [self]) (rule_sets := [CHGraphFamilies])] ReceiverOn.witness
ch_family_split_result ReceiverOn.witness
#print axioms currentReceiver
#print axioms receiver_at
#print axioms source_receiver
end LeanCH.BR.LabelledCompromiseRecipe

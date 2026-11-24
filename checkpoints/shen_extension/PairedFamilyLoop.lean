import checkpoints.shen_extension.EqualizerTransfer

namespace LeanCH.BR.Closure.PairedFamilyLoop
open Finset Function BRq2 BRq3 BR45 WeightedSD MarkedCyclePeeling CycleSlotOrbit

def pairs (F : Family) := (F ×ˢ F).filter (fun e => e.1 ≠ e.2)
abbrev State (F : Family) := ↥(pairs F)
def previous {F} (s : State F) := s.val.1
def current {F} (s : State F) := s.val.2

def Admissible (F : Family) (E : CH.Digraph)
    (law : (s t : State F) → (↥(previous s) ≃ ↥(previous t)) → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ s : State F, ∃ t : State F, previous t=current s ∧
    ∃ e : ↥(previous s) ≃ ↥(previous t), ∃ b : ℕ, ∃ r : ↥(previous s),
      E b r=false ∧ E b (e r)=true ∧ law s t e b (e r) r

/-- The integer transfer certificate can be retained in law, while the
permutation tracks each occurrence of its labels. A compensating switch
is on the same orbit, at a genuine transition of the selected schedule. -/
theorem schedule {F E law} (moves : Admissible F E law) (seed : State F) :
    ∃ (go : State F → State F) (send : ∀s, ↥(previous s) ≃ ↥(previous (go s))),
    (∀s,previous (go s)=current s ∧ ∃ b,∃ r : ↥(previous s),
      E b r=false ∧ E b (send s r)=true ∧ law s (go s) (send s) b (send s r) r) ∧
    ∃ t,∃ periodic : go^[t] seed ∈ periodicPts go,
    ∃ s : Slot go previous, s.1=⟨go^[t] seed,periodic⟩ ∧ ∃ b,
      let step := lift go previous send
      let label := fun z : Slot go previous => (z.2 : ℕ)
      law s.1.val (go s.1.val) (send s.1.val) b (label (step s)) (label s) ∧
      E b (label s)=false ∧ E b (label (step s))=true ∧
      ∃ k,0<k ∧ k<minimalPeriod step s ∧ E b (label (step^[k] s))=true ∧
        E b (label (step^[k+1] s))=false := by
  classical
  choose go joins send b r misses hits legal using moves
  refine ⟨go,send,fun s => ⟨joins s,b s,r s,misses s,hits s,legal s⟩,?_⟩
  obtain ⟨t,recurs⟩ := recurrent go seed
  let a := go^[t] seed
  let s : Slot go previous := ⟨⟨a,recurs⟩,r a⟩
  let step := lift go previous send
  let label := fun z : Slot go previous => (z.2 : ℕ)
  have first : E (b a) (label s)=false := misses a
  have second : E (b a) (label (step s))=true := hits a
  have : Finite (Slot go previous) := by dsimp [Slot]; infer_instance
  obtain ⟨k,positive,within,seen,miss⟩ := switch step (fun z => !(E (b a) (label z)))
    (by simp [first] : !(E (b a) (label s))=true) (by simp [second])
  refine ⟨t,recurs,s,rfl,b a,legal a,first,second,k,positive,within,?_,?_⟩
  · simpa using seen
  · simpa using miss

/-- Each positive-to-negative switch is a failed single-vertex repair by
that same surviving row at the normalized outgoing equalizer. -/
theorem fails {q E V x c b y r} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0≤x i)
    (high : mass V x<c) (rows : ∀i∈V,WeightedSD.row q E V x i=c) (bv : b∈V)
    (yv : y∈V) (rv : r∈V) (byArc : E b y=true) (miss : E b r=false) :
    b∈V.erase y ∧ WeightedSD.row q E (V.erase y) (transferWeight x y r) b <
      mass (V.erase y) (transferWeight x y r) := by
  have br : b≠y := by rintro rfl; exact loopfree free (by omega) bv byArc
  have yr : y≠r := by rintro rfl; simp_all
  have kept := mem_erase.mpr ⟨br,bv⟩
  exact ⟨kept,(EqualizerTransfer.classify hq free small pos high rows yv rv yr kept).1.mpr ⟨byArc,miss⟩⟩

#print axioms schedule
#print axioms fails
end LeanCH.BR.Closure.PairedFamilyLoop

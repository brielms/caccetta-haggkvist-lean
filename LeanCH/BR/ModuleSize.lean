import LeanCH.BR.Compose.Boundary

/-!
# Lemma A (module size), Lean 4.35.0

If every vertex of a set `M` keeps at least `c ≥ 1` out-neighbours inside `M`, the graph has no cycle of length
`≤ q`, and boundary regularity holds at `(q, c)`, then `|M| ≥ q c + 1`.

Applied to a module `M` of a boundary graph for `(q, s)` whose outside out-neighbourhood has weight `W < s`
(take `c = s - W`), this is the slack inequality `q s + 1 ≤ q W + |M|` used by `CircSubst.uniform`.
-/

namespace LeanCH.BR.ModuleSize

open CH Compose.Boundary

theorem module_size {G : CH.Digraph} {n q c : Nat} {M : Finset Nat}
    (hc : 0 < c) (br : BoundaryRegular q c) (hsub : M ⊆ Finset.range n) (hne : 0 < M.card)
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n q)
    (keep : ∀ x ∈ M, c ≤ (M.filter (fun w => G x w = true)).card) :
    q * c + 1 ≤ M.card := by
  classical
  by_contra hsmall
  apply noShort
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hsub
  set m := M.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    show (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    rw [if_pos hv, if_pos hv]; exact loopless (e v) (eB v hv)
  have hmin : CH.MinOutdegreeAtLeast H m c := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = M.filter (fun w => G (e a) w = true) := by
      ext w
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩; exact ⟨eM i hi, hG⟩
      · rintro ⟨hwM, hG⟩; obtain ⟨i, hi, rfl⟩ := eS w hwM; exact ⟨i, ⟨hi, hG⟩, rfl⟩
    have hinj : Set.InjOn e T := by
      intro i hi j hj hij
      simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
      exact eI i j hi.1 hj.1 hij
    have hTcard : c ≤ T.card := by
      have := Finset.card_image_of_injOn hinj
      rw [himage] at this; rw [← this]; exact keep (e a) (eM a ha)
    refine ⟨(T.sort (· ≤ ·)).take c, ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ T := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      simp only [T, Finset.mem_filter, Finset.mem_range] at hwT
      refine ⟨hwT.1, ?_⟩
      show (if a < m then (if w < m then G (e a) (e w) else false) else false) = true
      rw [if_pos ha, if_pos hwT.1]; exact hwT.2
  exact CH.Side.sc_induced_subgraph_transport eB eI
    (ch_of_boundaryRegular hc br hne (by omega) hloop hmin)

end LeanCH.BR.ModuleSize

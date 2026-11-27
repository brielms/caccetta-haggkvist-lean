"""Index the exact open contexts of a finished local Capstone.lean replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


def replay_events(lines):
    events = []
    event_pattern = re.compile(r"^(CH-INSTANCE|CH-FORWARD|CH-FAMILY OPEN|CH-FAMILY ROUND|CH-NUMERIC) (\S+) (.*)")
    for i, line in enumerate(lines):
        match = event_pattern.match(line)
        if not match:
            continue
        kind, tag, detail = match.groups()
        tail = i + 1
        while tail < len(lines) and lines[tail].startswith(" "):
            tail += 1
        events.append({"kind": kind, "case": tag.split("._@.")[0], "line": i + 1,
                       "detail": "\n".join([detail, *lines[i + 1:tail]])})
    return events


def published_bounds(lines, leaf):
    """Recover the capstone's named numerical frontier from a saved goal, including old replays."""
    names = set("""
        hn hs cutoffReduction hNoOneLossChild q hcover hq hq1 hq2 hq3
        hbankLaw h24 htriangleOrder htri htriangleResidual hsmall hCertifiedPrefix
        hdegreeSix degreeFrontier hbelowWindow hnextStrip hdeeper hfourthLow hfourth
        hbelowFourth hfifthClosed hremainingCutoff hsixthClosed hsixthRemaining
        gap hgap hgapPos hremainingScale hceilSlack hremainingGap hremainingPaid
        hfifthRemaining hfifthHigherRemaining hfifthTensorRemaining
        hInputAtLeastEight hAboveDegreeSeven hDegreeSevenGone hEightOrder hTightCoverBudget
        hNo38DegreeNine hReducedOrder hReducedParity hOneLossOrder
    """.split())
    projected = ("GuardedDegreeFrontier.Direct", "GuardedDegreeFrontier.Terminal",
                 "GuardedFamilyRules.Fits", "GuardedProfileBudget.Window", "InheritedProfileWindow.Fits", "OneSpareGrowth.BelowFour",
                 "OneSpareGrowth.Window", "ParentCutFrontier.Gate",
                 "ProjectedQuotaTransfer.from_recorded_projection", "SymbolicQuotaSweep.Covers")
    selected_bank_bounds = {
        "2 ^ (q - 1) < s",
        "q * (s - 1) + 3 ≤ n",
        "2 ^ (2 ^ (q / 2) + 1) ≤ q * (s - 1) + 3",
        "(2 ^ (q / 2) + 2) * 2 ^ (2 ^ (q / 2) - 1) ≤ q * (s - 1) + 3",
    }
    bounds = []
    def take(name, parts):
        statement = " ".join(" ".join(parts).split())
        if name in names:
            bounds.append(name + " : " + statement)
        elif name.startswith("fwd") and (
            statement in selected_bank_bounds or any(p in statement for p in projected)
        ):
            bounds.append(statement)
    name, parts = "", []
    for line in lines[leaf["context_line"]:leaf["goal_line"] - 1]:
        if line.startswith(" "):
            parts.append(line)
        else:
            take(name, parts)
            name, _, first = line.partition(" :")
            parts = [first]
    take(name, parts)
    return sorted(set(bounds))


def leaf_facts(lines, leaf, *, strip_hygiene=True):
    """Statements of one saved context, without local names, name suffixes or replay bookkeeping."""
    facts, parts = set(), None
    def take(parts):
        if parts is None:
            return
        statement = " ".join(" ".join(parts).split())
        if strip_hygiene:
            statement = re.sub(r"✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*", "", statement)
        if statement and not re.search(r"CHFamilyWorklist\.Opened|CHContextCatalog\.Fired", statement):
            facts.add(statement)
    for line in lines[leaf["context_line"]:leaf["goal_line"] - 1]:
        if line.startswith(" "):
            if parts is not None:
                parts.append(line)
        else:
            take(parts)
            _, colon, first = line.partition(" :")
            parts = [first] if colon else None
    take(parts)
    return facts


def native_bank_refinements(lines, leaf):
    """Track refinements of the surviving input and its native source."""
    local_inputs = ("input", "{ n := n, s := s, D := D }")
    degree = {"10 ≤ s"} | {f"10 ≤ {input_term}.s" for input_term in local_inputs}
    deletion = {
        f"¬BankRefinementReplay.DeletionWindow {input_term}.n {input_term}.s "
        f"(CHRuleCatalog.cutoff {input_term})"
        for input_term in local_inputs
    }
    guards = {
        f"BankRefinementReplay.AtTriangle q (BankRefinementReplay.{kind}TriangleBank source)"
        for kind in ("Shared", "Missed")
    }
    return sorted(leaf_facts(lines, leaf) & (degree | deletion | guards))


def common_head_refinements(lines, leaf):
    """Index witnesses whose pair, assignment and tree root agree on this leaf."""
    facts = {
        re.sub(r"(?:LeanCH\.BR\.)?CommonHead(?:CutReplay|CutDepth|LastCut|TwoLayerCut)\.", "", fact)
        .replace("BypassBankReplay.jointParents", "jointParents")
        for fact in leaf_facts(lines, leaf, strip_hygiene=False)
    }
    def holds_card(prefix, expression, suffix=""):
        return (f"{prefix}({expression}).card{suffix}" in facts
                or f"{prefix}#({expression}){suffix}" in facts)

    candidates = [[]]
    sources = [fact.removeprefix("CommonBank ") for fact in facts if fact.startswith("CommonBank ")]
    for source in sources:
        native = ["native CommonBank"]
        candidates.append(native)
        graph, vertices = f"{source}.D", f"{source}.V"
        law_prefix = f"ForkLaw {graph} {vertices} "
        for law in facts:
            if not law.startswith(law_prefix):
                continue
            labels = law.removeprefix(law_prefix).split()
            if len(labels) != 4:
                continue
            q, s, p, h = labels
            matching_law = [*native, "native ForkLaw"]
            candidates.append(matching_law)
            assignment_prefix = f"Assignment {graph} {vertices} {p} {h} "
            bank = rf"({vertices} \ {{{p}, {h}}})"
            parents = f"(jointParents {graph} {vertices} {p} {h})"
            for assignment in facts:
                if not assignment.startswith(assignment_prefix):
                    continue
                f = assignment.removeprefix(assignment_prefix)
                matching = {*matching_law, "matching Assignment"}
                routes = f"(routes {graph} {bank} {parents} {q} {f})"
                tree = f"{routes} {bank} {parents} ({q} - 1)"
                prefix = f"Branches {tree} ({f} "
                for branches in facts:
                    if not branches.startswith(prefix) or not branches.endswith(")"):
                        continue
                    u = branches.removeprefix(prefix)[:-1]
                    if f"{u} ∈ {parents[1:-1]}" not in facts:
                        continue
                    matching.add("matching Branches rooted at an assigned head")
                    if holds_card(f"2 ^ ({q} - 1) ≤ ", f"words {tree} ({f} {u})"):
                        matching.add("matching word bound at depth q - 1")
                retained_suffix = f" ∈ {bank[1:-1]}"
                for member in facts:
                    if member.endswith(retained_suffix):
                        b = member.removesuffix(retained_suffix)
                        if (holds_card("2 ≤ ", f"previousBill {graph} {bank} {parents} {q} {f} {b}")
                                and holds_card("", f"outN {graph} {bank} {b}", f" = {s}")):
                            matching.add("matching full-row fork to two contested payers")
                candidates.append(sorted(matching))
    return sorted(max(candidates, key=lambda candidate: (len(candidate), candidate)))


def cyclic_layer_refinements(lines, leaf):
    """Match the counted assignment and its cyclic row budget on the native source."""
    facts = leaf_facts(lines, leaf, strip_hygiene=False)
    prefix = "CyclicLayerReplay.CountedBank source.D source.V "
    candidates = [
        fact.removeprefix(prefix).split()
        for fact in facts if fact.startswith(prefix)
    ]
    if not candidates:
        return []
    if len(candidates) != 1 or len(candidates[0]) != 4:
        return ["nonunique native cyclic count"]
    q, p, h, f = candidates[0]
    if f"CommonHeadCutReplay.Assignment source.D source.V {p} {h} {f}" not in facts:
        return ["native cyclic count with unmatched assignment"]
    result = ["native cyclic count on matching bank and assignment"]
    rows = f"CyclicLayerReplay.Representatives source.D source.V {q} {p} "
    budget = f"CyclicLayerReplay.Budget source.D source.V {q} {p} "
    representatives = {
        fact.removeprefix(rows) for fact in facts if fact.startswith(rows)
    }
    budgets = {fact.removeprefix(budget) for fact in facts if fact.startswith(budget)}
    if len(representatives) == 1 and representatives == budgets:
        result.append("matching representatives and layer budget")
    return result


def common_core_refinements(lines, leaf):
    """Require both row bounds on the exact labels in the native ForkLaw."""
    facts = leaf_facts(lines, leaf, strip_hygiene=False)
    prefix = "CommonCoreReplay.RowCoreBound source.D source.V "
    bounds = {
        fact.removeprefix(prefix) for fact in facts
        if fact.startswith(prefix) and len(fact.removeprefix(prefix).split()) == 2
    }
    if not bounds:
        return []
    law = "CommonHeadCutReplay.ForkLaw source.D source.V "
    for fact in facts:
        if not fact.startswith(law):
            continue
        labels = fact.removeprefix(law).split()
        if len(labels) == 4:
            _, s, p, h = labels
            if p != h and bounds == {f"{s} {p}", f"{s} {h}"}:
                return ["row core bounds for both labels of the native ForkLaw"]
    return ["native row core bounds with unmatched labels"]


def independent_obligations(lines, leaves):
    """Factor the open contexts into splits that never interact.

    Two varying statements belong to one factor when the sets of contexts that
    hold them are not independent. If the contexts are exactly the product of
    the factors, each factor can be discharged on its own, and the number of
    separate obligations is the sum of the factor sizes."""
    if len(leaves) < 2:
        return None
    facts = [leaf_facts(lines, leaf) for leaf in leaves]
    total = len(leaves)
    support = {}
    for i, held in enumerate(facts):
        for fact in held:
            support.setdefault(fact, set()).add(i)
    by_support = {}
    for fact, where in support.items():
        if len(where) < total:
            by_support.setdefault(frozenset(where), []).append(fact)
    keys = list(by_support)
    parent = list(range(len(keys)))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for i, a in enumerate(keys):
        for j in range(i + 1, len(keys)):
            b = keys[j]
            if len(a & b) * total != len(a) * len(b):
                parent[find(i)] = find(j)
    groups = {}
    for i, key in enumerate(keys):
        groups.setdefault(find(i), []).append(key)
    factors, product = [], 1
    for members in groups.values():
        kinds = {}
        for i in range(total):
            kinds.setdefault(tuple(i in key for key in members), []).append(leaves[i]["case"])
        product *= len(kinds)
        examples = sorted((fact for key in members for fact in by_support[key]), key=len)[:6]
        factors.append({"kinds": len(kinds), "contexts_per_kind": sorted(len(v) for v in kinds.values()),
                        "varying_statements": sum(len(by_support[key]) for key in members),
                        "shortest_varying_statements": examples,
                        "one_context_per_kind": sorted(v[0] for v in kinds.values())})
    factors.sort(key=lambda f: -f["kinds"])
    exact = product == total and all(len(set(f["contexts_per_kind"])) == 1 for f in factors)
    return {"open_contexts": total, "factors": factors, "exact_product": exact,
            "separate_obligations": sum(f["kinds"] for f in factors) if exact else total}


def compare_frontiers(previous_path, leaves, lines):
    previous = json.loads(previous_path.read_text(encoding="utf-8-sig"))
    old_data = Path(previous["source_log"]).read_bytes()
    if hashlib.sha256(old_data).hexdigest() != previous["sha256"]:
        sys.exit("The previous frontier no longer matches its source log.")
    old_lines = old_data.decode("utf-8-sig").splitlines()
    old_events = replay_events(old_lines)
    new_events = replay_events(lines)
    comparison = []
    for old in previous["leaves"]:
        name = old["case"]
        def in_family(tag):
            return tag == name or tag.startswith(name + ".")
        survivors = [leaf["case"] for leaf in leaves if in_family(leaf["case"])]
        previous_facts = {e["detail"] for e in old_events if e["kind"] == "CH-FORWARD" and in_family(e["case"])}
        activity = [e for e in new_events if in_family(e["case"])]
        old_context = " ".join(" ".join(old_lines[old["context_line"]:old["goal_line"] - 1]).split())
        numbers = {}
        old_bounds = set(published_bounds(old_lines, old))
        for child in survivors:
            facts = [" ".join(e["detail"].split()) for e in activity
                     if e["kind"] == "CH-NUMERIC" and e["case"] == child]
            child_leaf = next(leaf for leaf in leaves if leaf["case"] == child)
            new_bounds = set(published_bounds(lines, child_leaf))
            numbers[child] = {"lean_numeric_facts": len(facts), "without_literal_baseline_match":
                              [fact for fact in facts if fact not in old_context],
                              "without_baseline_proposition":
                              [fact for fact in facts if fact.partition(" : ")[2] not in old_context],
                              "baseline_named_bounds": len(old_bounds), "current_named_bounds": len(new_bounds),
                              "removed_bounds": sorted(old_bounds - new_bounds), "added_bounds": sorted(new_bounds - old_bounds)}
        comparison.append({"previous_case": name, "open_descendants": survivors,
                           "numerical_context_check": numbers,
                           "opened_alternatives": [e for e in activity if e["kind"] == "CH-FAMILY OPEN"],
                           "named_applications": [e for e in activity if e["kind"] == "CH-INSTANCE"],
                           "additional_forward_facts": [e for e in activity if e["kind"] == "CH-FORWARD"
                                                        and e["detail"] not in previous_facts]})
    old_names = {leaf["case"] for leaf in previous["leaves"]}
    inherited = [e for e in new_events if e["kind"] == "CH-INSTANCE" and
                 not any(e["case"] == tag or e["case"].startswith(tag + ".") for tag in old_names)]
    return {"baseline": str(previous_path.resolve()), "baseline_sha256": previous["sha256"],
            "applications_before_the_six_contexts": inherited, "cases": comparison}


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--case", help="print every hypothesis and the goal for this case")
    parser.add_argument("--compare", type=Path, help="compare the named families with a saved frontier JSON")
    args = parser.parse_args()
    data = args.log.read_bytes()
    lines = data.decode("utf-8-sig").splitlines()
    errors = [(i, line) for i, line in enumerate(lines)
              if re.match(r"^.+:\d+:\d+: error(?:\([^)]*\))?:", line)]
    if len(errors) != 1 or not errors[0][1].endswith("error: unsolved goals"):
        sys.exit("No verified open-frontier diagnostic. " + " ".join(line for _, line in errors))
    begin = errors[0][0] + 1
    cases = [i for i in range(begin, len(lines)) if lines[i].startswith("case ")]
    if not cases:
        sys.exit("Lean did not print named case contexts.")
    leaves = []
    for start, end in zip(cases, cases[1:] + [len(lines)]):
        end_goal = next(i for i in range(start + 1, end) if lines[i].startswith("⊢ "))
        target = [lines[end_goal][2:]]
        for line in lines[end_goal + 1:end]:
            if not line.startswith(" "):
                break
            target.append(line)
        name = lines[start][5:]
        if args.case == name:
            print("\n".join(lines[start:end_goal + len(target)]))
            return
        leaves.append({"case": name, "context_line": start + 1, "goal_line": end_goal + 1,
                       "missing_implication_conclusion": "\n".join(target)})
    if args.case:
        sys.exit("Unknown case. Available cases: " + ", ".join(item["case"] for item in leaves))
    rounds = [line for line in lines[:begin] if line.startswith("CH-FAMILY ROUND ")]
    result = {"source_log": str(args.log.resolve()), "sha256": hashlib.sha256(data).hexdigest(),
              "open_leaves": len(leaves), "rounds": rounds, "leaves": leaves}
    result["published_bounds"] = {leaf["case"]: published_bounds(lines, leaf) for leaf in leaves}
    native = {leaf["case"]: native_bank_refinements(lines, leaf) for leaf in leaves}
    if any(native.values()):
        result["native_bank_refinements"] = native
    common_head = {leaf["case"]: common_head_refinements(lines, leaf) for leaf in leaves}
    if any(common_head.values()):
        result["common_head_refinements"] = common_head
    cyclic = {leaf["case"]: cyclic_layer_refinements(lines, leaf) for leaf in leaves}
    if any(cyclic.values()):
        result["cyclic_layer_refinements"] = cyclic

    common_core = {leaf["case"]: common_core_refinements(lines, leaf) for leaf in leaves}
    if any(common_core.values()):
        result["common_core_refinements"] = common_core
    factored = independent_obligations(lines, leaves)
    if factored:
        result["independent_obligations"] = factored
    numeric = {}
    for event in replay_events(lines[:begin]):
        if event["kind"] == "CH-NUMERIC":
            numeric.setdefault(event["case"], []).append(event["detail"])
    if numeric:
        result["numerical_hypotheses"] = numeric
    if args.compare:
        result["comparison"] = compare_frontiers(args.compare, leaves, lines)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

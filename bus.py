from collections import defaultdict
from dataclasses import dataclass
import itertools
from typing import List, Set, Tuple
import neurosym as ns

# c = ParserConfig(prefix_symbols="", dots_are_cons=False)

# corpus = [
#     parse("(+ 2 (+ 2 3))", c)[0],
#     parse("(+ 2 (+ 2 4))", c)[0],
# ]
corpus = [
    ns.parse_s_expression(x)
    for x in [
        "(app Y (lam (lam (app (app (app if (app is_nil $0)) nil) (app (app cons (app (app + (app car $0)) (app car $0))) (app $1 (app cdr $0)))))))",
        "(app Y (lam (lam (app (app (app if (app is_nil $0)) nil) (app (app cons (app (app - (app car $0)) 1))            (app $1 (app cdr $0)))))))",
    ]
    # ns.parse_s_expression("(+ 2 (+ 2 3))"),
    # ns.parse_s_expression("(+ 2 (+ 2 4))"),
]


def get_children(node):
    return node.children


symbols_at = {}
children_of = {}


def add_to_graph(node):
    if isinstance(node, str):
        numeric_node = len(children_of)
        symbols_at[numeric_node] = node
        children_of[numeric_node] = ()
        return numeric_node
    children = tuple(add_to_graph(child) for child in get_children(node))
    numeric_node = len(children_of)
    children_of[numeric_node] = children
    symbols_at[numeric_node] = node.symbol
    return numeric_node


for tree in corpus:
    add_to_graph(tree)

symbol_to_location = defaultdict(set)
for location, symbol in symbols_at.items():
    symbol_to_location[(symbol, len(children_of[location]))].add(location)
symbol_to_location = {k: sorted(v) for k, v in symbol_to_location.items()}

print(symbols_at)
print(children_of)

all_locations = set(symbols_at)


@dataclass
class Match:
    tree: ns.SExpression
    locations: Set[int]
    local_utility: float


# def matches_for_location(location):
#     return [match for match in matches if location in match.locations]


def all_combinations(submatches):
    """
    Combine the submatches in all possible ways. E.g., (+ #1 #2) and #1 can be combined
    as
        (+ #1 #2), #3 -- treating the second #1 independently of the first match
        (+ #1 #2), #1 -- treating the second #1 as the same as the first match's #1
        (+ #1 #2), #2 -- treating the second #1 as the same as the first match's #2

    We ensure that any introduced variable reuse is consistent.
    """
    # TODO actually do this. For now we just do not support variable reuse
    return [submatches]


def update_matches(matches):
    new_matches = matches[:]

    for (symbol, arity), locations in symbol_to_location.items():
        # print(symbol, arity, locations)
        all_submatches = itertools.product(*[matches for _ in range(arity)])
        all_submatches = [
            submatches_new
            for submatches in all_submatches
            for submatches_new in all_combinations(submatches)
        ]
        for submatches in all_submatches:
            # print(submatches)
            locs = {
                loc
                for loc in locations
                if all(
                    child_loc in submatch.locations
                    for submatch, child_loc in zip(submatches, children_of[loc])
                )
            }
            if len(locs) == 0:
                continue
            # print(locs)
            new_matches.append(
                Match(
                    ns.SExpression(symbol, [submatch.tree for submatch in submatches]),
                    locs,
                    1 + sum(submatch.local_utility for submatch in submatches),
                )
            )
    new_matches = sorted(
        new_matches, key=lambda match: match.local_utility, reverse=True
    )
    pareto_optimal_matches = []
    for match in new_matches:
        # TODO variable reuse makes this rule somewhat more complicated
        if any(
            match.locations.issubset(other_match.locations)
            for other_match in pareto_optimal_matches
        ):
            continue
        pareto_optimal_matches.append(match)
    return pareto_optimal_matches


def main():
    matches: List[Match] = [Match("#0", all_locations, 0)]
    for iteration in itertools.count():
        print(
            "ITERATION",
            iteration,
            [
                (ns.render_s_expression(match.tree), match.locations)
                for match in matches
            ],
        )
        matches_new = update_matches(matches)
        if matches_new == matches:
            break
        matches = matches_new
    print([(ns.render_s_expression(match.tree), match.locations) for match in matches])


main()

# for node_idx in symbols_at:
#     print(node_idx, symbols_at[node_idx], children_of[node_idx])


# print(initial_matches)

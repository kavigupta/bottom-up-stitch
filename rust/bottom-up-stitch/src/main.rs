
use lambdas::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
// import BitSet
use bit_set::BitSet;

mod interning;

const APP_UTIL: usize = 1;
const SYM_UTIL: usize = 100;

#[derive(Debug, Clone)]
struct Match {
    tree: usize,
    utility: usize,
    locations: Vec<usize>,
    locations_set: BitSet,
    iteration_added: usize,
}

// constructor
impl Match {
    fn construct(tree: usize, utility: usize, locations_set: BitSet, locations: Vec<usize>, iteration_added: usize, is: &mut interning::InternedSets) -> Self {
        is.intern(&locations, utility);
        Match {
            tree,
            utility,
            locations,
            locations_set,
            iteration_added,
        }
    }
}

#[derive(Debug, Clone)]
struct Statistics {
    pairs_considered_at_all: usize,
    pairs_considered_for_intersection: usize,
    pairs_post_intersection: usize,
    pairs_considered_for_dominance: usize,
}

impl Statistics {
    fn new() -> Self {
        Statistics {
            pairs_considered_at_all: 0,
            pairs_considered_for_intersection: 0,
            pairs_post_intersection: 0,
            pairs_considered_for_dominance: 0,
        }
    }
}

fn update_matches(ms: &Vec<Match>, set: &mut ExprSet, app_locs: &Vec<usize>, iteration: usize, is: &mut interning::InternedSets) -> (Vec<Match>, bool) {
    // ms has the invariant that iteration_added is sorted increasingly
    let mut done = true;
    let mut lefts = HashMap::new();
    let mut rights = HashMap::new();
    let mut right_to_top = HashMap::new();
    for i in app_locs {
        match &set.nodes[*i] {
            Node::App(left, right) => {
                lefts.insert(*left, *i);
                rights.insert(*i, *right);
                right_to_top.insert(*right, *i);
            }
            _ => panic!("Expected an application node"),
        }
    }

    // matches_by_parent_only_right[i] contains matches that contain i's right child
    let mut matches_by_loc: Vec<Vec<usize>> = vec![vec![]; set.nodes.len()];
    for i in 0..ms.len() {
        for loc in &ms[i].locations {
            matches_by_loc[*loc].push(i);
        }
    }

    let mut new_matches: HashMap<Vec<usize>, Match> = HashMap::new();
    for m in ms {
        new_matches.insert(m.locations.clone(), m.clone());
    }
    let mut to_remove = vec![false; ms.len()];
    let mut stats = Statistics::new();
    for left_m in (&*ms) {
        // println!("Analyzinparentsg {:?}", left_m);
        let mut parents = Vec::new();
        for loc in &left_m.locations {
            if let Some(parent) = lefts.get(&loc) {
                parents.push(*parent);
            }
        }
        if parents.len() < 2 {
            continue;
        }
        let rights_for_parents = parents.iter()
            .map(|p| {
                if let Node::App(_, right) = &set.nodes[*p] {
                    *right
                } else {
                    panic!("Expected an application node")
                }
            })
            .collect::<Vec<_>>();
        let max_util_parents = is.get_utility_for_set(&parents);//compute_max_util_parents(&parents, is);
        let recent = left_m.iteration_added == iteration - 1;
        let right_m_candidate_idxs = compute_right_m_candidate_idxs(&rights_for_parents, &matches_by_loc);
        // for right_m in ms.into_iter().rev() {
        for right_m_idx in right_m_candidate_idxs.iter() {
            let right_m = &ms[right_m_idx];
            if !recent && right_m.iteration_added != iteration - 1 {
                continue;
            }
            let Some ((still_valid_parents, utility)) = unify_with_right(
                left_m,
                right_m,
                &parents,
                &rights_for_parents,
                is,
                iteration,
                max_util_parents,
                recent,
                &mut stats,
            ) else {
                continue;
            };
            
            // println!("{:?} {:?}", parents, still_valid_parents);
            let m_new = Match::construct(
                set.add(
                    Node::App(
                        left_m.tree,
                        right_m.tree,
                    )
                ),
                utility,
                BitSet::from_iter(still_valid_parents.iter().cloned()),
                still_valid_parents,
                iteration,
                is,
            );
            done = false;
            new_matches.insert(m_new.locations.clone(), m_new);
            // to_remove.push(false);
        }
    }
    println!("{:?}; done={}", stats, done);
    println!("Interned sets: {:?}", is.len());
    let mut index = 0; 
    // new_matches.retain(|_| { index+=1; !to_remove[index-1] });
    // remove_dominated_matches(&mut new_matches);
    
    return (new_matches.values().cloned().collect(), done);
}

fn compute_right_m_candidate_idxs(rights_for_parents: &Vec<usize>, matches_by_loc: &Vec<Vec<usize>>) -> BitSet {
    let mut right_m_candidate_idxs = BitSet::new();
    for i in rights_for_parents.iter().flat_map(|p| matches_by_loc[*p].iter()) {
        right_m_candidate_idxs.insert(*i);
    }
    return right_m_candidate_idxs
}

fn unify_with_right(
    left_m: &Match,
    right_m: &Match,
    parents: &Vec<usize>,
    rights_for_parents: &Vec<usize>,
    is: &mut interning::InternedSets,
    iteration: usize,
    max_util_parents: usize,
    recent: bool,
    stats: &mut Statistics,
) -> Option<(Vec<usize>, usize)> {
    stats.pairs_considered_at_all += 1;
    let utility = APP_UTIL + left_m.utility + right_m.utility;
    if utility <= max_util_parents {
        return None;
    }

    stats.pairs_considered_for_intersection += 1;

    let mut count = parents.len();
    
    let still_valid_parents = compute_still_valid_parents(parents, rights_for_parents, right_m);

    if still_valid_parents.len() < 2 {
        return None;
    }

    stats.pairs_post_intersection += 1;

    let max_util = is.get_utility_for_set(&still_valid_parents);
    if utility <= max_util {
        return None;
    }
    stats.pairs_considered_for_dominance += 1;
    return Some((still_valid_parents, utility));
}

fn compute_still_valid_parents(
    parents: &Vec<usize>,
    rights_for_parents: &Vec<usize>,
    right_m: &Match,
) -> Vec<usize> {
    let mut still_valid_parents = vec![];
    for i in 0..parents.len() {
        if right_m.locations_set.contains(rights_for_parents[i]) {
            still_valid_parents.push(parents[i]);
        }
    }
    return still_valid_parents;
}

fn bottom_up_stitch(set: &mut ExprSet) -> Vec<Match> {
    let original_num_nodes = set.nodes.len();

    let app_locs = (0..original_num_nodes)
        .filter(|i| matches!(set.nodes[*i], Node::App(_, _)))
        .collect::<Vec<_>>();

    let variable = set.parse_extend("?").unwrap();

    let mut is = interning::InternedSets::new();

    let mut matches: Vec<Match> = vec![Match::construct(
        variable,
        0,
        BitSet::from_iter(0..original_num_nodes),
        (0..original_num_nodes).collect(),
        0,
        &mut is,
    )];

    let mut sym_to_locations = HashMap::new();

    for i in 0..original_num_nodes {
        match &set.nodes[i] {
            Node::Prim(sym) => {
                if ! sym_to_locations.contains_key(sym) {
                    sym_to_locations.insert(sym.clone(), BitSet::new());
                }
                sym_to_locations.get_mut(sym).unwrap().insert(i);
            }
            _ => {}
        }
    }
    for vs in sym_to_locations.values() {
        if vs.len() < 2 {
            continue;
        }
        matches.push(Match::construct(
            vs.iter().next().unwrap(),
            SYM_UTIL,
            vs.clone(),
            vs.into_iter().collect(),
            0,
            &mut is,
        ));
    }

    for i in 1.. {
        let done;
        println!("Iteration {}, {} matches", i, matches.len());
        (matches, done) = update_matches(&mut matches, set, &app_locs, i, &mut is);
        if done {
            break;
        }
    }
    return matches;
}

fn main() {
    let set = &mut ExprSet::empty(Order::ChildFirst, false, false);
    // let corpus = json.load("/home/kavi/mit/compression_benchmark/processed/without-apps-no-lam/dials.json");
    let path = "/home/kavi/mit/compression_benchmark/processed/without-apps-no-lam/wheels.json";

    let corpus = std::fs::read_to_string(path).unwrap();
    let corpus: Vec<String> = serde_json::from_str(&corpus).unwrap();

    for s in &corpus {
        set.parse_extend(s).unwrap();
    }

    let matches = bottom_up_stitch(set);

    // for m in &matches {
    //     println!("{:?}", set.get(m.tree).to_string());
    //     // print_match(m, set);
    // }
    // save to file
    let mut file = File::create("matches.txt").unwrap();
    for m in &matches {
        writeln!(file, "{:?}", set.get(m.tree).to_string()).unwrap();
        // print_match(m, set);
    }
}

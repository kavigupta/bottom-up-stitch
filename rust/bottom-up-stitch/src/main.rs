
use lambdas::*;
use std::collections::HashMap;
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
    for i in app_locs {
        match &set.nodes[*i] {
            Node::App(left, right) => {
                lefts.insert(*left, *i);
                rights.insert(*i, *right);
            }
            _ => panic!("Expected an application node"),
        }
    }


    let mut new_matches = ms.clone();
    let mut to_remove = vec![false; ms.len()];
    let mut stats = Statistics::new();
    for left_m in &*ms {
        // println!("Analyzinparentsg {:?}", left_m);
        let mut parents = Vec::new();
        for loc in &left_m.locations_set {
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
        for right_m in ms.into_iter().rev() {
            if !recent && right_m.iteration_added != iteration - 1 {
                break;
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
            let mr = dominates_or_is_dominated(&m_new, &new_matches, &mut to_remove);
            // println!("Dominance result: {:?}", mr);
            match mr {
                DominanceResult::Dominated() => continue,
                DominanceResult::Dominates() => {
                    done = false;
                }
                DominanceResult::NeitherDominates() => {}
            }
            new_matches.push(m_new);
            to_remove.push(false);
        }
    }
    println!("{:?}; done={}", stats, done);
    println!("Interned sets: {:?}", is.len());
    let mut index = 0; 
    new_matches.retain(|_| { index+=1; !to_remove[index-1] });
    // remove_dominated_matches(&mut new_matches);
    return (new_matches, done);
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

#[derive(Debug, Clone)]
enum DominanceResult {
    Dominated(),
    Dominates(),
    NeitherDominates(),
}

fn dominates_or_is_dominated(a: &Match, existing: &Vec<Match>, to_remove: &mut Vec<bool>) -> DominanceResult {
    let mut dominates = false;
    for i in (0..existing.len()).rev() {
    // for i in existing.len()-1..=0 {
        if to_remove[i] {
            continue;
        }
        if a_dominates_b(&existing[i], &a) {
            return DominanceResult::Dominated();
        }
        if a_dominates_b(&a, &existing[i]) {
            to_remove[i] = true;
            dominates = true;
        }
    }
    if dominates {
        return DominanceResult::Dominates();
    }
    return DominanceResult::NeitherDominates();
}

fn a_dominates_b(a: &Match, b: &Match) -> bool {
    if a.utility < b.utility {
        return false;
    }
    if a.locations.len() < b.locations.len() {
        return false;
    }
    // return b.locations.iter().all(|i| a.locations_set.contains(*i))
    for i in &b.locations {
        if !a.locations_set.contains(*i) {
            return false;
        }
    }
    return true;
    // return b.locations_set.is_subset(&a.locations_set);
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
    let corpus = [
        // "(+ 1 (+ 2 3) (+ 3 4))",
        // "(+ 1 (+ 2 7) (+ 3 4))",
        // "(+ 1 a (+ 3 4))",
        "(C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1)))",
        "(C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0)))",
        "(C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5)))",
        "(T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 1 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 0 0))",
        "(C (C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) 4.5) (M 1 0 0 0)) (T (r_s 1 2.25) (M 1 0 7.75 0))) (T (r_s 1 2.25) (M 1 0 (- 0 (* 0.5 (+ (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* 2 0.5)))) 0))) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0)))",
        "(C (C (C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) 4.5) (M 1 0 0 0)) (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 1 (* 4 0.5))) 2.25) (M 1 0 0 (+ (* 0.5 0) (* 0.5 (+ (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 1)) (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 0)))))))) (T (r_s 1 2.25) (M 1 0 7.75 0))) (T (r_s 1 2.25) (M 1 0 (- 0 (* 0.5 (+ (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* 2 0.5)))) 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0)))",
        "(C (C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (r_s 1 6.25) (M 1 0 7.75 0))) (T (r_s 1 6.25) (M 1 0 (- 0 (* 0.5 (+ (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* 2 0.5)))) 0))) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0)))",
        "(C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T c (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0)))",
        "(C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0))) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 8.25)))",
        "(C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0))) (T (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (M 1 0 0 8.25)))",
        "(C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (repeat (repeat (C (C (T c (M 2 0 0 0)) (T r (M 2.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 2 (/ pi 4) 0 0)) (M 1 0 (* 2 (* 0.5 (cos (/ pi 4)))) (* 2 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0))) (T (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (M 1 0 0 8.25)))",
        "(C (C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* (+ (* 1 (+ 10 0.5)) (* 4 0.5)) (pow 0.5 0))) (M 1 0 0 0)) (T (repeat (repeat (C (C (T c (M 2 0 0 0)) (T r (M 2.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 2 (/ pi 4) 0 0)) (M 1 0 (* 2 (* 0.5 (cos (/ pi 4)))) (* 2 (* 0.5 (sin (/ pi 4))))))) 5 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) 0))) (T (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 (* (max 0 (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5)))) 0.25) 8.25))) (T (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 (- 0 (* (max 0 (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5)))) 0.25)) 8.25)))",
        "(C (C (C (T (r_s (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) 7) (M 1 0 0 0)) (T (r_s 1 3.5) (M 1 0 7.75 0))) (T (r_s 1 3.5) (M 1 0 (- 0 (* 0.5 (+ (- (+ (* 5 (+ 2 0.5)) (* 4 0.5)) (* 0 (* 4 0.5))) (* 2 0.5)))) 0))) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 5 (M 1 0 2.5 0)) 2 (M 1 0 0 2.5)) (M 1 0 (- 0 (* 0.5 (* (- 5 1) (+ 2 0.5)))) -1.25)))",
        "(C (T (r_s 9.5 4.5) (M 1 0 0 0)) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 9.5 4.5) (M 1 0 0 0)) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 9.5 4.5) (M 1 0 0 0)) (T (C (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 -1))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 9.5 4.5) (M 1 0 0 0)) (T (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 9.5 4.5) (M 1 0 0 0)) (T (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 0 0 0 0)) (M 1 0 0 -1))) (M 1 0 0 4.25)))",
        "(C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (C (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 0 0 0 0)) (M 1 0 0 -1))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 4.25)))",
        "(C (C (C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (r_s 1 2.25) (M 1 0 2.75 0))) (T (r_s 1 2.25) (M 1 0 -2.75 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 1 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 0 0)))",
        "(C (C (C (C (C (C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (r_s 2.5 2.25) (M 1 0 0 (+ (* 0.5 0) (* 0.5 (+ (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 1)) (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 0)))))))) (T (r_s 1 2.25) (M 1 0 2.75 0))) (T (r_s 1 2.25) (M 1 0 -2.75 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T c (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 1 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 0 0))) (T (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (M 1 0 0 6.5))) (T (T (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (M 1 (- 0 (/ pi 2)) 0 0)) (M 1 0 5.25 0)))",
        "(C (C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (r_s 2.5 2.25) (M 1 0 0 (+ (* 0.5 0) (* 0.5 (+ (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 1)) (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 0)))))))) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 1 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 0 0)))",
        "(C (C (C (C (T (r_s 4.5 4.5) (M 1 0 0 0)) (T (r_s 2.5 2.25) (M 1 0 0 (+ (* 0.5 0) (* 0.5 (+ (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 1)) (* (+ (* 1 (+ 2 0.5)) (* 4 0.5)) (pow 0.5 0)))))))) (T (repeat (repeat (C (repeat c 1 (M 2.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 (/ pi 4) 0 0)) (M 1 0 (* 2 (* 0.5 (cos (/ pi 4)))) (* 2 (* 0.5 (sin (/ pi 4))))))) 1 (M 1 0 2.5 0)) 1 (M 1 0 0 2.5)) (M 1 0 0 0))) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 0 0 0 0)) (M 1 0 0 -1))) (M 1 0 0 6.5))) (T (T (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (M 1 (- 0 (/ pi 2)) 0 0)) (M 1 0 4.25 0)))",
        "(C (C (C (C (T (r_s 4.5 7) (M 1 0 0 0)) (T (r_s 1 3.5) (M 1 0 2.75 0))) (T (r_s 1 3.5) (M 1 0 -2.75 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 1 (M 1 0 2.5 0)) 2 (M 1 0 0 2.5)) (M 1 0 0 -1.25))) (T (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T r (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T r (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 5.5)))",
        "(C (C (C (C (T (r_s 4.5 7) (M 1 0 0 0)) (T (r_s 1 3.5) (M 1 0 2.75 0))) (T (r_s 1 3.5) (M 1 0 -2.75 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 1 (M 1 0 2.5 0)) 2 (M 1 0 0 2.5)) (M 1 0 0 -1.25))) (T (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (M 1 0 0 5.5)))",
        "(C (C (C (C (C (T (r_s 4.5 7) (M 1 0 0 0)) (T (r_s 1 3.5) (M 1 0 2.75 0))) (T (r_s 1 3.5) (M 1 0 -2.75 0))) (T (repeat (repeat (C (C (T c (M 1 0 0 0)) (T r (M 1.5 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 4) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 4)))) (* 1 (* 0.5 (sin (/ pi 4))))))) 1 (M 1 0 2.5 0)) 2 (M 1 0 0 2.5)) (M 1 0 0 -1.25))) (T (C (C (C (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 1 0 0 0)) (M 1 0 0 0))) (T (T (T l (M 1 0 -0.5 0)) (M 0 0 0 0)) (M 1 0 0 -1))) (T (T c (M 1 0 -1.5 0.5)) (M 1 0 0 0.5))) (T (T c (M 1 0 1.5 0.5)) (M 1 0 0 0.5))) (M 1 0 0 5.5))) (T (T (C (C (T (T (T l (M 3 (/ pi 2) 0 -2)) (M 1 0 0 0)) (M 1 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 1))) (T (T (T l (M 1 0 -0.5 0)) (M 2 0 0 0)) (M 1 0 0 0))) (M 1 (- 0 (/ pi 2)) 0 0)) (M 1 0 5.25 0)))",
        "(C (T (r_s 4.5 7) (M 1 0 0 0)) (T (repeat (repeat (C (repeat c 1 (M 1.5 0 0 0)) (T (T (T l (M 1 0 -0.5 0)) (M 1 (/ pi 2) 0 0)) (M 1 0 (* 1 (* 0.5 (cos (/ pi 2)))) 0.5))) 1 (M 1 0 2.5 0)) 2 (M 1 0 0 2.5)) (M 1 0 0 -1.25)))"
    ];

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

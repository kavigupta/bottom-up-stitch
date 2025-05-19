
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

fn print_match(m: &Match, set: &ExprSet) {
    println!("******************");
    println!("Tree: {:?}", set.get(m.tree).to_string());
    println!("Utility: {:?}", m.utility);
    println!("Locations: {:?}", m.locations_set);
    println!("Locations: {:?}", m.locations_set.iter().map(|i| set.get(i).to_string()).collect::<Vec<_>>());
}

fn update_matches(ms: &mut Vec<Match>, set: &mut ExprSet, app_locs: &Vec<usize>, iteration: usize, is: &mut interning::InternedSets) -> (Vec<Match>, bool) {
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
    // println!("Lefts: {:?}", lefts);
    // println!("Rights: {:?}", lefts);
    // // right_matches[parent] = all the matches that match at the right of the parent, as indices into ms
    // let mut right_matches: HashMap<usize, Vec<usize>> = HashMap::new();
    // for (i, m) in ms.iter().enumerate() {
    //     for loc in &m.locations {
    //         if let Some(right) = rights.get(loc) {
    //             if !right_matches.contains_key(right) {
    //                 right_matches.insert(*right, Vec::new());
    //             }
    //             right_matches.get_mut(right).unwrap().push(i);
    //         }
    //     }
    // }
    // check_pareto(ms);
    let mut new_matches = ms.clone();
    let mut to_remove = vec![false; ms.len()];
    let mut considered = 0;
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
        let max_util_parents = compute_max_util_parents(&parents, is);
        let recent = left_m.iteration_added == iteration - 1;
        for right_m in &*ms {
            if !recent && right_m.iteration_added != iteration - 1 {
                continue;
            }
            let utility = APP_UTIL + left_m.utility + right_m.utility;
            if utility <= max_util_parents {
                continue;
            }
            let mut still_valid_parents = vec![];
            for p in &parents {
                let Node::App(_, right) = &set.nodes[*p] else {panic!("Expected an application node")};
                if right_m.locations_set.contains(*right) {
                    still_valid_parents.push(*p);
                }
            }
            if still_valid_parents.len() < 2 {
                continue;
            }

            let max_util = compute_max_util_parents(&still_valid_parents, is);
            if utility <= max_util {
                continue;
            }
            
            // println!("{:?} {:?}", parents, still_valid_parents);
            considered += 1;
            
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
    println!("Considered {} new matches; done={}", considered, done);
    println!("Interned sets: {:?}", is.len());
    let mut index = 0; 
    new_matches.retain(|_| { index+=1; !to_remove[index-1] });
    // remove_dominated_matches(&mut new_matches);
    return (new_matches, done);
}

// fn compute_max_util_parents(parents: &Vec<usize>, ms: &Vec<Match>) -> usize {
//     let mut max_util = 0;
//     for m in ms {
//         let mut subset = true;
//         for p in parents {
//             if !m.locations_set.contains(*p) {
//                 subset = false;
//                 break;
//             }
//         }
//         if subset {
//             if m.utility > max_util {
//                 max_util = m.utility;
//             }
//         }
//     }
//     return max_util;
// }

fn compute_max_util_parents(parents: &Vec<usize>, is: &mut interning::InternedSets) -> usize {
    let index = is.intern(parents, 0);
    return is.get_utility(index)
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

// fn check_pareto(matches: &Vec<Match>) {
//     for i in 0..matches.len() {
//         for j in 0..matches.len() {
//             if i == j {
//                 continue;
//             }
//             if a_dominates_b(&matches[i], &matches[j]) {
//                 panic!("Dominated match ({} {})/{}: {:?}; {:?}", i, j, matches.len(), matches[i], matches[j]);
//             }
//         }
//     }
// }

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

fn remove_dominated_matches(matches: &mut Vec<Match>) {
    println!("Removing dominated matches; {} matches before", matches.len());
    let mut dominated = vec![false; matches.len()];
    for i in 0..matches.len() {
        if dominated[i] {
            continue;
        }
        for j in 0..matches.len() {
            if i == j {
                continue;
            }
            if dominated[j] {
                continue;
            }
            if a_dominates_b(&matches[i], &matches[j]) {
                dominated[j] = true;
            }
        }
    }
    let mut index = 0;
    matches.retain(|_| { index+=1; !dominated[index-1] });
    println!("{} matches after", matches.len());
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

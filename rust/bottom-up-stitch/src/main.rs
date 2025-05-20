
use lambdas::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
// import BitSet
use bit_set::BitSet;

mod interning;

const ARITY_LIMIT: usize = usize::MAX;

const APP_UTIL: usize = 1;
const SYM_UTIL: usize = 100;

#[derive(Debug, Clone)]
struct Match {
    tree: usize,
    utility: usize,
    num_holes: usize,
    intern_idx: usize,
    intern_idx_left: i32,
    intern_idx_right: i32,
    iteration_added: usize,
}

// constructor
impl Match {
    fn construct(tree: usize, utility: usize, num_holes: usize, locations: Vec<usize>, iteration_added: usize, is: &mut interning::InternedSets) -> Self {
        let intern_idx = is.intern(&locations, utility);
        Match {
            tree,
            utility,
            num_holes,
            intern_idx,
            intern_idx_left: is.parent_set_left[intern_idx],
            intern_idx_right: is.parent_set_right[intern_idx],
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

fn update_matches(
    ms: &Vec<Match>,
    set: &mut ExprSet,
    iteration: usize,
    is: &mut interning::InternedSets,
    app_locs: &Vec<i32>,
    num_app_locs: usize,
) -> (Vec<Match>, bool) {
    // ms has the invariant that iteration_added is sorted increasingly
    let mut done = true;

    let matches_with_right: Vec<Match> = ms.iter().filter(|m| m.intern_idx_right != -1).cloned().collect();
    let matches_with_left: Vec<Match> = ms.iter().filter(|m| m.intern_idx_left != -1).cloned().collect();

    let matrix = compute_matrix(&matches_with_left, &matches_with_right, app_locs, num_app_locs, is);

    println!("Matrix: {:?}", matrix.len() * matrix[0].len());



    let mut new_matches: HashMap<usize, Match> = HashMap::new();
    for m in ms {
        new_matches.insert(m.intern_idx, m.clone());
    }
    let mut stats = Statistics::new();
    for i in 0..matches_with_left.len() {
        let left_m = &matches_with_left[i];
        // println!("Analyzinparentsg {:?}", left_m);
        let parents_idx = left_m.intern_idx_left as usize;
        let parents = is.unintern(parents_idx);
        let max_util_parents = is.get_utility_for_set(&parents); //compute_max_util_parents(&parents, is);
        let recent = left_m.iteration_added == iteration - 1;
        // for right_m in ms.into_iter().rev() {
        for right_m_idx in (0..matches_with_right.len()).rev() {
            if matrix[i][right_m_idx] < 2 {
                continue;
            }
            let right_m = &matches_with_right[right_m_idx];
            let num_holes = left_m.num_holes + right_m.num_holes;
            if num_holes > ARITY_LIMIT {
                continue;
            }
            if !recent && right_m.iteration_added != iteration - 1 {
                continue;
            }
            let Some ((still_valid_parents_idx, utility)) = unify_with_right(
                left_m,
                right_m,
                parents_idx,
                matches_with_right[right_m_idx].intern_idx_right as usize,
                is,
                max_util_parents,
                &mut stats,
            ) else {
                continue;
            };

            let still_valid_parents = is.unintern(still_valid_parents_idx);
            
            // println!("{:?} {:?}", parents, still_valid_parents);
            let m_new = Match::construct(
                set.add(
                    Node::App(
                        left_m.tree,
                        right_m.tree,
                    )
                ),
                utility,
                num_holes,
                still_valid_parents,
                iteration,
                is,
            );
            done = false;
            new_matches.insert(m_new.intern_idx, m_new);
            // to_remove.push(false);
        }
    }
    println!("{:?}; done={}", stats, done);
    println!("Interned sets: {:?}", is.len());
    
    return (new_matches.values().cloned().collect(), done);
}

fn compute_matrix(
    matches_with_left: &Vec<Match>,
    matches_with_right: &Vec<Match>,
    app_locs: &Vec<i32>,
    num_app_locs: usize,
    is: &mut interning::InternedSets
) -> Vec<Vec<u8>> {
    let mut left_matches_by_loc: Vec<Vec<usize>> = vec![vec![]; num_app_locs];
    for i in 0..matches_with_left.len() {
        for loc in is.unintern(matches_with_left[i].intern_idx_left as usize) {
            if app_locs[loc] == -1 {
                continue;
            }
            left_matches_by_loc[app_locs[loc] as usize].push(i);
        }
    }
    
    let mut right_matches_by_loc: Vec<Vec<usize>> = vec![vec![]; num_app_locs];
    for i in 0..matches_with_right.len() {
        for loc in is.unintern(matches_with_right[i].intern_idx_right as usize) {
            if app_locs[loc] == -1 {
                continue;
            }
            right_matches_by_loc[app_locs[loc] as usize].push(i);
        }
    }

    let mut matrix: Vec<Vec<u8>> = vec![vec![0; matches_with_right.len()]; matches_with_left.len()];
    for node_idx in 0..num_app_locs {
        for ml in left_matches_by_loc[node_idx].iter() {
            for mr in right_matches_by_loc[node_idx].iter() {
                matrix[*ml][*mr] += 1;
            }
        }
    }
    return matrix
}

fn unify_with_right(
    left_m: &Match,
    right_m: &Match,
    parents_left_idx: usize,
    parents_right_idx: usize,
    is: &mut interning::InternedSets,
    max_util_parents: usize,
    stats: &mut Statistics,
) -> Option<(usize, usize)> {
    stats.pairs_considered_at_all += 1;
    let utility = APP_UTIL + left_m.utility + right_m.utility;
    if utility <= max_util_parents {
        return None;
    }

    stats.pairs_considered_for_intersection += 1;

    // let still_valid_parents = compute_still_valid_parents(parents, rights_for_parents, right_m);
    let still_valid_parents_idx = is.intersect(parents_left_idx, parents_right_idx);

    if still_valid_parents_idx < 0 {
        return None;
    }

    stats.pairs_post_intersection += 1;

    let max_util = is.get_utility(still_valid_parents_idx as usize);
    if utility <= max_util {
        return None;
    }
    stats.pairs_considered_for_dominance += 1;
    return Some((still_valid_parents_idx as usize, utility));
}

fn location_to_app_loc_idx(
    set: &ExprSet,
    mask: Vec<bool>,
    original_num_nodes: usize,
) -> (Vec<i32>, usize) {
    let app_locs = (0..original_num_nodes)
        .filter(|i| mask[*i] && matches!(set.nodes[*i], Node::App(_, _)))
        .collect::<Vec<_>>();
    let mut backmap = vec![-1; set.nodes.len()];
    for i in 0..app_locs.len() {
        backmap[app_locs[i]] = i as i32;
    }
    return (backmap, app_locs.len());
}

fn compute_depth_by_node(set: &ExprSet) -> Vec<usize> {
    let original_num_nodes = set.nodes.len();
    let mut depth_by_node = vec![-1; original_num_nodes];
    for i in 0..original_num_nodes {
        match &set.nodes[i] {
            Node::App(left, right) => {
                assert!(depth_by_node[*left] != -1);
                assert!(depth_by_node[*right] != -1);
                depth_by_node[i] = depth_by_node[*left].max(depth_by_node[*right]) + 1;
            }
            Node::Prim(_) => {
                depth_by_node[i] = 0;
            }
            _ => {
                panic!("Unknown node type");
            }
        }
    }
    return depth_by_node.iter().map(|x| *x as usize).collect();
}

fn bottom_up_stitch(set: &mut ExprSet) -> Vec<Match> {
    let original_num_nodes = set.nodes.len();

    let depth_by_node = compute_depth_by_node(set);

    let variable = set.parse_extend("?").unwrap();

    let (parents_left, parents_right) = get_parents_left_right(set);

    let mut is = interning::InternedSets::new(parents_left, parents_right);

    let mut matches: Vec<Match> = vec![Match::construct(
        variable,
        0,
        1,
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
            0,
            vs.into_iter().collect(),
            0,
            &mut is,
        ));
    }

    for i in 1usize.. {
        let done;
        println!("Iteration {}, {} matches", i, matches.len());
        let (app_locs, num_app_locs) = location_to_app_loc_idx(set, depth_by_node.iter().map(|x| *x >= i).collect(), original_num_nodes);
        println!("App locs: {:?}", num_app_locs);
        (matches, done) = update_matches(&mut matches, set, i, &mut is, &app_locs, num_app_locs);
        if done {
            break;
        }
    }
    return matches;
}

fn get_parents_left_right(set: &ExprSet) -> (Vec<i32>, Vec<i32>) {
    let mut parents_left = vec![-1; set.nodes.len()];
    let mut parents_right = vec![-1; set.nodes.len()];
    for i in 0..set.nodes.len() {
        match &set.nodes[i] {
            Node::App(left, right) => {
                parents_left[*left] = i as i32;
                parents_right[*right] = i as i32;
            }
            _ => {}
        }
    }
    return (parents_left, parents_right);
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

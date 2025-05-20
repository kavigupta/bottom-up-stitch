
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct InternedSets {
    parents_left: Vec<i32>,
    parents_right: Vec<i32>,
    sets: Vec<Vec<usize>>,
    parent_set_left: Vec<i32>,
    parent_set_right: Vec<i32>,
    set_backmap: HashMap<Vec<usize>, usize>,
    best_utility_seen: Vec<usize>,
    intersection_cache: HashMap<(usize, usize), i32>,
}

// fn new_interned_sets() -> InternedSets {
//     InternedSets {
//         sets: Vec::new(),
//         set_backmap: HashMap::new(),
//         best_utility_seen: Vec::new(),
//     }
// }

impl InternedSets {
    pub fn new(parents_left: Vec<i32>, parents_right: Vec<i32>) -> InternedSets {
        InternedSets {
            parents_left: parents_left,
            parents_right: parents_right,
            sets: Vec::new(),
            parent_set_left: Vec::new(),
            parent_set_right: Vec::new(),
            set_backmap: HashMap::new(),
            best_utility_seen: Vec::new(),
            intersection_cache: HashMap::new(),
        }
    }

    pub fn get_utility(&self, value: usize) -> usize {
        return self.best_utility_seen[value];
    }

    pub fn get_utility_for_set(&self, value: &Vec<usize>) -> usize {
        if let Some(&index) = self.set_backmap.get(value) {
            return self.best_utility_seen[index];
        }
        return 0
    }

    pub fn get_parents_left(&self, value: usize) -> Option<usize> {
        let u = self.parent_set_left[value];
        if u >= 0 {
            return Some(u as usize);
        }
        return None;
    }

    pub fn get_parents_right(&self, value: usize) -> Option<usize> {
        let u = self.parent_set_right[value];
        if u >= 0 {
            return Some(u as usize);
        }
        return None;
    }

    pub fn intersect(
        &mut self,
        left_idx: usize,
        right_idx: usize,
    ) -> i32 {
        if let Some(intersection) = self.intersection_cache.get(&(left_idx, right_idx)) {
            return *intersection;
        }
        let parents_left = self.unintern(left_idx);
        let parents_right = self.unintern(right_idx);
        let result = intersect(parents_left, parents_right);
        let result_idx = if result.len() < 2 {
            -1
        } else {
            self.intern(&result, 0) as i32
        };
        self.intersection_cache.insert((left_idx, right_idx), result_idx);
        if (self.intersection_cache.len() % 1000) == 0 {
            println!("Intersection cache size: {}", self.intersection_cache.len());
        }
        return result_idx
    }

    pub fn unintern(&self, value: usize) -> Vec<usize> {
        let res = self.sets[value].clone();
        // check that this is sorted
        // assert!(res.is_sorted());
        return res
    }

    pub fn intern(&mut self, set: &Vec<usize>, utility: usize) -> usize {
        if let Some(&index) = self.set_backmap.get(set) {
            if utility > self.best_utility_seen[index] {
                self.best_utility_seen[index] = utility;
            }
            return index;
        }
        let parent_set_left = set.iter()
            .map(|&x| self.parents_left[x])
            .filter(|&x| x != -1)
            .map(|x| x as usize)
            .collect::<Vec<usize>>();
        let parent_set_left_idx: i32 = if parent_set_left.len() < 2 { -1 } else { self.intern(&parent_set_left, utility) as i32 };
        let parent_set_right = set.iter()
            .map(|&x| self.parents_right[x])
            .filter(|&x| x != -1)
            .map(|x| x as usize)
            .collect::<Vec<usize>>();
        let parent_set_right_idx: i32 = if parent_set_right.len() < 2 { -1 } else { self.intern(&parent_set_right, utility) as i32 };
        self.parent_set_left.push(parent_set_left_idx);
        self.parent_set_right.push(parent_set_right_idx);
        let mut sorted = set.clone();
        sorted.sort();
        self.sets.push(sorted.clone());
        let index = self.sets.len() - 1;
        self.set_backmap.insert(sorted, index);
        self.best_utility_seen.push(utility);
        return index;
    }

    pub fn len(&self) -> usize {
        self.sets.len()
    }

}


fn intersect(
    parents_left: Vec<usize>,
    parents_right: Vec<usize>,
) -> Vec<usize> {
    if (parents_left.len() > parents_right.len()) {
        return intersect(parents_right, parents_left);
    }
    let mut still_valid_parents = vec![];
    let mut a_ptr = 0;
    let mut b_ptr = 0;
    while a_ptr < parents_left.len() && b_ptr < parents_right.len() {
        if parents_left[a_ptr] == parents_right[b_ptr] {
            still_valid_parents.push(parents_left[a_ptr]);
            a_ptr += 1;
            b_ptr += 1;
        } else if parents_left[a_ptr] < parents_right[b_ptr] {
            a_ptr += 1;
        } else {
            b_ptr += 1;
        }
    }
    // for i in 0..parents_left.len() {
    //     // if parents_right.contains(&parents_left[i]) {
    //     // use binary search
    //     if parents_right.binary_search(&parents_left[i]).is_ok() {
    //         still_valid_parents.push(parents_left[i]);
    //     }
    // }
    return still_valid_parents;
}